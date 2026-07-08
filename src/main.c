/*
 * XDS BLE -> ANT+ BPWR bridge
 */

#include <stdio.h>
#include <limits.h>
#include <string.h>

#include <zephyr/bluetooth/bluetooth.h>
#include <zephyr/bluetooth/assigned_numbers.h>
#include <zephyr/bluetooth/conn.h>
#include <zephyr/bluetooth/gatt.h>
#include <zephyr/bluetooth/hci.h>
#include <zephyr/bluetooth/uuid.h>
#include <zephyr/device.h>
#include <zephyr/drivers/gpio.h>
#include <zephyr/drivers/uart.h>
#include <zephyr/kernel.h>
#include <zephyr/logging/log.h>
#include <zephyr/sys/byteorder.h>
#include <zephyr/sys/util.h>

#include <ant_key_manager.h>
#include <ant_parameters.h>
#include <ant_profiles/bpwr/ant_bpwr.h>

LOG_MODULE_REGISTER(xds_ant_bridge, LOG_LEVEL_WRN);

/** @brief BLE/ANT 数据超时（ms），约 2 个 XDS 包周期，停脚后尽快清零。 */
#define DATA_TIMEOUT_MS 2200
/** @brief ANT profile 刷新周期（ms），与 BPWR 广播 ~4Hz 对齐。 */
#define ANT_UPDATE_MS 250
/** @brief 主循环周期（ms）。 */
#define MAIN_LOOP_MS 25
/** @brief 慢闪半周期（ms），用于状态指示灯闪烁节奏。 */
#define SLOW_BLINK_HALF_MS 250
/** @brief 串口接收数据日志输出周期（ms）。 */
#define RX_LOG_INTERVAL_MS 1000
/** @brief APP 转发日志输出周期（ms）。 */
#define APP_LOG_INTERVAL_MS 2000
/** @brief BLE APP 通知发送周期（ms，XDS 原生约 1Hz）。 */
#define APP_NOTIFY_INTERVAL_MS 1000
/** @brief 中央侧（连接 XDS）监督超时（ms），放宽以避免停脚时误断链。 */
#define XDS_CONN_TIMEOUT_MS 12000
/* Faster advertising helps watches find the bridge in crowded BLE environments. */
#define APP_ADV_INTERVAL_MIN 0x0030U /* 30 ms, units of 0.625 ms */
#define APP_ADV_INTERVAL_MAX 0x0060U /* 60 ms, units of 0.625 ms */
#define APP_ADV_WATCHDOG_MS 3000
/* Keep the watch connection tighter than the old 100-150 ms / latency 4 setting. */
#define APP_CONN_INTERVAL_MIN 36 /* 45 ms, units of 1.25 ms */
#define APP_CONN_INTERVAL_MAX 48 /* 60 ms, units of 1.25 ms */
#define APP_CONN_LATENCY 0
#define APP_CONN_TIMEOUT_MS 8000
/* Scan in bursts so central scanning does not starve advertising/ANT in busy areas. */
#define XDS_SCAN_ON_MS 5000
#define XDS_SCAN_OFF_MS 1000

/** @brief XDS 功率计服务 UUID（16-bit）。 */
#define XDS_SERVICE_UUID_16 0x1828
/** @brief XDS 功率计测量特征 UUID（16-bit）。 */
#define XDS_MEAS_UUID_16 0x2A63

/** @brief 板载 LED0（P0.12）。 */
#define LED0_NODE DT_ALIAS(led0)
/** @brief 板载 LED1（P1.09）。 */
#define LED1_NODE DT_ALIAS(led1)
/** @brief 板载 LED2（P0.04），用于 BLE 外设连接状态指示。 */
#define LED2_NODE DT_ALIAS(led2)

/** @brief 串口命令缓冲区长度。 */
#define CMD_BUF_LEN 64
/** @brief 无换行命令的自动执行空闲时间（ms）。 */
#define CMD_IDLE_EXEC_MS 1200

static const struct gpio_dt_spec led0 = GPIO_DT_SPEC_GET(LED0_NODE, gpios);
static const struct gpio_dt_spec led1 = GPIO_DT_SPEC_GET(LED1_NODE, gpios);
static const struct gpio_dt_spec led2 = GPIO_DT_SPEC_GET(LED2_NODE, gpios);

/** @brief 控制台串口设备。 */
static const struct device *uart_console;
/** @brief 串口命令缓存。 */
static char cmd_buf[CMD_BUF_LEN];
/** @brief 当前已接收命令长度。 */
static size_t cmd_len;
/** @brief 串口最后一次接收字符时间戳（ms）。 */
static uint32_t cmd_last_rx_ms;

/** @brief 串口调试打印总开关，默认关闭以减轻 UART 占用与回调延迟。 */
static bool serial_log_enabled;

#define SLOG(...)                                                                                  \
	do {                                                                                       \
		if (serial_log_enabled) {                                                              \
			printf(__VA_ARGS__);                                                           \
		}                                                                                      \
	} while (0)

/** @brief 上次 ANT profile 刷新时间戳（ms）。 */
static uint32_t last_ant_update_ms;
static uint32_t last_adv_watchdog_ms;
static uint32_t last_xds_scan_state_ms;

/** @brief 当前与 XDS 连接对象（中央角色）。 */
static struct bt_conn *sensor_conn;
/** @brief GATT 发现参数。 */
static struct bt_gatt_discover_params discover_params;
/** @brief GATT 订阅参数。 */
static struct bt_gatt_subscribe_params subscribe_params;
/** @brief 动态发现用 16-bit UUID 容器。 */
static struct bt_uuid_16 discover_uuid;
/** @brief 目标服务起始句柄。 */
static uint16_t service_start_handle;
/** @brief 目标服务结束句柄。 */
static uint16_t service_end_handle;

/** @brief BLE 数据共享锁（通知回调与主循环共享）。 */
static struct k_mutex data_lock;
/** @brief 最新总功率（W）。 */
static uint16_t latest_power_w;
/** @brief 最新左腿功率（W）。 */
static int16_t latest_left_power_w;
/** @brief 最新右腿功率（W）。 */
static int16_t latest_right_power_w;
/** @brief 最新踏频（rpm）。 */
static uint16_t latest_cadence;
/** @brief 最新错误码。 */
static uint8_t latest_error_code;
/** @brief 最后收到 BLE 数据时间戳（ms）。 */
static uint32_t last_ble_data_ms;
/** @brief 上一包 BLE 到达时间戳（ms）。 */
static uint32_t last_rx_packet_ms;
/** @brief BLE 包间隔平滑均值（ms）。 */
static uint32_t rx_avg_interval_ms;
/** @brief 功率事件计数（ANT page16 event count）。 */
static uint8_t pwr_event_count;
/** @brief 累计功率（ANT page16 accumulated power）。 */
static uint16_t accumulated_power;
/** @brief CPS 通知是否已被 APP 订阅。 */
static bool cps_notify_enabled;
/** @brief CSCS 通知是否已被 APP 订阅。 */
static bool csc_notify_enabled;

/** @brief 是否扫描到目标 XDS 设备。 */
static bool ble_seen_sensor;
/** @brief 是否已连接 XDS 设备。 */
static bool ble_connected_sensor;
/** @brief 是否有手机 APP 连接到本机外设。 */
static bool ble_periph_connected;
static bool ble_adv_active;
static bool xds_scan_active;
/** @brief 是否检测到 ANT 码表已链路建立。 */
static bool ant_linked_display;
/** @brief 累计曲柄转数（供 CPS/CSCS）。 */
static uint32_t cumulative_crank_revs;
/** @brief 上次曲柄事件时间（1/1024s，16-bit 回卷）。 */
static uint16_t last_crank_event_time_1024;
/** @brief 曲柄更新参考时间戳（ms）。 */
static uint32_t last_crank_update_ms;
/** @brief 上次向 APP 发送通知时间戳（ms）。 */
static uint32_t last_app_notify_ms;
/** @brief 上次 APP 转发日志时间戳（ms）。 */
static uint32_t last_app_log_ms;
/** @brief 上次 RX 日志时间戳（ms）。 */
static uint32_t last_rx_log_ms;

/**
 * @brief BLE 外设广播数据（放服务与外观）。
 *
 * 说明：
 * - 将设备名移到扫描响应，降低首包长度，提升不同手机/手表扫描器的兼容性。
 * - 使用 UUID16_SOME（而非 ALL）避免被客户端严格按“完整列表”校验时误判。
 */
static const struct bt_data adv_ad[] = {
	BT_DATA_BYTES(BT_DATA_FLAGS, (BT_LE_AD_GENERAL | BT_LE_AD_NO_BREDR)),
	BT_DATA_BYTES(BT_DATA_GAP_APPEARANCE, BT_UUID_16_ENCODE(BT_APPEARANCE_CYCLING_POWER)),
	BT_DATA_BYTES(BT_DATA_UUID16_SOME,
		      BT_UUID_16_ENCODE(BT_UUID_CPS_VAL),
		      BT_UUID_16_ENCODE(BT_UUID_CSC_VAL)),
};

/** @brief BLE 外设扫描响应数据（放完整设备名）。 */
static const struct bt_data adv_sd[] = {
	BT_DATA(BT_DATA_NAME_COMPLETE, CONFIG_BT_DEVICE_NAME, sizeof(CONFIG_BT_DEVICE_NAME) - 1),
};

static void device_found(const bt_addr_le_t *addr, int8_t rssi, uint8_t type,
			 struct net_buf_simple *ad);

void ant_bpwr_evt_handler(ant_bpwr_profile_t *p_profile, ant_bpwr_evt_t event);
void ant_bpwr_calib_handler(ant_bpwr_profile_t *p_profile, ant_bpwr_page1_data_t *p_page1);

BPWR_SENS_CHANNEL_CONFIG_DEF(bpwr, CONFIG_BPWR_TX_CHANNEL_NUM, CONFIG_BPWR_TX_CHAN_ID_TRANS_TYPE,
			     CONFIG_BPWR_TX_CHAN_ID_DEV_NUM, CONFIG_BPWR_TX_NETWORK_NUM);
BPWR_SENS_PROFILE_CONFIG_DEF(bpwr, (ant_bpwr_torque_t)(CONFIG_SENSOR_TYPE), ant_bpwr_calib_handler,
			     ant_bpwr_evt_handler);

static ant_bpwr_profile_t bpwr;

static void cps_ccc_cfg_changed(const struct bt_gatt_attr *attr, uint16_t value);
static void csc_ccc_cfg_changed(const struct bt_gatt_attr *attr, uint16_t value);
static void update_ant_from_latest_data(bool bump_evt_on_tick);
static void notify_ble_apps_from_cache(void);
static int start_scan(void);
static int stop_scan(void);
static int start_advertising(void);
static void maintain_ble_links(void);
static ssize_t read_cps_feature(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				void *buf, uint16_t len, uint16_t offset);
static ssize_t read_sensor_location(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				    void *buf, uint16_t len, uint16_t offset);
static ssize_t read_csc_feature(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				void *buf, uint16_t len, uint16_t offset);

BT_GATT_SERVICE_DEFINE(cps_svc,
	BT_GATT_PRIMARY_SERVICE(BT_UUID_CPS),
	/* Measurement 按规范使用 Notify，避免客户端因可读属性判定为非标准实现。 */
	BT_GATT_CHARACTERISTIC(BT_UUID_GATT_CPS_CPM, BT_GATT_CHRC_NOTIFY,
			       BT_GATT_PERM_NONE, NULL, NULL, NULL),
	BT_GATT_CCC(cps_ccc_cfg_changed, BT_GATT_PERM_READ | BT_GATT_PERM_WRITE),
	BT_GATT_CHARACTERISTIC(BT_UUID_GATT_CPS_CPF, BT_GATT_CHRC_READ,
			       BT_GATT_PERM_READ, read_cps_feature, NULL, NULL),
	BT_GATT_CHARACTERISTIC(BT_UUID_SENSOR_LOCATION, BT_GATT_CHRC_READ,
			       BT_GATT_PERM_READ, read_sensor_location, NULL, NULL));

BT_GATT_SERVICE_DEFINE(csc_svc,
	BT_GATT_PRIMARY_SERVICE(BT_UUID_CSC),
	BT_GATT_CHARACTERISTIC(BT_UUID_CSC_MEASUREMENT, BT_GATT_CHRC_NOTIFY,
			       BT_GATT_PERM_NONE, NULL, NULL, NULL),
	BT_GATT_CCC(csc_ccc_cfg_changed, BT_GATT_PERM_READ | BT_GATT_PERM_WRITE),
	BT_GATT_CHARACTERISTIC(BT_UUID_CSC_FEATURE, BT_GATT_CHRC_READ,
			       BT_GATT_PERM_READ, read_csc_feature, NULL, NULL),
	BT_GATT_CHARACTERISTIC(BT_UUID_SENSOR_LOCATION, BT_GATT_CHRC_READ,
			       BT_GATT_PERM_READ, read_sensor_location, NULL, NULL));

/**
 * @brief 根据当前踏频更新曲柄累计圈数与事件时间。
 *
 * @param cadence_rpm 当前瞬时踏频（rpm）。
 * @param now_ms 当前系统毫秒计时。
 */
static void update_crank_metrics(uint16_t cadence_rpm, uint32_t now_ms)
{
	uint32_t per_rev_ms;
	uint32_t elapsed;
	uint16_t time_inc_1024;

	if (cadence_rpm == 0U) {
		return;
	}

	if (last_crank_update_ms == 0U) {
		last_crank_update_ms = now_ms;
		return;
	}

	per_rev_ms = 60000U / cadence_rpm;
	if (per_rev_ms == 0U) {
		per_rev_ms = 1U;
	}

	elapsed = now_ms - last_crank_update_ms;
	if (elapsed < per_rev_ms) {
		return;
	}

	time_inc_1024 = (uint16_t)MAX(1U, (per_rev_ms * 1024U) / 1000U);
	while (elapsed >= per_rev_ms) {
		cumulative_crank_revs++;
		last_crank_event_time_1024 = (uint16_t)(last_crank_event_time_1024 + time_inc_1024);
		last_crank_update_ms += per_rev_ms;
		elapsed -= per_rev_ms;
	}
}

/**
 * @brief 组装 CPS 测量包（功率+曲柄数据）。
 *
 * @param power_w 当前功率（W）。
 * @param cadence_rpm 当前踏频（rpm）。
 * @param out 输出缓冲区。
 *
 * @return 数据包长度（字节）。
 */
static size_t build_cps_measurement(uint16_t power_w, uint16_t cadence_rpm, uint8_t out[8])
{
	int16_t power_s16 = (power_w > INT16_MAX) ? INT16_MAX : (int16_t)power_w;
	uint16_t flags = BIT(5); /* Crank revolution data present. */
	uint32_t now = k_uptime_get_32();

	update_crank_metrics(cadence_rpm, now);
	sys_put_le16(flags, out);
	sys_put_le16((uint16_t)power_s16, out + 2);
	sys_put_le16((uint16_t)cumulative_crank_revs, out + 4);
	sys_put_le16(last_crank_event_time_1024, out + 6);
	return 8U;
}

/**
 * @brief 组装 CSCS 测量包（曲柄数据）。
 *
 * @param cadence_rpm 当前踏频（rpm）。
 * @param out 输出缓冲区。
 *
 * @return 数据包长度（字节）。
 */
static size_t build_csc_measurement(uint16_t cadence_rpm, uint8_t out[5])
{
	uint32_t now = k_uptime_get_32();

	update_crank_metrics(cadence_rpm, now);
	out[0] = BIT(1); /* Crank data present. */
	sys_put_le16((uint16_t)cumulative_crank_revs, out + 1);
	sys_put_le16(last_crank_event_time_1024, out + 3);
	return 5U;
}

static void cps_ccc_cfg_changed(const struct bt_gatt_attr *attr, uint16_t value)
{
	ARG_UNUSED(attr);
	cps_notify_enabled = (value == BT_GATT_CCC_NOTIFY);
}

static ssize_t read_cps_feature(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				void *buf, uint16_t len, uint16_t offset)
{
	uint32_t features = BIT(3); /* Crank revolution data supported. */

	return bt_gatt_attr_read(conn, attr, buf, len, offset, &features, sizeof(features));
}

static ssize_t read_sensor_location(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				    void *buf, uint16_t len, uint16_t offset)
{
	uint8_t sensor_location = 0x05; /* Left crank */

	return bt_gatt_attr_read(conn, attr, buf, len, offset,
				 &sensor_location, sizeof(sensor_location));
}

static void csc_ccc_cfg_changed(const struct bt_gatt_attr *attr, uint16_t value)
{
	ARG_UNUSED(attr);
	csc_notify_enabled = (value == BT_GATT_CCC_NOTIFY);
}

static ssize_t read_csc_feature(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				void *buf, uint16_t len, uint16_t offset)
{
	uint16_t features = BIT(1); /* Crank revolution data supported. */

	return bt_gatt_attr_read(conn, attr, buf, len, offset, &features, sizeof(features));
}

/**
 * @brief 将缓存数据立即转发给已订阅的 APP（每包 XDS 数据调用一次，~1Hz）。
 */
static void notify_ble_apps_from_cache(void)
{
	uint8_t cpm[8];
	uint16_t pwr;
	uint16_t cad;
	uint32_t now = k_uptime_get_32();
	size_t cpm_len;
	bool use_live_data;
	bool any_notified = false;

	if (!cps_notify_enabled && !csc_notify_enabled) {
		return;
	}

	k_mutex_lock(&data_lock, K_FOREVER);
	use_live_data = ble_connected_sensor && ((now - last_ble_data_ms) < DATA_TIMEOUT_MS);
	pwr = use_live_data ? latest_power_w : 0U;
	cad = use_live_data ? latest_cadence : 0U;
	k_mutex_unlock(&data_lock);

	if (cps_notify_enabled) {
		cpm_len = build_cps_measurement(pwr, cad, cpm);
		(void)bt_gatt_notify(NULL, &cps_svc.attrs[2], cpm, cpm_len);
		any_notified = true;
	}

	if (!ant_linked_display && csc_notify_enabled) {
		uint8_t csc[5];
		size_t csc_len = build_csc_measurement(cad, csc);

		(void)bt_gatt_notify(NULL, &csc_svc.attrs[2], csc, csc_len);
		any_notified = true;
	}

	if (any_notified && (now - last_app_log_ms) >= APP_LOG_INTERVAL_MS) {
		SLOG("APP TX P=%uW C=%urpm rev=%lu t=%u\n", pwr, cad,
		     (unsigned long)cumulative_crank_revs, last_crank_event_time_1024);
		last_app_log_ms = now;
	}
}

/**
 * @brief 按 ~4Hz 节拍刷新 ANT profile（主循环调用）。
 */
static void ant_update_if_due(void)
{
	uint32_t now = k_uptime_get_32();

	if ((now - last_ant_update_ms) < ANT_UPDATE_MS) {
		return;
	}
	last_ant_update_ms = now;
	update_ant_from_latest_data(true);
}

/**
 * @brief 按固定节拍向已订阅的 APP 发送 CPS/CSCS 通知（兜底，正常由 XDS 包触发）。
 */
static void notify_ble_apps_if_due(void)
{
	uint32_t now = k_uptime_get_32();

	if (!cps_notify_enabled && !csc_notify_enabled) {
		return;
	}

	if ((now - last_app_notify_ms) < APP_NOTIFY_INTERVAL_MS) {
		return;
	}
	last_app_notify_ms = now;
	notify_ble_apps_from_cache();
}

/**
 * @brief Maintain BLE advertising and burst scanning state.
 */
static void maintain_ble_links(void)
{
	uint32_t now = k_uptime_get_32();

	if (!ble_periph_connected &&
	    (!ble_adv_active || (now - last_adv_watchdog_ms) >= APP_ADV_WATCHDOG_MS)) {
		last_adv_watchdog_ms = now;
		(void)start_advertising();
	}

	if (sensor_conn || ble_connected_sensor) {
		return;
	}

	if (xds_scan_active) {
		if ((now - last_xds_scan_state_ms) >= XDS_SCAN_ON_MS) {
			(void)stop_scan();
		}
	} else if (last_xds_scan_state_ms == 0U ||
		   (now - last_xds_scan_state_ms) >= XDS_SCAN_OFF_MS) {
		(void)start_scan();
	}
}

/**
 * @brief 打印当前桥接状态（串口命令 status）。
 */
static void print_status(void)
{
	uint32_t age_ms = 0;
	uint32_t hz_x10 = 0;

	k_mutex_lock(&data_lock, K_FOREVER);
	if (last_ble_data_ms != 0U) {
		age_ms = k_uptime_get_32() - last_ble_data_ms;
	}
	if (rx_avg_interval_ms > 0U) {
		hz_x10 = 10000U / rx_avg_interval_ms;
	}
	printf("status: seen=%d ble_conn=%d ant_link=%d app=%d adv=%d scan=%d ble_out=%d/%d log=%d pwr=%u cad=%u err=%u evt=%u rate=%u.%uHz age=%ums\n",
	       ble_seen_sensor, ble_connected_sensor, ant_linked_display,
	       ble_periph_connected, ble_adv_active, xds_scan_active,
	       cps_notify_enabled, csc_notify_enabled, serial_log_enabled,
	       latest_power_w, latest_cadence, latest_error_code,
	       pwr_event_count, hz_x10 / 10U, hz_x10 % 10U, age_ms);
	k_mutex_unlock(&data_lock);
}

/**
 * @brief 处理串口命令入口。
 *
 * @param cmd 已解析完成的一行命令字符串。
 */
static void handle_command(const char *cmd)
{
	if (strcmp(cmd, "help") == 0) {
		printf("commands: help, status, scan, log on, log off\n");
		return;
	}
	if (strcmp(cmd, "log on") == 0) {
		serial_log_enabled = true;
		printf("serial log enabled\n");
		return;
	}
	if (strcmp(cmd, "log off") == 0) {
		serial_log_enabled = false;
		printf("serial log disabled\n");
		return;
	}
	if (strcmp(cmd, "status") == 0) {
		print_status();
		return;
	}
	if (strcmp(cmd, "scan") == 0) {
		(void)stop_scan();
		(void)start_scan();
		printf("scan restart requested\n");
		return;
	}
	printf("unknown command: %s\n", cmd);
}

/**
 * @brief 执行缓冲区中的待处理命令。
 */
static void execute_pending_command(void)
{
	if (cmd_len == 0U) {
		return;
	}

	cmd_buf[cmd_len] = '\0';
	handle_command(cmd_buf);
	cmd_len = 0U;
}

/**
 * @brief 轮询串口命令输入，支持换行触发与空闲超时触发。
 */
static void poll_uart_commands(void)
{
	unsigned char c;
	uint32_t now = k_uptime_get_32();

	if (!uart_console) {
		return;
	}

	while (uart_poll_in(uart_console, &c) == 0) {
		cmd_last_rx_ms = now;
		if (c == '\r' || c == '\n') {
			execute_pending_command();
			continue;
		}

		/* Support backspace/delete from various serial terminals. */
		if (c == '\b' || c == 0x7fU) {
			if (cmd_len > 0U) {
				cmd_len--;
			}
			continue;
		}

		/* Ignore non-printable bytes to avoid command corruption. */
		if (c < 0x20U || c > 0x7eU) {
			continue;
		}

		if (cmd_len < (CMD_BUF_LEN - 1U)) {
			cmd_buf[cmd_len++] = (char)c;
		} else {
			/* Execute on overflow so bytes are not endlessly concatenated. */
			execute_pending_command();
		}
	}

	/* Fallback: run command if terminal didn't send newline. */
	if (cmd_len > 0U && (now - cmd_last_rx_ms) > CMD_IDLE_EXEC_MS) {
		execute_pending_command();
	}
}

static bool ad_parse_cb(struct bt_data *data, void *user_data)
{
	bool *matched = user_data;
	uint16_t uuid;

	if (data->type != BT_DATA_UUID16_ALL && data->type != BT_DATA_UUID16_SOME) {
		return true;
	}

	for (size_t i = 0; i + 1 < data->data_len; i += 2) {
		uuid = sys_get_le16(&data->data[i]);
		if (uuid == XDS_SERVICE_UUID_16) {
			*matched = true;
			return false;
		}
	}

	return true;
}

static bool adv_has_xds_service(struct net_buf_simple *buf)
{
	bool matched = false;

	bt_data_parse(buf, ad_parse_cb, &matched);
	return matched;
}

/**
 * @brief XDS 测量通知回调：解析原始 11 字节数据并更新全局状态。
 *
 * 踏频字段采用已验证格式：byte6 有符号值，负值视为反踩并归零。
 */
static uint8_t notify_func(struct bt_conn *conn, struct bt_gatt_subscribe_params *params,
			   const void *data, uint16_t length)
{
	const uint8_t *raw = data;
	uint16_t total_power;
	int16_t left_power;
	int16_t right_power;
	int8_t raw_cadence_s8;
	uint8_t raw_cadence_u8;
	uint16_t angle_deg;
	uint16_t crank_angle_deg;
	uint16_t cadence_calc;
	uint8_t err_code;
	uint32_t now;

	ARG_UNUSED(conn);
	ARG_UNUSED(params);

	if (!data || length < 11) {
		return BT_GATT_ITER_CONTINUE;
	}

	/* XDS custom fixed 11-byte format from ESP32 implementation. */
	total_power = sys_get_le16(raw + 0);
	left_power = (int16_t)sys_get_le16(raw + 2);
	right_power = (int16_t)sys_get_le16(raw + 4);
	/* cpp2026042201.ino: byte6 is signed cadence, reverse pedaling appears as negative. */
	raw_cadence_s8 = (int8_t)raw[6];
	raw_cadence_u8 = raw[6];
	angle_deg = (uint16_t)(sys_get_le16(raw + 6) % 360U);
	crank_angle_deg = (uint16_t)(sys_get_le16(raw + 8) % 360U);
	err_code = raw[10];
	now = k_uptime_get_32();
	if (raw_cadence_s8 >= 0 && raw_cadence_s8 <= 200) {
		cadence_calc = (uint16_t)raw_cadence_s8;
	} else if (raw_cadence_u8 <= 200U) {
		/* 某些固件版本以无符号 byte6 上报踏频。 */
		cadence_calc = (uint16_t)raw_cadence_u8;
	} else {
		cadence_calc = 0U;
	}

	k_mutex_lock(&data_lock, K_FOREVER);
	latest_power_w = total_power;
	latest_left_power_w = left_power;
	latest_right_power_w = right_power;
	latest_cadence = cadence_calc;
	latest_error_code = err_code;
	last_ble_data_ms = now;
	if (last_rx_packet_ms != 0U) {
		uint32_t delta = now - last_rx_packet_ms;

		if (delta > 0U && delta < DATA_TIMEOUT_MS) {
			uint32_t acc_inc = ((uint32_t)total_power * delta * 4U) / 1000U;

			rx_avg_interval_ms = (rx_avg_interval_ms == 0U) ? delta :
					      ((rx_avg_interval_ms * 7U) + delta) / 8U;
			accumulated_power = (uint16_t)(accumulated_power + acc_inc);
		}
	}
	last_rx_packet_ms = now;
	pwr_event_count++;
	k_mutex_unlock(&data_lock);

	update_ant_from_latest_data(false);
	notify_ble_apps_from_cache();
	last_ant_update_ms = k_uptime_get_32();

	if ((now - last_rx_log_ms) >= RX_LOG_INTERVAL_MS) {
		SLOG("RX P=%uW C=%urpm E=%u (L=%d R=%d A=%u CA=%u B6=0x%02X)\n",
		     total_power, cadence_calc, err_code, left_power, right_power, angle_deg,
		     crank_angle_deg, raw_cadence_u8);
		last_rx_log_ms = now;
	}
	return BT_GATT_ITER_CONTINUE;
}

static void subscribe_func(struct bt_conn *conn, uint8_t err,
			   struct bt_gatt_subscribe_params *params)
{
	ARG_UNUSED(conn);
	ARG_UNUSED(params);
	if (err) {
		LOG_ERR("CCCD subscribe write failed (ATT err 0x%02x)", err);
	} else {
		LOG_INF("CCCD subscribe write OK");
	}
}

static uint8_t discover_func(struct bt_conn *conn, const struct bt_gatt_attr *attr,
			     struct bt_gatt_discover_params *params)
{
	int err;

	if (!attr) {
		LOG_WRN("GATT discover finished without full match");
		(void)memset(params, 0, sizeof(*params));
		return BT_GATT_ITER_STOP;
	}

	if (params->type == BT_GATT_DISCOVER_PRIMARY) {
		const struct bt_gatt_service_val *service = attr->user_data;

		service_start_handle = attr->handle + 1;
		service_end_handle = service->end_handle;

		discover_uuid.uuid.type = BT_UUID_TYPE_16;
		discover_uuid.val = XDS_MEAS_UUID_16;
		discover_params.uuid = &discover_uuid.uuid;
		discover_params.start_handle = service_start_handle;
		discover_params.end_handle = service_end_handle;
		discover_params.type = BT_GATT_DISCOVER_CHARACTERISTIC;

		err = bt_gatt_discover(conn, &discover_params);
		if (err) {
			LOG_ERR("Characteristic discover failed (%d)", err);
		}
		return BT_GATT_ITER_STOP;
	}

	if (params->type == BT_GATT_DISCOVER_CHARACTERISTIC) {
		const struct bt_gatt_chrc *chrc = attr->user_data;

		subscribe_params.notify = notify_func;
		subscribe_params.subscribe = subscribe_func;
		subscribe_params.value = BT_GATT_CCC_NOTIFY;
		subscribe_params.value_handle = chrc->value_handle;
		subscribe_params.ccc_handle = chrc->value_handle + 1;

		LOG_INF("XDS char discovered: handle=0x%04x props=0x%02x ccc=0x%04x",
			chrc->value_handle, chrc->properties, subscribe_params.ccc_handle);

		err = bt_gatt_subscribe(conn, &subscribe_params);
		if (err && err != -EALREADY) {
			LOG_ERR("Subscribe failed (%d)", err);
		} else {
			LOG_INF("Subscribed to XDS measurement notifications");
		}

		(void)memset(params, 0, sizeof(*params));
		return BT_GATT_ITER_STOP;
	}

	return BT_GATT_ITER_STOP;
}

/**
 * @brief 启动 BLE 扫描（中央角色），搜索 XDS 服务。
 *
 * @return 0 成功，其它为错误码。
 */
static int start_scan(void)
{
	int err;
	struct bt_le_scan_param param = {
		.type = BT_LE_SCAN_TYPE_ACTIVE,
		.options = BT_LE_SCAN_OPT_NONE,
		.interval = BT_GAP_SCAN_FAST_INTERVAL,
		.window = BT_GAP_SCAN_FAST_WINDOW / 2,
	};

	if (sensor_conn || ble_connected_sensor) {
		xds_scan_active = false;
		return 0;
	}

	err = bt_le_scan_start(&param, device_found);
	if (err == -EALREADY) {
		xds_scan_active = true;
		last_xds_scan_state_ms = k_uptime_get_32();
		return 0;
	}
	if (err) {
		xds_scan_active = false;
		LOG_ERR("Scan start failed (%d)", err);
		return err;
	}

	xds_scan_active = true;
	last_xds_scan_state_ms = k_uptime_get_32();
	LOG_INF("BLE scanning for XDS service (0x1828)");
	return 0;
}

static int stop_scan(void)
{
	int err = bt_le_scan_stop();

	if (err && err != -EALREADY) {
		LOG_WRN("Scan stop failed (%d)", err);
		return err;
	}

	xds_scan_active = false;
	last_xds_scan_state_ms = k_uptime_get_32();
	return 0;
}

/**
 * @brief 启动本机 BLE 外设广播（CPS+CSCS）。
 *
 * @return 0 成功，其它为错误码。
 */
static int start_advertising(void)
{
	int err;
	struct bt_le_adv_param adv_param = {
		.options = BT_LE_ADV_OPT_CONN,
		.interval_min = APP_ADV_INTERVAL_MIN,
		.interval_max = APP_ADV_INTERVAL_MAX,
		.peer = NULL,
	};

	if (ble_periph_connected) {
		ble_adv_active = false;
		return 0;
	}

	err = bt_le_adv_start(&adv_param,
			      adv_ad, ARRAY_SIZE(adv_ad),
			      adv_sd, ARRAY_SIZE(adv_sd));
	if (err == -EALREADY) {
		ble_adv_active = true;
		last_adv_watchdog_ms = k_uptime_get_32();
		return 0;
	}
	if (err) {
		ble_adv_active = false;
		LOG_ERR("Adv start failed (%d)", err);
		return err;
	}

	ble_adv_active = true;
	last_adv_watchdog_ms = k_uptime_get_32();
	LOG_INF("BLE peripheral advertising started (CPS+CSCS)");
	return 0;
}

/**
 * @brief 扫描回调：发现目标设备后停止扫描并发起连接。
 */
static void device_found(const bt_addr_le_t *addr, int8_t rssi, uint8_t type,
			 struct net_buf_simple *ad)
{
	int err;
	struct bt_conn_le_create_param create_param = BT_CONN_LE_CREATE_PARAM_INIT(
		BT_CONN_LE_OPT_NONE, BT_GAP_SCAN_FAST_INTERVAL, BT_GAP_SCAN_FAST_INTERVAL);
	struct bt_le_conn_param conn_param = BT_LE_CONN_PARAM_INIT(
		48, 72, 0, BT_GAP_MS_TO_CONN_TIMEOUT(XDS_CONN_TIMEOUT_MS));

	ARG_UNUSED(rssi);
	ARG_UNUSED(type);

	if (sensor_conn || !adv_has_xds_service(ad)) {
		return;
	}

	ble_seen_sensor = true;

	err = stop_scan();
	if (err && err != -EALREADY) {
		return;
	}

	err = bt_conn_le_create(addr, &create_param, &conn_param, &sensor_conn);
	if (err) {
		LOG_ERR("Create conn failed (%d)", err);
		sensor_conn = NULL;
		(void)start_scan();
		return;
	}

	LOG_INF("Connecting to XDS meter (RSSI %d)...", rssi);
}

/**
 * @brief BLE 连接事件回调（中央/外设双角色共用）。
 */
static void connected(struct bt_conn *conn, uint8_t err)
{
	struct bt_conn_info info;

	if (err) {
		LOG_ERR("BLE connect failed (%u)", err);
		/* 仅当失败的是中央侧（连 XDS）对象时，才清理 sensor_conn。 */
		if (sensor_conn && conn == sensor_conn) {
			bt_conn_unref(sensor_conn);
			sensor_conn = NULL;
			ble_connected_sensor = false;
			(void)start_scan();
		} else {
			/* 外设侧连接失败时，确保仍可被后续 APP/手表发现。 */
			(void)start_advertising();
		}
		return;
	}

	if (bt_conn_get_info(conn, &info) != 0 || info.type != BT_CONN_TYPE_LE) {
		return;
	}

	if (info.role == BT_CONN_ROLE_CENTRAL) {
		struct bt_le_conn_param xds_param =
			BT_LE_CONN_PARAM_INIT(48, 72, 0, BT_GAP_MS_TO_CONN_TIMEOUT(XDS_CONN_TIMEOUT_MS));
		int perr;

		xds_scan_active = false;
		ble_connected_sensor = true;
		LOG_INF("BLE connected to XDS");
		perr = bt_conn_le_param_update(conn, &xds_param);
		if (perr && perr != -EALREADY) {
			LOG_WRN("XDS conn param update failed (%d)", perr);
		}

		discover_uuid.uuid.type = BT_UUID_TYPE_16;
		discover_uuid.val = XDS_SERVICE_UUID_16;
		discover_params.uuid = &discover_uuid.uuid;
		discover_params.func = discover_func;
		discover_params.start_handle = BT_ATT_FIRST_ATTRIBUTE_HANDLE;
		discover_params.end_handle = BT_ATT_LAST_ATTRIBUTE_HANDLE;
		discover_params.type = BT_GATT_DISCOVER_PRIMARY;

		if (bt_gatt_discover(conn, &discover_params)) {
			LOG_ERR("Primary service discover failed");
		}
	} else {
		/* APP/watch connections use tighter parameters for outdoor stability. */
		struct bt_le_conn_param app_param =
			BT_LE_CONN_PARAM_INIT(APP_CONN_INTERVAL_MIN, APP_CONN_INTERVAL_MAX,
					      APP_CONN_LATENCY,
					      BT_GAP_MS_TO_CONN_TIMEOUT(APP_CONN_TIMEOUT_MS));
		int perr;

		ble_periph_connected = true;
		ble_adv_active = false;
		last_crank_update_ms = k_uptime_get_32();
		perr = bt_conn_le_param_update(conn, &app_param);
		if (perr && perr != -EALREADY) {
			LOG_WRN("BLE app conn param update failed (%d)", perr);
		}
		LOG_INF("BLE app/phone connected to local CPS");
	}
}

/**
 * @brief BLE 断开事件回调，负责重连扫描与外设广播恢复。
 */
static void disconnected(struct bt_conn *conn, uint8_t reason)
{
	struct bt_conn_info info;

	LOG_WRN("BLE disconnected (reason 0x%02x)", reason);
	if (bt_conn_get_info(conn, &info) != 0 || info.type != BT_CONN_TYPE_LE) {
		return;
	}

	if (info.role == BT_CONN_ROLE_CENTRAL) {
		ble_connected_sensor = false;
		if (sensor_conn) {
			bt_conn_unref(sensor_conn);
			sensor_conn = NULL;
		}
		(void)memset(&subscribe_params, 0, sizeof(subscribe_params));
		(void)start_scan();
	} else {
		ble_periph_connected = false;
		ble_adv_active = false;
		/* 手机 APP 断开后必须立即恢复可连接广播，否则 APP 无法再次连接。 */
		(void)start_advertising();
	}
}

BT_CONN_CB_DEFINE(conn_callbacks) = {
	.connected = connected,
	.disconnected = disconnected,
};

void ant_bpwr_evt_handler(ant_bpwr_profile_t *p_profile, ant_bpwr_evt_t event)
{
	ARG_UNUSED(p_profile);
	ARG_UNUSED(event);
}

void ant_bpwr_calib_handler(ant_bpwr_profile_t *p_profile, ant_bpwr_page1_data_t *p_page1)
{
	switch (p_page1->calibration_id) {
	case ANT_BPWR_CALIB_ID_MANUAL:
		bpwr.BPWR_PROFILE_calibration_id = ANT_BPWR_CALIB_ID_MANUAL_SUCCESS;
		bpwr.BPWR_PROFILE_general_calib_data = CONFIG_BPWR_TX_CALIBRATION_DATA;
		break;
	case ANT_BPWR_CALIB_ID_AUTO:
		bpwr.BPWR_PROFILE_calibration_id = ANT_BPWR_CALIB_ID_MANUAL_SUCCESS;
		bpwr.BPWR_PROFILE_auto_zero_status = p_page1->auto_zero_status;
		bpwr.BPWR_PROFILE_general_calib_data = CONFIG_BPWR_TX_CALIBRATION_DATA;
		break;
	case ANT_BPWR_CALIB_ID_CUSTOM_REQ:
		bpwr.BPWR_PROFILE_calibration_id = ANT_BPWR_CALIB_ID_CUSTOM_REQ_SUCCESS;
		memcpy(bpwr.BPWR_PROFILE_custom_calib_data, p_page1->data.custom_calib,
		       sizeof(bpwr.BPWR_PROFILE_custom_calib_data));
		break;
	case ANT_BPWR_CALIB_ID_CUSTOM_UPDATE:
		bpwr.BPWR_PROFILE_calibration_id = ANT_BPWR_CALIB_ID_CUSTOM_UPDATE_SUCCESS;
		memcpy(bpwr.BPWR_PROFILE_custom_calib_data, p_page1->data.custom_calib,
		       sizeof(bpwr.BPWR_PROFILE_custom_calib_data));
		break;
	default:
		break;
	}
}

static void ant_evt_handler(ant_evt_t *p_ant_evt)
{
	ant_bpwr_sens_evt_handler(p_ant_evt, &bpwr);

	switch (p_ant_evt->event) {
	case EVENT_CONNECTION_SUCCESS:
	case EVENT_RX:
		ant_linked_display = true;
		break;
	case EVENT_CONNECTION_FAIL:
	case EVENT_CONNECTION_TIMEOUT:
	case EVENT_CHANNEL_CLOSED:
	case EVENT_RX_SEARCH_TIMEOUT:
		ant_linked_display = false;
		break;
	default:
		break;
	}
}

static int profile_setup(void)
{
	int err = ant_bpwr_sens_init(&bpwr, BPWR_SENS_CHANNEL_CONFIG(bpwr),
				     BPWR_SENS_PROFILE_CONFIG(bpwr));

	if (err) {
		LOG_ERR("ant_bpwr_sens_init failed: %d", err);
		return err;
	}

	bpwr.page_80 = ANT_COMMON_page80(CONFIG_BPWR_TX_HW_VERSION, CONFIG_BPWR_TX_MFG_ID,
					 CONFIG_BPWR_TX_MODEL_NUM);
	bpwr.page_81 = ANT_COMMON_page81(CONFIG_BPWR_TX_SW_VERSION, CONFIG_BPWR_TX_SW_VERSION,
					 CONFIG_BPWR_TX_SERIAL_NUM);
	bpwr.BPWR_PROFILE_auto_zero_status = ANT_BPWR_AUTO_ZERO_OFF;
	bpwr.BPWR_PROFILE_instantaneous_power = 0;
	bpwr.BPWR_PROFILE_accumulated_power = 0;
	bpwr.BPWR_PROFILE_power_update_event_count = 0;
	bpwr.BPWR_PROFILE_instantaneous_cadence = 0;

	err = ant_bpwr_sens_open(&bpwr);
	if (err) {
		LOG_ERR("ant_bpwr_sens_open failed: %d", err);
		return err;
	}


	LOG_INF("ANT+ BPWR TX open: dev=%d type=11", CONFIG_BPWR_TX_CHAN_ID_DEV_NUM);
	return 0;
}

static int ant_stack_setup(void)
{
	int err = ant_init();

	if (err) {
		LOG_ERR("ant_init failed: %d", err);
		return err;
	}

	LOG_INF("ANT version %s", ANT_VERSION_STRING);

	err = ant_cb_register(&ant_evt_handler);
	if (err) {
		LOG_ERR("ant_cb_register failed: %d", err);
		return err;
	}

	err = ant_plus_key_set(CONFIG_BPWR_TX_NETWORK_NUM);
	if (err) {
		LOG_ERR("ant_plus_key_set failed: %d", err);
		return err;
	}

	return 0;
}

static int leds_init(void)
{
	if (!gpio_is_ready_dt(&led0) || !gpio_is_ready_dt(&led1) || !gpio_is_ready_dt(&led2)) {
		LOG_ERR("One or more LED GPIOs are not ready");
		return -ENODEV;
	}

	if (gpio_pin_configure_dt(&led0, GPIO_OUTPUT_INACTIVE) < 0 ||
	    gpio_pin_configure_dt(&led1, GPIO_OUTPUT_INACTIVE) < 0 ||
	    gpio_pin_configure_dt(&led2, GPIO_OUTPUT_INACTIVE) < 0) {
		LOG_ERR("Failed to configure LED pins");
		return -EIO;
	}

	return 0;
}

static void set_leds(bool l0, bool l1, bool l2)
{
	(void)gpio_pin_set_dt(&led0, l0);
	(void)gpio_pin_set_dt(&led1, l1);
	(void)gpio_pin_set_dt(&led2, l2);
}

/**
 * @brief 更新三颗 LED 状态指示。
 *
 * LED2(P0.04): APP 已连接常亮，否则慢闪。
 */
static void update_led_pattern(void)
{
	uint32_t now = k_uptime_get_32();
	bool slow_on = ((now / SLOW_BLINK_HALF_MS) & 0x1U) == 0U;
	bool ant_led;

	if (!ble_seen_sensor) {
		set_leds(slow_on, slow_on, ble_periph_connected ? true : slow_on);
		return;
	}

	/* LED1: blink while ANT display (bike computer) is not linked, solid on when linked. */
	ant_led = ant_linked_display ? true : slow_on;
	set_leds(true, ant_led, ble_periph_connected ? true : slow_on);
}

/**
 * @brief 将最新 BLE 数据映射到 ANT BPWR 发送结构。
 *
 * 包括功率、踏频与左右平衡字段，供码表通过 ANT+ 读取。
 */
/**
 * @brief 将最新 BLE 数据映射到 ANT BPWR 页面字段。
 */
static void update_ant_from_latest_data(bool bump_evt_on_tick)
{
	uint16_t pwr;
	uint16_t cad;
	uint8_t evt;
	uint16_t acc;
	int16_t left_w;
	int16_t right_w;
	uint32_t now = k_uptime_get_32();
	bool use_live_data;
	uint32_t lr_sum;
	uint32_t right_pct;

	k_mutex_lock(&data_lock, K_FOREVER);
	use_live_data = ble_connected_sensor && ((now - last_ble_data_ms) < DATA_TIMEOUT_MS);
	if (bump_evt_on_tick && use_live_data) {
		pwr_event_count++;
	}
	pwr = use_live_data ? latest_power_w : 0U;
	cad = use_live_data ? latest_cadence : 0U;
	left_w = use_live_data ? latest_left_power_w : 0;
	right_w = use_live_data ? latest_right_power_w : 0;
	evt = pwr_event_count;
	acc = accumulated_power;
	k_mutex_unlock(&data_lock);

	bpwr.BPWR_PROFILE_instantaneous_power = pwr;
	/* Forward parsed cadence to ANT+ (0xFF is reserved as invalid). */
	bpwr.BPWR_PROFILE_instantaneous_cadence = (cad > 254U) ? 254U : (uint8_t)cad;
	if (use_live_data && left_w >= 0 && right_w >= 0) {
		lr_sum = (uint32_t)left_w + (uint32_t)right_w;
		if (lr_sum > 0U) {
			right_pct = ((uint32_t)right_w * 100U + (lr_sum / 2U)) / lr_sum;
			if (right_pct > 100U) {
				right_pct = 100U;
			}
			bpwr.BPWR_PROFILE_pedal_power.differentiation = 1U; /* right % */
			bpwr.BPWR_PROFILE_pedal_power.distribution = (uint8_t)right_pct;
		} else {
			bpwr.page_16.pedal_power.byte = 0xFFU;
		}
	} else {
		bpwr.page_16.pedal_power.byte = 0xFFU;
	}
	bpwr.BPWR_PROFILE_power_update_event_count = evt;
	bpwr.BPWR_PROFILE_accumulated_power = acc;
}

/**
 * @brief 程序主入口：初始化 ANT/BLE 并执行桥接主循环。
 */
int main(void)
{
	int err;

	k_mutex_init(&data_lock);
	uart_console = DEVICE_DT_GET(DT_CHOSEN(zephyr_console));

	if (leds_init() < 0) {
		return 0;
	}

	err = ant_stack_setup();
	if (err) {
		return 0;
	}

	err = profile_setup();
	if (err) {
		return 0;
	}

	err = bt_enable(NULL);
	if (err) {
		LOG_ERR("Bluetooth init failed (%d)", err);
		return 0;
	}

	err = start_advertising();
	if (err) {
		LOG_WRN("Continue without BLE peripheral output");
	}

	err = start_scan();
	if (err && err != -EALREADY) {
		LOG_ERR("Scan start failed (%d)", err);
	}

	LOG_INF("Bridge running: BLE(XDS) -> ANT + BLE(CPS)");
	printf("Type 'help' for commands (log off by default).\n");

	while (1) {
		poll_uart_commands();
		maintain_ble_links();
		notify_ble_apps_if_due();
		ant_update_if_due();
		update_led_pattern();
		k_sleep(K_MSEC(MAIN_LOOP_MS));
	}

	
}
