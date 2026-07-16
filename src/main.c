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
#include <zephyr/drivers/watchdog.h>
#include <zephyr/kernel.h>
#include <zephyr/logging/log.h>
#include <zephyr/sys/atomic.h>
#include <zephyr/sys/byteorder.h>
#include <zephyr/sys/reboot.h>
#include <zephyr/sys/util.h>

#include <ant_key_manager.h>
#include <ant_parameters.h>
#include <ant_profiles/bpwr/ant_bpwr.h>

LOG_MODULE_REGISTER(xds_ant_bridge, LOG_LEVEL_INF);

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
/** @brief 未通过 GATT 验证的地址暂停重试时间（ms）。 */
#define XDS_REJECT_RETRY_MS 30000
/** @brief ANT RX 活动多久后不再显示码表在线（ms）。 */
#define ANT_DISPLAY_ACTIVITY_TIMEOUT_MS 10000
/** @brief XDS 可接受的最大总功率/单侧功率绝对值（W）。 */
#define XDS_MAX_POWER_W 3000
/** @brief 硬件看门狗超时（ms）。 */
#define WDT_TIMEOUT_MS 5000
/** @brief 初始化失败后重启前的错误显示时间（ms）。 */
#define FATAL_REBOOT_DELAY_MS 2000
/** @brief 无法立即断开异常 XDS 连接时的重试周期（ms）。 */
#define SENSOR_DISCONNECT_RETRY_MS 1000
/** @brief XDS 功率计服务 UUID（16-bit）。 */
#define XDS_SERVICE_UUID_16 0x1828
/** @brief XDS 功率计测量特征 UUID（16-bit）。 */
#define XDS_MEAS_UUID_16 0x2A63

/** @brief 板载 LED0。 */
#define LED0_NODE DT_ALIAS(led0)
/** @brief 板载 LED1。 */
#define LED1_NODE DT_ALIAS(led1)
/** @brief 板载 LED2，用于 BLE 外设连接状态指示。 */
#define LED2_NODE DT_ALIAS(led2)
/** @brief nRF52840 硬件看门狗。 */
#define WDT_NODE DT_NODELABEL(wdt0)

/** @brief 串口命令缓冲区长度。 */
#define CMD_BUF_LEN 64
/** @brief 每轮主循环最多处理的串口字节数，避免持续输入饿死看门狗。 */
#define UART_RX_BUDGET 64
/** @brief 无换行命令的自动执行空闲时间（ms）。 */
#define CMD_IDLE_EXEC_MS 1200

static const struct gpio_dt_spec led0 = GPIO_DT_SPEC_GET(LED0_NODE, gpios);
static const struct gpio_dt_spec led1 = GPIO_DT_SPEC_GET(LED1_NODE, gpios);
static const struct gpio_dt_spec led2 = GPIO_DT_SPEC_GET(LED2_NODE, gpios);
static const struct device *const wdt_dev = DEVICE_DT_GET(WDT_NODE);
static int wdt_channel_id = -1;
static bool leds_initialized;

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
static uint32_t last_sensor_disconnect_retry_ms;

/** @brief 当前与 XDS 连接对象（中央角色）。 */
static struct bt_conn *sensor_conn;
/** @brief 保护 sensor_conn 引用的短临界区锁。 */
static struct k_spinlock sensor_conn_lock;
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
/** @brief 已通过完整 GATT 验证的 XDS 地址（本次上电期间绑定）。 */
static bt_addr_le_t validated_sensor_addr;
static bool validated_sensor_addr_valid;
/** @brief 最近未通过 GATT 验证的地址及其退避起点。 */
static bt_addr_le_t rejected_sensor_addr;
static bool rejected_sensor_addr_valid;
static uint32_t rejected_sensor_at_ms;

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
/** @brief 最新数据包是否通过范围与错误码校验。 */
static bool latest_data_valid;
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
/** @brief 当前与 APP/手表的外设连接数（按连接计数，支持多设备同时连接）。 */
static uint8_t periph_conn_count;
/** @brief CPS 测量值特征属性指针（延迟到首次广播后取，避免 BT_GATT_SERVICE_DEFINE 顺序问题）。 */
static const struct bt_gatt_attr *cps_meas_attr;
/** @brief CSCS 测量值特征属性指针。 */
static const struct bt_gatt_attr *csc_meas_attr;

/** @brief 是否扫描到目标 XDS 设备。 */
static bool ble_seen_sensor;
/** @brief 是否已连接 XDS 设备。 */
static bool ble_connected_sensor;
/** @brief XDS 测量特征已成功订阅，可以使用本连接的数据。 */
static bool ble_sensor_ready;
static bool ble_adv_active;
static bool xds_scan_active;
/** @brief 是否检测到 ANT 码表已链路建立。 */
static bool ant_linked_display;
/** @brief 最近一次收到 ANT 对端消息的时间。 */
static uint32_t last_ant_rx_ms;
/** @brief 累计曲柄转数（供 CPS/CSCS）。 */
static uint32_t cumulative_crank_revs;
/** @brief 上次曲柄事件时间（1/1024s，16-bit 回卷）。 */
static uint16_t last_crank_event_time_1024;
/** @brief 曲柄更新参考时间戳（ms）。 */
static uint32_t last_crank_update_ms;
/** @brief 上一次曲柄状态是否为转动。 */
static bool crank_was_moving;
/** @brief 上次向 APP 发送通知时间戳（ms）。 */
static uint32_t last_app_notify_ms;
/** @brief 上次 APP 转发日志时间戳（ms）。 */
static uint32_t last_app_log_ms;
/** @brief 上次 RX 日志时间戳（ms）。 */
static uint32_t last_rx_log_ms;
/** @brief 收到新 XDS 包后请求主循环尽快发送 APP 通知。 */
static atomic_t app_notify_pending;
/** @brief 收到新 XDS 包后请求主循环异步输出 RX 日志。 */
static atomic_t rx_log_pending;
/** @brief bind clear 断开期间禁止当前连接重新完成绑定。 */
static atomic_t bind_clear_pending;
/** @brief 当前 XDS 连接需要在主循环中重试断开。 */
static atomic_t sensor_disconnect_pending;

static bool sensor_conn_exists(void)
{
	k_spinlock_key_t key = k_spin_lock(&sensor_conn_lock);
	bool exists = sensor_conn != NULL;

	k_spin_unlock(&sensor_conn_lock, key);
	return exists;
}

static struct bt_conn *sensor_conn_ref_get(void)
{
	k_spinlock_key_t key = k_spin_lock(&sensor_conn_lock);
	struct bt_conn *conn = sensor_conn != NULL ? bt_conn_ref(sensor_conn) : NULL;

	k_spin_unlock(&sensor_conn_lock, key);
	return conn;
}

static void sensor_conn_store(struct bt_conn *conn)
{
	k_spinlock_key_t key = k_spin_lock(&sensor_conn_lock);

	sensor_conn = conn;
	k_spin_unlock(&sensor_conn_lock, key);
}

static struct bt_conn *sensor_conn_take_if(struct bt_conn *expected)
{
	k_spinlock_key_t key = k_spin_lock(&sensor_conn_lock);
	struct bt_conn *conn = NULL;

	if (sensor_conn == expected) {
		conn = sensor_conn;
		sensor_conn = NULL;
	}
	k_spin_unlock(&sensor_conn_lock, key);
	return conn;
}

static bool sensor_conn_matches(struct bt_conn *conn)
{
	k_spinlock_key_t key = k_spin_lock(&sensor_conn_lock);
	bool matches = sensor_conn == conn;

	k_spin_unlock(&sensor_conn_lock, key);
	return matches;
}

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
static void update_ant_from_latest_data(void);
static void notify_ble_apps_from_cache(void);
static int start_scan(void);
static int stop_scan(void);
static int start_advertising(void);
static void maintain_ble_links(void);
static void log_rx_if_due(void);
static ssize_t read_cps_feature(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				void *buf, uint16_t len, uint16_t offset);
static ssize_t read_sensor_location(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				    void *buf, uint16_t len, uint16_t offset);
static ssize_t read_csc_feature(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				void *buf, uint16_t len, uint16_t offset);

/* Index of the measurement VALUE attribute inside each GATT service definition.
 * CPI/SVC(0) -> CHRC-decl(1) -> CHRC-value(2) -> CCC(3) ...  */
#define CPS_MEAS_ATTR_IDX 2U
#define CSC_MEAS_ATTR_IDX 2U

/* 订阅判断 helpers（函数体在 BT_GATT_SERVICE_DEFINE 之后，因要引用 cps_svc/csc_svc）。 */
static bool cps_any_subscribed(void);
static bool csc_any_subscribed(void);

struct subscription_check {
	const struct bt_gatt_attr *attr;
	bool subscribed;
};

static void check_connection_subscription(struct bt_conn *conn, void *user_data)
{
	struct subscription_check *check = user_data;

	if (!check->subscribed &&
	    bt_gatt_is_subscribed(conn, check->attr, BT_GATT_CCC_NOTIFY)) {
		check->subscribed = true;
	}
}

static bool any_connection_subscribed(const struct bt_gatt_attr *attr)
{
	struct subscription_check check = {
		.attr = attr,
		.subscribed = false,
	};

	bt_conn_foreach(BT_CONN_TYPE_LE, check_connection_subscription, &check);
	return check.subscribed;
}

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

/** @brief 是否有任一外设连接订阅了 CPS 通知（按连接判断，天然支持多设备）。 */
static bool cps_any_subscribed(void)
{
	if (cps_meas_attr == NULL) {
		cps_meas_attr = &cps_svc.attrs[CPS_MEAS_ATTR_IDX];
	}
	return any_connection_subscribed(cps_meas_attr);
}

/** @brief 是否有任一外设连接订阅了 CSCS 通知。 */
static bool csc_any_subscribed(void)
{
	if (csc_meas_attr == NULL) {
		csc_meas_attr = &csc_svc.attrs[CSC_MEAS_ATTR_IDX];
	}
	return any_connection_subscribed(csc_meas_attr);
}

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
		/* 停脚后令下一次非零样本只建立时间基准，不补算停脚期。 */
		last_crank_update_ms = now_ms;
		crank_was_moving = false;
		return;
	}

	if (!crank_was_moving || last_crank_update_ms == 0U) {
		last_crank_update_ms = now_ms;
		crank_was_moving = true;
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

/* 订阅状态由 Zephyr 按 per-connection 维护，无需手写标志位；
 * notify 用 bt_gatt_notify(NULL,...) 广播给所有已开 CCC 的连接，
 * 是否有人订阅通过 bt_conn_foreach() 对每个有效连接检查。
 */
static void cps_ccc_cfg_changed(const struct bt_gatt_attr *attr, uint16_t value)
{
	ARG_UNUSED(attr);
	ARG_UNUSED(value);
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
	ARG_UNUSED(value);
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
	bool cps_sub;
	bool csc_sub;

	cps_sub = cps_any_subscribed();
	csc_sub = csc_any_subscribed();
	if (!cps_sub && !csc_sub) {
		return;
	}

	k_mutex_lock(&data_lock, K_FOREVER);
	use_live_data = ble_sensor_ready && latest_data_valid &&
			((now - last_ble_data_ms) < DATA_TIMEOUT_MS);
	pwr = use_live_data ? latest_power_w : 0U;
	cad = use_live_data ? latest_cadence : 0U;
	k_mutex_unlock(&data_lock);

	if (cps_sub) {
		cpm_len = build_cps_measurement(pwr, cad, cpm);
		(void)bt_gatt_notify(NULL, cps_meas_attr, cpm, cpm_len);
		any_notified = true;
	}

	if (csc_sub) {
		uint8_t csc[5];
		size_t csc_len = build_csc_measurement(cad, csc);

		(void)bt_gatt_notify(NULL, csc_meas_attr, csc, csc_len);
		any_notified = true;
	}

	if (any_notified && (now - last_app_log_ms) >= APP_LOG_INTERVAL_MS) {
		SLOG("APP TX P=%uW C=%urpm rev=%lu t=%u\n",
		     (unsigned int)pwr, (unsigned int)cad,
		     (unsigned long)cumulative_crank_revs,
		     (unsigned int)last_crank_event_time_1024);
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
	update_ant_from_latest_data();
}

/**
 * @brief 按固定节拍向已订阅的 APP 发送 CPS/CSCS 通知（兜底，正常由 XDS 包触发）。
 */
static void notify_ble_apps_if_due(void)
{
	uint32_t now = k_uptime_get_32();

	if (atomic_clear(&app_notify_pending) == 0 &&
	    (now - last_app_notify_ms) < APP_NOTIFY_INTERVAL_MS) {
		return;
	}
	last_app_notify_ms = now;
	notify_ble_apps_from_cache();
}

/**
 * @brief 在主循环中输出最近一包 RX 数据，避免在 GATT 回调里阻塞 UART。
 */
static void log_rx_if_due(void)
{
	uint32_t now = k_uptime_get_32();
	uint16_t pwr;
	uint16_t cad;
	int16_t left;
	int16_t right;
	uint8_t err;
	bool valid;

	if (!serial_log_enabled || atomic_get(&rx_log_pending) == 0 ||
	    (now - last_rx_log_ms) < RX_LOG_INTERVAL_MS) {
		return;
	}

	(void)atomic_clear(&rx_log_pending);
	k_mutex_lock(&data_lock, K_FOREVER);
	pwr = latest_power_w;
	cad = latest_cadence;
	left = latest_left_power_w;
	right = latest_right_power_w;
	err = latest_error_code;
	valid = latest_data_valid;
	k_mutex_unlock(&data_lock);

	SLOG("RX P=%uW C=%urpm E=%u L=%d R=%d valid=%d\n",
	     (unsigned int)pwr, (unsigned int)cad, (unsigned int)err,
	     left, right, valid);
	last_rx_log_ms = now;
}

/**
 * @brief Maintain BLE advertising and burst scanning state.
 */
static void maintain_ble_links(void)
{
	uint32_t now = k_uptime_get_32();

	if (periph_conn_count < CONFIG_BT_CTLR_SDC_PERIPHERAL_COUNT &&
	    (!ble_adv_active || (now - last_adv_watchdog_ms) >= APP_ADV_WATCHDOG_MS)) {
		last_adv_watchdog_ms = now;
		(void)start_advertising();
	}

	if (atomic_get(&sensor_disconnect_pending) != 0) {
		if ((now - last_sensor_disconnect_retry_ms) >= SENSOR_DISCONNECT_RETRY_MS) {
			struct bt_conn *conn = sensor_conn_ref_get();

			last_sensor_disconnect_retry_ms = now;
			if (conn != NULL) {
				int err = bt_conn_disconnect(
					conn, BT_HCI_ERR_REMOTE_USER_TERM_CONN);

				bt_conn_unref(conn);
				if (err != 0 && err != -EALREADY) {
					LOG_WRN("Retry XDS disconnect failed (%d)", err);
				}
			} else {
				atomic_clear(&sensor_disconnect_pending);
				atomic_clear(&bind_clear_pending);
			}
		}
		return;
	}

	if (sensor_conn_exists() || ble_connected_sensor) {
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
	uint16_t pwr;
	uint16_t cad;
	uint8_t err;
	uint8_t evt;
	bool ready;
	bool valid;

	k_mutex_lock(&data_lock, K_FOREVER);
	if (last_ble_data_ms != 0U) {
		age_ms = k_uptime_get_32() - last_ble_data_ms;
	}
	if (rx_avg_interval_ms > 0U) {
		hz_x10 = 10000U / rx_avg_interval_ms;
	}
	pwr = latest_power_w;
	cad = latest_cadence;
	err = latest_error_code;
	evt = pwr_event_count;
	ready = ble_sensor_ready;
	valid = latest_data_valid;
	k_mutex_unlock(&data_lock);

	/* 持锁期间不要 printf（UART 阻塞会拖慢 BLE 通知回调），先取快照再打印。 */
	printf("status: seen=%d ble_conn=%d ready=%d valid=%d ant_link=%d app=%d adv=%d scan=%d ble_out=%d/%d log=%d pwr=%u cad=%u err=%u evt=%u rate=%u.%uHz age=%ums\n",
	       ble_seen_sensor, ble_connected_sensor, ready, valid,
	       ant_linked_display, periph_conn_count, ble_adv_active, xds_scan_active,
	       cps_any_subscribed(), csc_any_subscribed(), serial_log_enabled,
	       (unsigned int)pwr, (unsigned int)cad, (unsigned int)err,
	       (unsigned int)evt, (unsigned int)(hz_x10 / 10U),
	       (unsigned int)(hz_x10 % 10U), (unsigned int)age_ms);
}

/**
 * @brief 清除本次上电的传感器绑定并断开当前 XDS，随后重新扫描。
 */
static void clear_sensor_binding(void)
{
	struct bt_conn *conn = NULL;
	int err = 0;

	atomic_set(&bind_clear_pending, 1);
	k_mutex_lock(&data_lock, K_FOREVER);
	validated_sensor_addr_valid = false;
	rejected_sensor_addr_valid = false;
	latest_data_valid = false;
	conn = sensor_conn_ref_get();
	k_mutex_unlock(&data_lock);
	atomic_set(&app_notify_pending, 1);

	if (conn != NULL) {
		atomic_set(&sensor_disconnect_pending, 1);
		err = bt_conn_disconnect(conn, BT_HCI_ERR_REMOTE_USER_TERM_CONN);
		bt_conn_unref(conn);
	}

	if (conn == NULL) {
		atomic_clear(&bind_clear_pending);
		atomic_clear(&sensor_disconnect_pending);
		(void)start_scan();
	} else if (err != 0 && err != -EALREADY) {
		LOG_WRN("XDS disconnect request failed (%d); retrying", err);
	}

	printf("sensor binding cleared%s\n", conn != NULL ? "; reconnecting" : "");
}

/**
 * @brief 处理串口命令入口。
 *
 * @param cmd 已解析完成的一行命令字符串。
 */
static void handle_command(const char *cmd)
{
	if (strcmp(cmd, "help") == 0) {
		printf("commands: help, status, scan, bind clear, log on/off\n");
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
	if (strcmp(cmd, "bind clear") == 0) {
		clear_sensor_binding();
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
	size_t bytes_read = 0U;

	if (!uart_console) {
		return;
	}

	while (bytes_read < UART_RX_BUDGET &&
	       uart_poll_in(uart_console, &c) == 0) {
		bytes_read++;
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

static bool xds_measurement_valid(uint16_t total_power, int16_t left_power,
				  int16_t right_power, uint8_t err_code)
{
	if (err_code != 0U || total_power > XDS_MAX_POWER_W) {
		return false;
	}

	if (left_power < -XDS_MAX_POWER_W || left_power > XDS_MAX_POWER_W ||
	    right_power < -XDS_MAX_POWER_W || right_power > XDS_MAX_POWER_W) {
		return false;
	}

	return true;
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
	uint16_t cadence_calc;
	uint8_t err_code;
	uint32_t now;
	bool valid;

	ARG_UNUSED(params);

	if (!data) {
		k_mutex_lock(&data_lock, K_FOREVER);
		ble_sensor_ready = false;
		latest_data_valid = false;
		k_mutex_unlock(&data_lock);
		atomic_set(&app_notify_pending, 1);
		LOG_WRN("XDS notification subscription was removed; reconnecting");
		if (conn != NULL) {
			(void)bt_conn_disconnect(conn, BT_HCI_ERR_REMOTE_USER_TERM_CONN);
		}
		return BT_GATT_ITER_STOP;
	}
	if (length < 11) {
		k_mutex_lock(&data_lock, K_FOREVER);
		latest_data_valid = false;
		latest_error_code = 0xFFU;
		last_ble_data_ms = k_uptime_get_32();
		k_mutex_unlock(&data_lock);
		atomic_set(&app_notify_pending, 1);
		LOG_WRN("Ignoring short XDS measurement (%u bytes)", (unsigned int)length);
		return BT_GATT_ITER_CONTINUE;
	}

	/* XDS custom fixed 11-byte format from ESP32 implementation. */
	total_power = sys_get_le16(raw + 0);
	left_power = (int16_t)sys_get_le16(raw + 2);
	right_power = (int16_t)sys_get_le16(raw + 4);
	/* cpp2026042201.ino: byte6 is signed cadence, reverse pedaling appears as negative. */
	raw_cadence_s8 = (int8_t)raw[6];
	err_code = raw[10];
	now = k_uptime_get_32();
	if (raw_cadence_s8 >= 0) {
		cadence_calc = (uint16_t)raw_cadence_s8;
	} else {
		/* XDS 协议定义 byte6 为有符号值；负值表示反踩，不得回退成高踏频。 */
		cadence_calc = 0U;
	}
	valid = xds_measurement_valid(total_power, left_power, right_power, err_code);

	k_mutex_lock(&data_lock, K_FOREVER);
	latest_power_w = total_power;
	latest_left_power_w = left_power;
	latest_right_power_w = right_power;
	latest_cadence = cadence_calc;
	latest_error_code = err_code;
	latest_data_valid = valid;
	last_ble_data_ms = now;
	if (last_rx_packet_ms != 0U) {
		uint32_t delta = now - last_rx_packet_ms;

		if (delta > 0U && delta < DATA_TIMEOUT_MS) {
			rx_avg_interval_ms = (rx_avg_interval_ms == 0U) ? delta :
					      ((rx_avg_interval_ms * 7U) + delta) / 8U;
		}
	}
	last_rx_packet_ms = now;
	if (valid) {
		const bt_addr_le_t *addr = bt_conn_get_dst(conn);

		/* 只有真实收到合理载荷后才完成本次上电的地址绑定。 */
		if (addr != NULL && atomic_get(&bind_clear_pending) == 0) {
			bt_addr_le_copy(&validated_sensor_addr, addr);
			validated_sensor_addr_valid = true;
			rejected_sensor_addr_valid = false;
		}
		/* ANT+ Page 16 累计的是每个功率更新事件的瞬时功率。 */
		accumulated_power = (uint16_t)(accumulated_power + total_power);
		pwr_event_count++;
	}
	k_mutex_unlock(&data_lock);

	atomic_set(&app_notify_pending, 1);
	atomic_set(&rx_log_pending, 1);
	if (!valid) {
		LOG_WRN("Rejected XDS measurement: P=%u L=%d R=%d err=%u",
			(unsigned int)total_power, left_power, right_power,
			(unsigned int)err_code);
	}
	return BT_GATT_ITER_CONTINUE;
}

static void reject_sensor_connection(struct bt_conn *conn, const char *reason)
{
	const bt_addr_le_t *addr = bt_conn_get_dst(conn);

	k_mutex_lock(&data_lock, K_FOREVER);
	if (addr != NULL) {
		bt_addr_le_copy(&rejected_sensor_addr, addr);
		rejected_sensor_addr_valid = true;
		rejected_sensor_at_ms = k_uptime_get_32();
	}
	ble_sensor_ready = false;
	latest_data_valid = false;
	k_mutex_unlock(&data_lock);
	atomic_set(&app_notify_pending, 1);
	LOG_WRN("Rejecting non-XDS/incomplete sensor connection: %s", reason);
	(void)bt_conn_disconnect(conn, BT_HCI_ERR_REMOTE_USER_TERM_CONN);
}

static void subscribe_func(struct bt_conn *conn, uint8_t err,
			   struct bt_gatt_subscribe_params *params)
{
	ARG_UNUSED(params);
	if (err) {
		LOG_ERR("CCCD subscribe write failed (ATT err 0x%02x)",
			(unsigned int)err);
		reject_sensor_connection(conn, "CCCD write failed");
	} else {
		k_mutex_lock(&data_lock, K_FOREVER);
		ble_sensor_ready = true;
		latest_data_valid = false;
		k_mutex_unlock(&data_lock);
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
		reject_sensor_connection(conn, "required GATT attribute not found");
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
			reject_sensor_connection(conn, "characteristic discovery failed");
		}
		return BT_GATT_ITER_STOP;
	}

	if (params->type == BT_GATT_DISCOVER_CHARACTERISTIC) {
		const struct bt_gatt_chrc *chrc = attr->user_data;

		if ((chrc->properties & BT_GATT_CHRC_NOTIFY) == 0U) {
			(void)memset(params, 0, sizeof(*params));
			reject_sensor_connection(conn, "measurement characteristic is not notifiable");
			return BT_GATT_ITER_STOP;
		}

		subscribe_params.value_handle = chrc->value_handle;
		discover_uuid.uuid.type = BT_UUID_TYPE_16;
		discover_uuid.val = BT_UUID_GATT_CCC_VAL;
		discover_params.uuid = &discover_uuid.uuid;
		discover_params.start_handle = chrc->value_handle + 1U;
		discover_params.end_handle = service_end_handle;
		discover_params.type = BT_GATT_DISCOVER_DESCRIPTOR;

		err = bt_gatt_discover(conn, &discover_params);
		if (err) {
			LOG_ERR("CCCD discover failed (%d)", err);
			reject_sensor_connection(conn, "CCCD discovery failed");
		}
		return BT_GATT_ITER_STOP;
	}

	if (params->type == BT_GATT_DISCOVER_DESCRIPTOR) {
		subscribe_params.notify = notify_func;
		subscribe_params.subscribe = subscribe_func;
		subscribe_params.value = BT_GATT_CCC_NOTIFY;
		subscribe_params.ccc_handle = attr->handle;
		atomic_set_bit(subscribe_params.flags, BT_GATT_SUBSCRIBE_FLAG_VOLATILE);

		LOG_INF("XDS measurement validated: value=0x%04x ccc=0x%04x",
			(unsigned int)subscribe_params.value_handle,
			(unsigned int)subscribe_params.ccc_handle);

		err = bt_gatt_subscribe(conn, &subscribe_params);
		if (err && err != -EALREADY) {
			LOG_ERR("Subscribe failed (%d)", err);
			reject_sensor_connection(conn, "subscription start failed");
		} else {
			LOG_INF("XDS subscription requested");
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

	if (sensor_conn_exists() || ble_connected_sensor) {
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

	if (periph_conn_count >= CONFIG_BT_CTLR_SDC_PERIPHERAL_COUNT) {
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
	uint32_t now = k_uptime_get_32();
	struct bt_conn_le_create_param create_param = BT_CONN_LE_CREATE_PARAM_INIT(
		BT_CONN_LE_OPT_NONE, BT_GAP_SCAN_FAST_INTERVAL, BT_GAP_SCAN_FAST_INTERVAL);
	struct bt_le_conn_param conn_param = BT_LE_CONN_PARAM_INIT(
		48, 72, 0, BT_GAP_MS_TO_CONN_TIMEOUT(XDS_CONN_TIMEOUT_MS));

	ARG_UNUSED(rssi);
	ARG_UNUSED(type);

	if (sensor_conn_exists() || !adv_has_xds_service(ad)) {
		return;
	}
	k_mutex_lock(&data_lock, K_FOREVER);
	if (validated_sensor_addr_valid &&
	    bt_addr_le_cmp(addr, &validated_sensor_addr) != 0) {
		k_mutex_unlock(&data_lock);
		return;
	}
	if (rejected_sensor_addr_valid &&
	    bt_addr_le_cmp(addr, &rejected_sensor_addr) == 0 &&
	    (now - rejected_sensor_at_ms) < XDS_REJECT_RETRY_MS) {
		k_mutex_unlock(&data_lock);
		return;
	}
	if (rejected_sensor_addr_valid &&
	    (now - rejected_sensor_at_ms) >= XDS_REJECT_RETRY_MS) {
		rejected_sensor_addr_valid = false;
	}
	k_mutex_unlock(&data_lock);

	ble_seen_sensor = true;

	err = stop_scan();
	if (err && err != -EALREADY) {
		return;
	}

	struct bt_conn *new_conn = NULL;

	err = bt_conn_le_create(addr, &create_param, &conn_param, &new_conn);
	if (err) {
		LOG_ERR("Create conn failed (%d)", err);
		(void)start_scan();
		return;
	}
	sensor_conn_store(new_conn);

	LOG_INF("Connecting to XDS meter (RSSI %d)...", rssi);
}

/**
 * @brief BLE 连接事件回调（中央/外设双角色共用）。
 */
static void connected(struct bt_conn *conn, uint8_t err)
{
	struct bt_conn_info info;

	if (err) {
		struct bt_conn *owned_conn;

		LOG_ERR("BLE connect failed (%u)", (unsigned int)err);
		/* 仅当失败的是中央侧（连 XDS）对象时，才清理 sensor_conn。 */
		owned_conn = sensor_conn_take_if(conn);
		if (owned_conn != NULL) {
			bt_conn_unref(owned_conn);
			ble_connected_sensor = false;
			k_mutex_lock(&data_lock, K_FOREVER);
			ble_sensor_ready = false;
			latest_data_valid = false;
			k_mutex_unlock(&data_lock);
			atomic_set(&app_notify_pending, 1);
			atomic_clear(&bind_clear_pending);
			atomic_clear(&sensor_disconnect_pending);
			(void)start_scan();
		} else {
			/* 外设侧连接失败时，确保仍可被后续 APP/手表发现。 */
			(void)start_advertising();
		}
		return;
	}

	if (bt_conn_get_info(conn, &info) != 0 || info.type != BT_CONN_TYPE_LE) {
		if (sensor_conn_matches(conn)) {
			int disconnect_err;

			LOG_ERR("Unable to identify XDS connection role; disconnecting");
			atomic_set(&sensor_disconnect_pending, 1);
			disconnect_err = bt_conn_disconnect(
				conn, BT_HCI_ERR_REMOTE_USER_TERM_CONN);
			if (disconnect_err != 0 && disconnect_err != -EALREADY) {
				/*
				 * 失败不等于连接已经消失。保留唯一引用并等待监督
				 * 超时/断开回调，避免同时建立第二条中央连接。
				 */
				LOG_ERR("XDS disconnect request failed (%d)",
					disconnect_err);
			}
		} else {
			(void)start_advertising();
		}
		return;
	}

	if (info.role == BT_CONN_ROLE_CENTRAL) {
		struct bt_le_conn_param xds_param =
			BT_LE_CONN_PARAM_INIT(48, 72, 0, BT_GAP_MS_TO_CONN_TIMEOUT(XDS_CONN_TIMEOUT_MS));
		int perr;

		xds_scan_active = false;
		ble_connected_sensor = true;
		k_mutex_lock(&data_lock, K_FOREVER);
		ble_sensor_ready = false;
		latest_data_valid = false;
		last_ble_data_ms = 0U;
		last_rx_packet_ms = 0U;
		k_mutex_unlock(&data_lock);
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

		perr = bt_gatt_discover(conn, &discover_params);
		if (perr) {
			LOG_ERR("Primary service discover failed (%d)", perr);
			reject_sensor_connection(conn, "primary service discovery failed");
		}
	} else {
		/* APP/watch connections use tighter parameters for outdoor stability. */
		struct bt_le_conn_param app_param =
			BT_LE_CONN_PARAM_INIT(APP_CONN_INTERVAL_MIN, APP_CONN_INTERVAL_MAX,
					      APP_CONN_LATENCY,
					      BT_GAP_MS_TO_CONN_TIMEOUT(APP_CONN_TIMEOUT_MS));
		int perr;

		periph_conn_count++;
		ble_adv_active = false;
		last_crank_update_ms = k_uptime_get_32();
		perr = bt_conn_le_param_update(conn, &app_param);
		if (perr && perr != -EALREADY) {
			LOG_WRN("BLE app conn param update failed (%d)", perr);
		}
		LOG_INF("BLE app/phone connected to local CPS");
		if (periph_conn_count < CONFIG_BT_CTLR_SDC_PERIPHERAL_COUNT) {
			/* Legacy connectable advertising stops after each connection; the main loop restarts it. */
			last_adv_watchdog_ms = 0U;
		}
	}
}

/**
 * @brief BLE 断开事件回调，负责重连扫描与外设广播恢复。
 */
static void disconnected(struct bt_conn *conn, uint8_t reason)
{
	struct bt_conn_info info;
	struct bt_conn *owned_conn;
	bool is_sensor_conn = sensor_conn_matches(conn);
	int info_err;

	LOG_WRN("BLE disconnected (reason 0x%02x)", (unsigned int)reason);
	info_err = bt_conn_get_info(conn, &info);
	if ((info_err != 0 || info.type != BT_CONN_TYPE_LE) && !is_sensor_conn) {
		return;
	}

	if (is_sensor_conn || (info_err == 0 && info.role == BT_CONN_ROLE_CENTRAL)) {
		ble_connected_sensor = false;
		k_mutex_lock(&data_lock, K_FOREVER);
		ble_sensor_ready = false;
		latest_data_valid = false;
		last_ble_data_ms = 0U;
		last_rx_packet_ms = 0U;
		k_mutex_unlock(&data_lock);
		atomic_set(&app_notify_pending, 1);
		owned_conn = sensor_conn_take_if(conn);
		if (owned_conn != NULL) {
			bt_conn_unref(owned_conn);
		}
		(void)memset(&subscribe_params, 0, sizeof(subscribe_params));
		atomic_clear(&bind_clear_pending);
		atomic_clear(&sensor_disconnect_pending);
		(void)start_scan();
	} else {
		/* 订阅状态由 Zephyr 按 per-connection 自动回收。 */
		if (periph_conn_count > 0U) {
			periph_conn_count--;
		}
		ble_adv_active = false;
		last_adv_watchdog_ms = 0U;
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
	bool response_ready = true;

	switch (p_page1->calibration_id) {
	case ANT_BPWR_CALIB_ID_MANUAL:
	case ANT_BPWR_CALIB_ID_AUTO:
	case ANT_BPWR_CALIB_ID_CUSTOM_REQ:
	case ANT_BPWR_CALIB_ID_CUSTOM_UPDATE:
		/*
		 * 桥接器无法把校准请求透传给 XDS。必须明确返回失败，
		 * 不能让码表误以为真实功率计已经完成校准。
		 */
		bpwr.BPWR_PROFILE_calibration_id = ANT_BPWR_CALIB_ID_FAILED;
		bpwr.BPWR_PROFILE_general_calib_data = 0;
		break;
	default:
		response_ready = false;
		break;
	}

	if (response_ready) {
		ant_bpwr_calib_response(p_profile);
	}
}

static void ant_evt_handler(ant_evt_t *p_ant_evt)
{
	ant_bpwr_sens_evt_handler(p_ant_evt, &bpwr);

	switch (p_ant_evt->event) {
	case EVENT_RX:
		ant_linked_display = true;
		last_ant_rx_ms = k_uptime_get_32();
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

static int watchdog_init(void)
{
	struct wdt_timeout_cfg timeout_cfg = {
		.window = {
			.min = 0U,
			.max = WDT_TIMEOUT_MS,
		},
		.callback = NULL,
		.flags = WDT_FLAG_RESET_SOC,
	};
	int err;

	if (!device_is_ready(wdt_dev)) {
		LOG_ERR("Watchdog device is not ready");
		return -ENODEV;
	}

	wdt_channel_id = wdt_install_timeout(wdt_dev, &timeout_cfg);
	if (wdt_channel_id < 0) {
		LOG_ERR("Watchdog timeout install failed (%d)", wdt_channel_id);
		return wdt_channel_id;
	}

	err = wdt_setup(wdt_dev, 0);
	if (err) {
		LOG_ERR("Watchdog setup failed (%d)", err);
		wdt_channel_id = -1;
		return err;
	}

	return 0;
}

static void fatal_reboot(const char *stage, int err)
{
	LOG_ERR("Fatal initialization failure at %s (%d); rebooting", stage, err);
	if (leds_initialized) {
		set_leds(true, false, true);
	}
	k_sleep(K_MSEC(FATAL_REBOOT_DELAY_MS));
	sys_reboot(SYS_REBOOT_COLD);

	CODE_UNREACHABLE;
}

/**
 * @brief 更新三颗 LED 状态指示。
 *
 * LED0: 未发现 XDS 时慢闪，发现后常亮。
 * LED1: 无近期 ANT 接收活动时慢闪，有活动后常亮；10 秒无消息后恢复慢闪。
 * LED2: 手机/手表连接本机 BLE 时常亮，无连接时慢闪。
 */
static void update_led_pattern(void)
{
	uint32_t now = k_uptime_get_32();
	bool slow_on = ((now / SLOW_BLINK_HALF_MS) & 0x1U) == 0U;

	if (ant_linked_display &&
	    (now - last_ant_rx_ms) >= ANT_DISPLAY_ACTIVITY_TIMEOUT_MS) {
		ant_linked_display = false;
	}

	set_leds(ble_seen_sensor ? true : slow_on,
		 ant_linked_display ? true : slow_on,
		 periph_conn_count > 0U ? true : slow_on);
}

/**
 * @brief 将最新 BLE 数据映射到 ANT BPWR 发送结构。
 *
 * 包括功率、踏频与左右平衡字段，供码表通过 ANT+ 读取。
 */
/**
 * @brief 将最新 BLE 数据映射到 ANT BPWR 页面字段。
 *
 * 注意：事件计数(pwr_event_count)只在真正收到新 XDS 包时(notify_func)递增，
 * 此 tick 刷新不再虚构新事件，否则累计功率不增而事件计数涨，码表用
 * Δacc/Δevent 推算功率会读到 0/偏低。
 */
static void update_ant_from_latest_data(void)
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
	unsigned int irq_key;

	k_mutex_lock(&data_lock, K_FOREVER);
	use_live_data = ble_sensor_ready && latest_data_valid &&
			((now - last_ble_data_ms) < DATA_TIMEOUT_MS);
	pwr = use_live_data ? latest_power_w : 0U;
	cad = use_live_data ? latest_cadence : 0U;
	left_w = use_live_data ? latest_left_power_w : 0;
	right_w = use_live_data ? latest_right_power_w : 0;
	evt = pwr_event_count;
	acc = accumulated_power;
	k_mutex_unlock(&data_lock);

	/* ANT 事件可异步读取 profile；短临界区保证整页字段来自同一快照。 */
	irq_key = irq_lock();
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
	irq_unlock(irq_key);
}

/**
 * @brief 程序主入口：初始化 ANT/BLE 并执行桥接主循环。
 */
int main(void)
{
	int err;

	k_mutex_init(&data_lock);
	uart_console = DEVICE_DT_GET(DT_CHOSEN(zephyr_console));

	err = leds_init();
	if (err) {
		fatal_reboot("LED", err);
	}
	leds_initialized = true;

	err = watchdog_init();
	if (err) {
		fatal_reboot("watchdog", err);
	}

	err = ant_stack_setup();
	if (err) {
		fatal_reboot("ANT stack", err);
	}

	err = profile_setup();
	if (err) {
		fatal_reboot("ANT profile", err);
	}

	err = bt_enable(NULL);
	if (err) {
		LOG_ERR("Bluetooth init failed (%d)", err);
		fatal_reboot("Bluetooth", err);
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
		log_rx_if_due();
		update_led_pattern();
		err = wdt_feed(wdt_dev, wdt_channel_id);
		if (err) {
			LOG_ERR("Watchdog feed failed (%d)", err);
		}
		k_sleep(K_MSEC(MAIN_LOOP_MS));
	}

	
}
