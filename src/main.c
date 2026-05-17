/*
 * XDS BLE -> ANT+ BPWR bridge
 */

#include <stdio.h>
#include <limits.h>
#include <string.h>

#include <zephyr/bluetooth/bluetooth.h>
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

LOG_MODULE_REGISTER(xds_ant_bridge, LOG_LEVEL_INF);

#define DATA_TIMEOUT_MS 5000
#define SLOW_BLINK_HALF_MS 250
#define FAST_BLINK_HALF_MS 100
#define DATA_FLASH_WINDOW_MS 350
#define CADENCE_STALE_MS 900
#define CADENCE_MAX_RPM 220
#define CADENCE_MIN_STEP_DEG 2
#define CADENCE_MAX_STEP_DEG 120
#define CADENCE_COMP_X10 18
#define APP_NOTIFY_INTERVAL_MS 200

#define XDS_SERVICE_UUID_16 0x1828
#define XDS_MEAS_UUID_16 0x2A63

#define LED0_NODE DT_ALIAS(led0)
#define LED1_NODE DT_ALIAS(led1)
#define LED2_NODE DT_ALIAS(led2)

#define CMD_BUF_LEN 64
#define CMD_IDLE_EXEC_MS 1200

static const struct gpio_dt_spec led0 = GPIO_DT_SPEC_GET(LED0_NODE, gpios);
static const struct gpio_dt_spec led1 = GPIO_DT_SPEC_GET(LED1_NODE, gpios);
static const struct gpio_dt_spec led2 = GPIO_DT_SPEC_GET(LED2_NODE, gpios);

static const struct device *uart_console;
static char cmd_buf[CMD_BUF_LEN];
static size_t cmd_len;
static uint32_t cmd_last_rx_ms;

static struct bt_conn *sensor_conn;
static struct bt_gatt_discover_params discover_params;
static struct bt_gatt_subscribe_params subscribe_params;
static struct bt_uuid_16 discover_uuid;
static uint16_t service_start_handle;
static uint16_t service_end_handle;

static struct k_mutex data_lock;
static uint16_t latest_power_w;
static int16_t latest_left_power_w;
static int16_t latest_right_power_w;
static uint16_t latest_cadence;
static uint8_t latest_error_code;
static uint32_t last_ble_data_ms;
static uint32_t last_data_change_ms;
static uint32_t last_rx_packet_ms;
static uint32_t rx_avg_interval_ms;
static uint8_t pwr_event_count;
static uint16_t accumulated_power;
static bool cps_notify_enabled;
static bool csc_notify_enabled;
static bool cadence_state_valid;
static uint16_t cadence_prev_angle_deg;
static uint32_t cadence_prev_ms;
static uint16_t cadence_est_rpm;
static uint32_t cadence_last_motion_ms;
static uint16_t cadence_cfg_stale_ms = CADENCE_STALE_MS;
static uint16_t cadence_cfg_min_step_deg = CADENCE_MIN_STEP_DEG;
static uint16_t cadence_cfg_max_step_deg = CADENCE_MAX_STEP_DEG;
static uint16_t cadence_cfg_comp_x10 = CADENCE_COMP_X10;

static bool ble_seen_sensor;
static bool ble_connected_sensor;
static bool ble_periph_connected;
static bool ant_linked_display;
static uint32_t cumulative_crank_revs;
static uint16_t last_crank_event_time_1024;
static uint32_t last_crank_update_ms;
static uint32_t last_app_notify_ms;
static uint32_t last_app_log_ms;

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
static ssize_t read_cps_measurement(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				    void *buf, uint16_t len, uint16_t offset);
static ssize_t read_cps_feature(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				void *buf, uint16_t len, uint16_t offset);
static ssize_t read_csc_measurement(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				    void *buf, uint16_t len, uint16_t offset);
static ssize_t read_csc_feature(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				void *buf, uint16_t len, uint16_t offset);

BT_GATT_SERVICE_DEFINE(cps_svc,
	BT_GATT_PRIMARY_SERVICE(BT_UUID_CPS),
	BT_GATT_CHARACTERISTIC(BT_UUID_GATT_CPS_CPM, BT_GATT_CHRC_READ | BT_GATT_CHRC_NOTIFY,
			       BT_GATT_PERM_READ, read_cps_measurement, NULL, NULL),
	BT_GATT_CCC(cps_ccc_cfg_changed, BT_GATT_PERM_READ | BT_GATT_PERM_WRITE),
	BT_GATT_CHARACTERISTIC(BT_UUID_GATT_CPS_CPF, BT_GATT_CHRC_READ,
			       BT_GATT_PERM_READ, read_cps_feature, NULL, NULL));

BT_GATT_SERVICE_DEFINE(csc_svc,
	BT_GATT_PRIMARY_SERVICE(BT_UUID_CSC),
	BT_GATT_CHARACTERISTIC(BT_UUID_CSC_MEASUREMENT, BT_GATT_CHRC_READ | BT_GATT_CHRC_NOTIFY,
			       BT_GATT_PERM_READ, read_csc_measurement, NULL, NULL),
	BT_GATT_CCC(csc_ccc_cfg_changed, BT_GATT_PERM_READ | BT_GATT_PERM_WRITE),
	BT_GATT_CHARACTERISTIC(BT_UUID_CSC_FEATURE, BT_GATT_CHRC_READ,
			       BT_GATT_PERM_READ, read_csc_feature, NULL, NULL));

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

static size_t build_csc_measurement(uint16_t cadence_rpm, uint8_t out[5])
{
	uint32_t now = k_uptime_get_32();

	update_crank_metrics(cadence_rpm, now);
	out[0] = BIT(1); /* Crank data present. */
	sys_put_le16((uint16_t)cumulative_crank_revs, out + 1);
	sys_put_le16(last_crank_event_time_1024, out + 3);
	return 5U;
}

static uint16_t __unused cadence_from_angle(uint16_t crank_angle_deg, uint32_t now_ms)
{
	uint32_t dt_ms;
	uint16_t delta_cw;
	uint16_t delta_ccw;
	uint16_t delta_deg;
	uint32_t rpm_instant;
	uint32_t rpm_comp;

	if (!cadence_state_valid) {
		cadence_state_valid = true;
		cadence_prev_angle_deg = crank_angle_deg;
		cadence_prev_ms = now_ms;
		cadence_est_rpm = 0U;
		cadence_last_motion_ms = now_ms;
		return 0U;
	}

	dt_ms = now_ms - cadence_prev_ms;
	if (dt_ms == 0U || dt_ms > DATA_TIMEOUT_MS) {
		cadence_prev_angle_deg = crank_angle_deg;
		cadence_prev_ms = now_ms;
		cadence_est_rpm = 0U;
		cadence_last_motion_ms = now_ms;
		return 0U;
	}

	delta_cw = (uint16_t)((crank_angle_deg + 360U - cadence_prev_angle_deg) % 360U);
	delta_ccw = (uint16_t)((cadence_prev_angle_deg + 360U - crank_angle_deg) % 360U);
	/* Use shortest angular travel magnitude, so occasional reverse pedaling is handled. */
	delta_deg = MIN(delta_cw, delta_ccw);
	cadence_prev_angle_deg = crank_angle_deg;
	cadence_prev_ms = now_ms;

	/* Treat implausible jump as no movement. */
	if (delta_deg > cadence_cfg_max_step_deg) {
		delta_deg = 0U;
	}

	if (delta_deg >= cadence_cfg_min_step_deg) {
		cadence_last_motion_ms = now_ms;
	}

	if ((now_ms - cadence_last_motion_ms) > cadence_cfg_stale_ms) {
		cadence_est_rpm = 0U;
		return 0U;
	}

	if (delta_deg < cadence_cfg_min_step_deg) {
		return cadence_est_rpm;
	}

	/* 1Hz source: use per-packet estimate and apply cadence-only compensation. */
	rpm_instant = ((uint32_t)delta_deg * 60000U) / (360U * dt_ms);
	rpm_comp = (rpm_instant * cadence_cfg_comp_x10 + 5U) / 10U;
	if (rpm_comp > CADENCE_MAX_RPM) {
		rpm_comp = CADENCE_MAX_RPM;
	}

	/* Moderate smoothing: keep response while reducing packet jitter. */
	cadence_est_rpm = (cadence_est_rpm == 0U) ? (uint16_t)rpm_comp :
			  (uint16_t)((cadence_est_rpm + rpm_comp * 2U) / 3U);
	return cadence_est_rpm;
}

static void print_cadence_cfg(void)
{
	printf("cad cfg: gain=%u.%u min_step=%u max_step=%u stale=%ums\n",
	       cadence_cfg_comp_x10 / 10U, cadence_cfg_comp_x10 % 10U,
	       cadence_cfg_min_step_deg, cadence_cfg_max_step_deg, cadence_cfg_stale_ms);
}

static ssize_t read_cps_measurement(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				    void *buf, uint16_t len, uint16_t offset)
{
	uint8_t cpm[8];
	uint16_t pwr;
	uint16_t cad;
	size_t cpm_len;

	k_mutex_lock(&data_lock, K_FOREVER);
	pwr = latest_power_w;
	cad = latest_cadence;
	k_mutex_unlock(&data_lock);

	cpm_len = build_cps_measurement(pwr, cad, cpm);
	return bt_gatt_attr_read(conn, attr, buf, len, offset, cpm, cpm_len);
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

static ssize_t read_csc_measurement(struct bt_conn *conn, const struct bt_gatt_attr *attr,
				    void *buf, uint16_t len, uint16_t offset)
{
	uint8_t csc[5];
	uint16_t cad;
	size_t csc_len;

	k_mutex_lock(&data_lock, K_FOREVER);
	cad = latest_cadence;
	k_mutex_unlock(&data_lock);

	csc_len = build_csc_measurement(cad, csc);
	return bt_gatt_attr_read(conn, attr, buf, len, offset, csc, csc_len);
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

static void notify_ble_apps_if_due(void)
{
	uint8_t cpm[8];
	uint8_t csc[5];
	uint16_t pwr;
	uint16_t cad;
	uint32_t now = k_uptime_get_32();
	size_t cpm_len;
	size_t csc_len;
	bool any_notified = false;

	if (!cps_notify_enabled && !csc_notify_enabled) {
		return;
	}

	if ((now - last_app_notify_ms) < APP_NOTIFY_INTERVAL_MS) {
		return;
	}
	last_app_notify_ms = now;

	k_mutex_lock(&data_lock, K_FOREVER);
	pwr = latest_power_w;
	cad = latest_cadence;
	k_mutex_unlock(&data_lock);

	if (cps_notify_enabled) {
		cpm_len = build_cps_measurement(pwr, cad, cpm);
		(void)bt_gatt_notify(NULL, &cps_svc.attrs[2], cpm, cpm_len);
		any_notified = true;
	}

	if (csc_notify_enabled) {
		csc_len = build_csc_measurement(cad, csc);
		(void)bt_gatt_notify(NULL, &csc_svc.attrs[2], csc, csc_len);
		any_notified = true;
	}

	if (any_notified && (now - last_app_log_ms) >= 1000U) {
		printf("APP TX P=%uW C=%urpm rev=%lu t=%u\n",
		       pwr, cad, (unsigned long)cumulative_crank_revs, last_crank_event_time_1024);
		last_app_log_ms = now;
	}
}

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
	printf("status: seen=%d ble_conn=%d ant_link=%d ble_out=%d/%d pwr=%u cad=%u err=%u evt=%u rate=%u.%uHz age=%ums\n",
	       ble_seen_sensor, ble_connected_sensor, ant_linked_display,
	       cps_notify_enabled, csc_notify_enabled, latest_power_w, latest_cadence, latest_error_code,
	       pwr_event_count, hz_x10 / 10U, hz_x10 % 10U, age_ms);
	k_mutex_unlock(&data_lock);
}

static void handle_command(const char *cmd)
{
	char key[16];
	unsigned int value;
	int n;

	n = sscanf(cmd, "%15s %u", key, &value);
	if (n < 1) {
		return;
	}

	if (strcmp(key, "help") == 0) {
		printf("commands: help, status, scan, cad_show, cad_gain <x10>, cad_min <deg>, cad_max <deg>, cad_stale <ms>\n");
		return;
	}
	if (strcmp(key, "status") == 0) {
		print_status();
		return;
	}
	if (strcmp(key, "scan") == 0) {
		(void)bt_le_scan_stop();
		(void)bt_le_scan_start(BT_LE_SCAN_ACTIVE, device_found);
		printf("scan restart requested\n");
		return;
	}
	/* Serial tool occasionally truncates the last char; accept both forms. */
	if (strcmp(key, "cad_show") == 0 || strcmp(key, "cad_sho") == 0) {
		print_cadence_cfg();
		return;
	}
	if (strcmp(key, "cad_gain") == 0 || strcmp(key, "cad_gai") == 0) {
		if (n != 2) {
			/* Fallback for serial links that lose the numeric suffix. */
			cadence_cfg_comp_x10 = 30U;
			printf("cad_gain fallback -> 30 (3.0x)\n");
			print_cadence_cfg();
			return;
		}
		if (value < 5U || value > 40U) {
			printf("cad_gain range: 5..40 (0.5x..4.0x)\n");
			return;
		}
		cadence_cfg_comp_x10 = (uint16_t)value;
		print_cadence_cfg();
		return;
	}
	if (strcmp(key, "cad_min") == 0 || strcmp(key, "cad_mi") == 0) {
		if (n != 2) {
			cadence_cfg_min_step_deg = 1U;
			printf("cad_min fallback -> 1 deg\n");
			print_cadence_cfg();
			return;
		}
		if (value < 1U || value > 30U) {
			printf("cad_min range: 1..30 deg\n");
			return;
		}
		cadence_cfg_min_step_deg = (uint16_t)value;
		print_cadence_cfg();
		return;
	}
	if (strcmp(key, "cad_max") == 0 || strcmp(key, "cad_ma") == 0) {
		if (n != 2) {
			cadence_cfg_max_step_deg = 180U;
			printf("cad_max fallback -> 180 deg\n");
			print_cadence_cfg();
			return;
		}
		if (value < 20U || value > 180U) {
			printf("cad_max range: 20..180 deg\n");
			return;
		}
		cadence_cfg_max_step_deg = (uint16_t)value;
		print_cadence_cfg();
		return;
	}
	if (strcmp(key, "cad_stale") == 0 || strcmp(key, "cad_stal") == 0 ||
	    strcmp(key, "cad_sta") == 0) {
		if (n != 2) {
			cadence_cfg_stale_ms = 2500U;
			printf("cad_stale fallback -> 2500 ms\n");
			print_cadence_cfg();
			return;
		}
		if (value < 300U || value > 5000U) {
			printf("cad_stale range: 300..5000 ms\n");
			return;
		}
		cadence_cfg_stale_ms = (uint16_t)value;
		print_cadence_cfg();
		return;
	}
	printf("unknown command: %s\n", cmd);
}

static void execute_pending_command(void)
{
	if (cmd_len == 0U) {
		return;
	}

	cmd_buf[cmd_len] = '\0';
	handle_command(cmd_buf);
	cmd_len = 0U;
}

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

static uint8_t notify_func(struct bt_conn *conn, struct bt_gatt_subscribe_params *params,
			   const void *data, uint16_t length)
{
	const uint8_t *raw = data;
	uint16_t total_power;
	int16_t left_power;
	int16_t right_power;
	int8_t raw_cadence_s8;
	uint16_t angle_deg;
	uint16_t crank_angle_deg;
	uint16_t cadence_calc;
	uint8_t err_code;
	bool changed;
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
	angle_deg = (uint16_t)(sys_get_le16(raw + 6) % 360U);
	crank_angle_deg = (uint16_t)(sys_get_le16(raw + 8) % 360U);
	err_code = raw[10];
	now = k_uptime_get_32();
	if (raw_cadence_s8 >= 0 && raw_cadence_s8 <= 200) {
		cadence_calc = (uint16_t)raw_cadence_s8;
	} else {
		cadence_calc = 0U;
	}

	k_mutex_lock(&data_lock, K_FOREVER);
	changed = (total_power != latest_power_w) || (cadence_calc != latest_cadence);
	latest_power_w = total_power;
	latest_left_power_w = left_power;
	latest_right_power_w = right_power;
	latest_cadence = cadence_calc;
	latest_error_code = err_code;
	last_ble_data_ms = now;
	if (last_rx_packet_ms != 0U) {
		uint32_t delta = now - last_rx_packet_ms;

		if (delta > 0U && delta < DATA_TIMEOUT_MS) {
			rx_avg_interval_ms = (rx_avg_interval_ms == 0U) ? delta :
					      ((rx_avg_interval_ms * 7U) + delta) / 8U;
		}
	}
	last_rx_packet_ms = now;
	if (changed) {
		last_data_change_ms = last_ble_data_ms;
	}
	pwr_event_count++;
	accumulated_power = (uint16_t)(accumulated_power + total_power);
	k_mutex_unlock(&data_lock);

	printf("RX P=%uW C=%urpm E=%u (L=%d R=%d A=%u CA=%u)\n",
	       total_power, cadence_calc, err_code, left_power, right_power, angle_deg, crank_angle_deg);
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

static int start_scan(void)
{
	int err;
	struct bt_le_scan_param param = {
		.type = BT_LE_SCAN_TYPE_ACTIVE,
		.options = BT_LE_SCAN_OPT_NONE,
		.interval = BT_GAP_SCAN_FAST_INTERVAL,
		.window = BT_GAP_SCAN_FAST_WINDOW / 2,
	};

	err = bt_le_scan_start(&param, device_found);
	if (err == -EALREADY) {
		return 0;
	}
	if (err) {
		LOG_ERR("Scan start failed (%d)", err);
		return err;
	}

	LOG_INF("BLE scanning for XDS service (0x1828)");
	return 0;
}

static int start_advertising(void)
{
	int err;
	const struct bt_data ad[] = {
		BT_DATA_BYTES(BT_DATA_FLAGS, (BT_LE_AD_GENERAL | BT_LE_AD_NO_BREDR)),
		BT_DATA(BT_DATA_NAME_COMPLETE, CONFIG_BT_DEVICE_NAME,
			sizeof(CONFIG_BT_DEVICE_NAME) - 1),
		BT_DATA_BYTES(BT_DATA_UUID16_ALL, 0x18, 0x18, 0x16, 0x18),
	};

	err = bt_le_adv_start(BT_LE_ADV_CONN_FAST_1, ad, ARRAY_SIZE(ad), NULL, 0);
	if (err == -EALREADY) {
		return 0;
	}
	if (err) {
		LOG_ERR("Adv start failed (%d)", err);
		return err;
	}

	LOG_INF("BLE peripheral advertising started (CPS+CSCS)");
	return 0;
}

static void device_found(const bt_addr_le_t *addr, int8_t rssi, uint8_t type,
			 struct net_buf_simple *ad)
{
	int err;
	struct bt_conn_le_create_param create_param = BT_CONN_LE_CREATE_PARAM_INIT(
		BT_CONN_LE_OPT_NONE, BT_GAP_SCAN_FAST_INTERVAL, BT_GAP_SCAN_FAST_INTERVAL);
	struct bt_le_conn_param conn_param = BT_LE_CONN_PARAM_INIT(
		BT_GAP_INIT_CONN_INT_MIN, BT_GAP_INIT_CONN_INT_MAX, 0, BT_GAP_MS_TO_CONN_TIMEOUT(4000));

	ARG_UNUSED(rssi);
	ARG_UNUSED(type);

	if (sensor_conn || !adv_has_xds_service(ad)) {
		return;
	}

	ble_seen_sensor = true;

	err = bt_le_scan_stop();
	if (err && err != -EALREADY) {
		LOG_ERR("Stop scan failed (%d)", err);
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

static void connected(struct bt_conn *conn, uint8_t err)
{
	struct bt_conn_info info;

	if (err) {
		LOG_ERR("BLE connect failed (%u)", err);
		if (sensor_conn) {
			bt_conn_unref(sensor_conn);
			sensor_conn = NULL;
		}
		ble_connected_sensor = false;
		(void)start_scan();
		return;
	}

	if (bt_conn_get_info(conn, &info) != 0 || info.type != BT_CONN_TYPE_LE) {
		return;
	}

	if (info.role == BT_CONN_ROLE_CENTRAL) {
		ble_connected_sensor = true;
		LOG_INF("BLE connected to XDS");

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
		ble_periph_connected = true;
		last_crank_update_ms = k_uptime_get_32();
		LOG_INF("BLE app/phone connected to local CPS");
	}
}

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

	k_mutex_lock(&data_lock, K_FOREVER);
	use_live_data = ble_connected_sensor && ((now - last_ble_data_ms) < DATA_TIMEOUT_MS);
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
	printf("Type 'help' for commands.\n");

	while (1) {
		poll_uart_commands();
		notify_ble_apps_if_due();
		update_ant_from_latest_data();
		update_led_pattern();
		k_sleep(K_MSEC(50));
	}

	
}
