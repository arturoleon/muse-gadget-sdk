/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * Muse chat turns on boards without PSRAM (CONFIG_MUSE_HATCH=n). There's no room
 * for a second TLS and Noise connection or for MP3 decoding, so turns ride
 * Home Link's own session (muse_link_req_*) and replies are text only:
 * A live POST /chat/subscribe receives NDJSON replies while POST /chat/stream
 * uploads the note. Both use the existing device token and Link connection.
 * Lines are parsed without cJSON; bounded buffers keep internal RAM use small.
 */
#include "muse_chat.h"
#include "muse_chat_priv.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "cJSON.h"
#include "esp_log.h"
#include "esp_random.h"
#include "esp_timer.h"
#include "freertos/FreeRTOS.h"
#include "freertos/queue.h"
#include "freertos/semphr.h"
#include "freertos/task.h"

#include "muse_link.h"
#include "muse_wifi.h"

static const char *TAG = "muse_chat_link";

#define MIC_RATE 16000
#define STAGE_BYTES 1536                /* PCM per body chunk: 2 KB of base64, 48 ms */
#define CHUNK_BYTES (STAGE_BYTES / 3 * 4)
#define ACK_MAX 2048
#define TEXT_MAX 1024                   /* reply text kept for the captions */
#define EV_TEXT 72
#define SEND_WAIT_MS 200               /* the press queues the pre-roll all at once */
#define SETTLE_US 3000000               /* quiet after a reply before the turn ends */
#define REPLY_TIMEOUT_US 60000000
#define READ_CHARS_PER_S 14             /* caption scroll, about speaking pace */


/* A reply being received on Link's session task, read by the voice task once done. */
typedef struct {
    uint32_t gen;       /* bumped per request; frames of older ones are dropped */
    int status;         /* HTTP status, -1 if the request died */
    bool done;
    bool overflow;
    size_t len;
    size_t cap;         /* fixed note ACK buffer; 0: incremental subscription parser */
    char *body;
} rx_t;

/* A subscription event, decoded without allocating a JSON tree. */
typedef struct {
    char type[16];
    bool ready;         /* display_text_ready */
    uint64_t seq;
    char event[24];
    char msg[80];
    char reply_to[80];
    char text[TEXT_MAX];
} row_t;

enum { RX_NOTE, RX_SUB, RX_COUNT };

typedef enum { T_IDLE, T_TALKING, T_ACK, T_REPLY } phase_t;

typedef struct {
    char text[EV_TEXT];
    muse_hatch_ev_t type;
} ev_t;

static SemaphoreHandle_t s_rx_lock;
static rx_t s_rx[RX_COUNT];
static int64_t s_stream[RX_COUNT];      /* open request per slot, 0 none */
static QueueHandle_t s_events;
/* Subscription callback state, always under s_rx_lock. Keep the two newest
 * completed messages until the voice task drains them, including before ACK. */
static row_t s_row, s_delta, s_pending[2];
static unsigned s_pending_count;
static uint64_t s_last_seq;
static bool s_early_evicted;
static char s_note_id[80], s_parent_id[80]; /* ACK IDs shared under s_rx_lock */

/* Voice task only. */
static struct {
    phase_t phase;
    uint8_t *stage;                     /* PCM waiting for the next chunk */
    size_t stage_len;
    char *chunk;
    char note_id[80], parent_id[80], seen[2][80];
    unsigned seen_count;
    int64_t t_end, t_reply, t_show;
    bool replied;
    char error[EV_TEXT];                /* why the turn failed, repeated at the release */
    char text[TEXT_MAX];
    char shown[EV_TEXT];
} s_turn;

/* ---- Incremental NDJSON events ---- */

/* Parse selected fields as bytes arrive, without retaining the NDJSON line.
 * Large text/metadata values therefore cannot hide the final-message marker.
 * Unknown objects are traversed with bounded depth; strings are UTF-8 clipped. */
enum { J_KEY, J_COLON, J_VALUE, J_COMMA };
enum {
    F_SKIP, F_TYPE, F_EVENT, F_SEQ, F_PAYLOAD, F_ID, F_ID_ALT,
    F_PARENT, F_PARENT_ALT, F_TEXT, F_CONTENT, F_DELTA, F_READY,
};
typedef struct {
    uint8_t state, field, context;
    bool object;
} json_frame_t;
static struct {
    json_frame_t stack[32];
    unsigned depth;
    bool started, complete, bad, string, key, escape, scalar, clipped;
    unsigned unicode, digits, high, utf8_len, utf8_need;
    unsigned text_priority, id_priority, parent_priority;
    char utf8[4], key_text[24], literal[24];
    char *out;
    size_t len, cap;
    uint8_t field;
} s_json;

static void parser_reset(void)
{
    memset(&s_json, 0, sizeof(s_json));
    memset(&s_row, 0, sizeof(s_row));
    s_row.ready = true;
}

static void string_put(const char *p, size_t n)
{
    if (!s_json.out || s_json.clipped) return;
    if (s_json.len + n >= s_json.cap) {
        s_json.clipped = true;
        return;
    }
    memcpy(s_json.out + s_json.len, p, n);
    s_json.len += n;
    s_json.out[s_json.len] = 0;
}

static void codepoint_put(unsigned c)
{
    char out[4];
    size_t n;
    if (c < 0x80) { out[0] = c; n = 1; }
    else if (c < 0x800) { out[0] = 0xc0 | (c >> 6); out[1] = 0x80 | (c & 63); n = 2; }
    else if (c < 0x10000) {
        out[0] = 0xe0 | (c >> 12); out[1] = 0x80 | (c >> 6 & 63); out[2] = 0x80 | (c & 63); n = 3;
    } else {
        out[0] = 0xf0 | (c >> 18); out[1] = 0x80 | (c >> 12 & 63);
        out[2] = 0x80 | (c >> 6 & 63); out[3] = 0x80 | (c & 63); n = 4;
    }
    string_put(out, n);
}

static uint8_t field_for(const char *key, unsigned context)
{
    if (!context) return F_SKIP;
    if (context == 1) {
        if (!strcmp(key, "type")) return F_TYPE;
        if (!strcmp(key, "event")) return F_EVENT;
        if (!strcmp(key, "seq")) return F_SEQ;
        if (!strcmp(key, "payload")) return F_PAYLOAD;
    }
    if (!strcmp(key, "message_id")) return F_ID;
    if (!strcmp(key, "id")) return F_ID_ALT;
    if (!strcmp(key, "reply_to_message_id")) return F_PARENT;
    if (!strcmp(key, "parent_message_id")) return F_PARENT_ALT;
    if (!strcmp(key, "display_text")) return F_TEXT;
    if (!strcmp(key, "content")) return F_CONTENT;
    if (!strcmp(key, "text")) return F_DELTA;
    if (!strcmp(key, "display_text_ready")) return F_READY;
    return F_SKIP;
}

static void string_begin(bool key, unsigned field)
{
    s_json.string = true;
    s_json.key = key;
    s_json.field = field;
    s_json.escape = s_json.clipped = false;
    s_json.digits = s_json.high = s_json.utf8_len = s_json.utf8_need = 0;
    s_json.len = 0;
    s_json.out = NULL;
    s_json.cap = 0;
    if (key) { s_json.out = s_json.key_text; s_json.cap = sizeof(s_json.key_text); }
    else {
        unsigned *priority = NULL, rank = 0;
        if (field == F_ID || field == F_ID_ALT) { priority = &s_json.id_priority; rank = field == F_ID ? 2 : 1; }
        if (field == F_PARENT || field == F_PARENT_ALT) { priority = &s_json.parent_priority; rank = field == F_PARENT ? 2 : 1; }
        if (field == F_TEXT || field == F_CONTENT || field == F_DELTA) {
            priority = &s_json.text_priority; rank = field == F_TEXT ? 3 : field == F_CONTENT ? 2 : 1;
        }
        if (priority && s_json.stack[s_json.depth - 1].context == 2) rank += 4;
        if (priority && rank < *priority) field = F_SKIP;
        else if (priority) *priority = rank;
        switch (field) {
        case F_TYPE: s_json.out = s_row.type; s_json.cap = sizeof(s_row.type); break;
        case F_EVENT: s_json.out = s_row.event; s_json.cap = sizeof(s_row.event); break;
        case F_ID: case F_ID_ALT: s_json.out = s_row.msg; s_json.cap = sizeof(s_row.msg); break;
        case F_PARENT: case F_PARENT_ALT: s_json.out = s_row.reply_to; s_json.cap = sizeof(s_row.reply_to); break;
        case F_TEXT: case F_CONTENT: case F_DELTA: s_json.out = s_row.text; s_json.cap = sizeof(s_row.text); break;
        default: break;
        }
    }
    if (s_json.out) s_json.out[0] = 0;
}

static void string_byte(unsigned char c)
{
    if (s_json.digits) {
        unsigned hex = c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10
                     : c >= 'A' && c <= 'F' ? c - 'A' + 10 : 16;
        if (hex == 16) { s_json.bad = true; return; }
        s_json.unicode = s_json.unicode * 16 + hex;
        if (--s_json.digits) return;
        unsigned cp = s_json.unicode;
        if (s_json.high) {
            if (cp < 0xdc00 || cp > 0xdfff) { s_json.bad = true; return; }
            cp = 0x10000 + ((s_json.high - 0xd800) << 10) + cp - 0xdc00;
            s_json.high = 0;
        } else if (cp >= 0xd800 && cp <= 0xdbff) { s_json.high = cp; return; }
        else if (cp >= 0xdc00 && cp <= 0xdfff) { s_json.bad = true; return; }
        /* Captions are C strings; render embedded NUL as a space. */
        codepoint_put(cp ? cp : ' ');
        return;
    }
    if (s_json.escape) {
        s_json.escape = false;
        if (c == 'u') { s_json.digits = 4; s_json.unicode = 0; return; }
        if (s_json.high) { s_json.bad = true; return; }
        switch (c) {
        case 'n': c = '\n'; break;
        case 't': case 'r': case 'b': case 'f': c = ' '; break;
        case '"': case '\\': case '/': break;
        default: s_json.bad = true; return;
        }
        char ch = c;
        string_put(&ch, 1);
        return;
    }
    if (s_json.utf8_need) {
        if ((c & 0xc0) != 0x80) { s_json.bad = true; return; }
        s_json.utf8[s_json.utf8_len++] = c;
        if (s_json.utf8_len == s_json.utf8_need) {
            string_put(s_json.utf8, s_json.utf8_len);
            s_json.utf8_need = s_json.utf8_len = 0;
        }
        return;
    }
    if (c == '\\') { s_json.escape = true; return; }
    if (s_json.high) { s_json.bad = true; return; }
    if (c == '"') {
        s_json.string = false;
        if (s_json.clipped && !s_json.key && s_json.field != F_TEXT
            && s_json.field != F_CONTENT && s_json.field != F_DELTA) s_json.bad = true;
        if (s_json.key) {
            json_frame_t *f = &s_json.stack[s_json.depth - 1];
            f->field = s_json.clipped ? F_SKIP : field_for(s_json.key_text, f->context);
            f->state = J_COLON;
        }
    } else if (c < 0x20) s_json.bad = true;
    else if (c >= 0x80) {
        s_json.utf8_need = c >= 0xc2 && c <= 0xdf ? 2 : c >= 0xe0 && c <= 0xef ? 3
                         : c >= 0xf0 && c <= 0xf4 ? 4 : 0;
        if (!s_json.utf8_need) s_json.bad = true;
        else { s_json.utf8[0] = c; s_json.utf8_len = 1; }
    } else {
        char ch = c;
        string_put(&ch, 1);
    }
}

static void scalar_end(void)
{
    s_json.scalar = false;
    if (s_json.clipped) { if (s_json.field != F_SKIP) s_json.bad = true; return; }
    s_json.literal[s_json.len] = 0;
    if (s_json.field == F_SEQ) {
        s_row.seq = 0;
        for (size_t i = 0; i < s_json.len; i++) {
            unsigned digit = (unsigned char)s_json.literal[i] - '0';
            if (digit > 9 || s_row.seq > (UINT64_MAX - digit) / 10) { s_json.bad = true; return; }
            s_row.seq = s_row.seq * 10 + digit;
        }
    } else if (s_json.field == F_READY) {
        s_row.ready = strcmp(s_json.literal, "false") != 0;
    }
}

static void parser_byte(unsigned char c)
{
    if (s_json.bad) return;
    if (s_json.string) { string_byte(c); return; }
    bool space = c == ' ' || c == '\t' || c == '\r';
    if (s_json.scalar) {
        if (!space && c != ',' && c != '}' && c != ']') {
            if (s_json.len < sizeof(s_json.literal) - 1) s_json.literal[s_json.len++] = c;
            else s_json.clipped = true;
            return;
        }
        scalar_end();
    }
    if (space) return;
    if (s_json.complete) { s_json.bad = true; return; }
    json_frame_t *f = s_json.depth ? &s_json.stack[s_json.depth - 1] : NULL;
    if (c == '}' || c == ']') {
        if (!f || f->object != (c == '}') || f->state == J_COLON
            || (f->state != J_COMMA && f->state != (f->object ? J_KEY : J_VALUE))) {
            s_json.bad = true; return;
        }
        if (!--s_json.depth) s_json.complete = true;
        return;
    }
    if (f && f->state == J_KEY && c == '"') { string_begin(true, F_SKIP); return; }
    if (f && f->state == J_COLON && c == ':') { f->state = J_VALUE; return; }
    if (f && f->state == J_COMMA && c == ',') {
        f->state = f->object ? J_KEY : J_VALUE; f->field = F_SKIP; return;
    }
    if ((f && f->state != J_VALUE) || (!f && (s_json.started || c != '{'))) {
        s_json.bad = true; return;
    }
    unsigned field = f ? f->field : F_SKIP;
    if (f) f->state = J_COMMA;
    if (c == '{' || c == '[') {
        if (s_json.depth == sizeof(s_json.stack) / sizeof(s_json.stack[0])) { s_json.bad = true; return; }
        unsigned context = !s_json.started ? 1 : field == F_PAYLOAD ? 2 : 0;
        s_json.stack[s_json.depth++] = (json_frame_t){
            .state = c == '{' ? J_KEY : J_VALUE, .object = c == '{', .context = context };
        s_json.started = true;
    } else if (c == '"') string_begin(false, field);
    else {
        s_json.scalar = true; s_json.field = field; s_json.len = 1;
        s_json.literal[0] = c; s_json.clipped = false;
    }
}

static bool related(const row_t *row)
{
    return !s_note_id[0] || !row->reply_to[0]
        || !strcmp(row->reply_to, s_note_id) || !strcmp(row->reply_to, s_parent_id);
}

/* Append whole UTF-8 characters even when the caption is already nearly full. */
static void text_append(char *out, size_t cap, const char *text)
{
    size_t used = strlen(out), n = strlen(text);
    if (n >= cap - used) {
        n = cap - used - 1;
        while (n && ((unsigned char)text[n] & 0xc0) == 0x80) n--;
    }
    memcpy(out + used, text, n);
    out[used + n] = 0;
}

/* Called with the receive lock held; never waits on the voice task. */
static void subscription_event(void)
{
    if (s_json.bad || !s_json.complete || strcmp(s_row.type, "event")) return;
    if (s_row.seq && s_row.seq <= s_last_seq) return;
    if (s_row.seq) s_last_seq = s_row.seq;
    bool append = !strcmp(s_row.event, "delta.text_append");
    bool start = !strcmp(s_row.event, "delta.message_start");
    bool done = !strcmp(s_row.event, "delta.message_done");
    bool full = !strcmp(s_row.event, "message.assistant");
    if ((!append && !start && !done && !full) || !s_row.msg[0]) return;
    if (!related(&s_row)) return;
    if (start || append) {
        if (strcmp(s_delta.msg, s_row.msg)) {
            memset(&s_delta, 0, sizeof(s_delta));
            strlcpy(s_delta.msg, s_row.msg, sizeof(s_delta.msg));
        }
        if (s_row.reply_to[0]) strlcpy(s_delta.reply_to, s_row.reply_to, sizeof(s_delta.reply_to));
        if (append) {
            text_append(s_delta.text, sizeof(s_delta.text), s_row.text);
        }
        return;
    }
    if (!done && !s_row.ready) return;
    if (!strcmp(s_row.msg, s_delta.msg)) {
        if (!s_row.text[0]) strlcpy(s_row.text, s_delta.text, sizeof(s_row.text));
        if (!s_row.reply_to[0]) strlcpy(s_row.reply_to, s_delta.reply_to, sizeof(s_row.reply_to));
    }
    if (!related(&s_row) || !s_row.text[0]) return;
    strlcpy(s_row.event, "message.assistant", sizeof(s_row.event));
    s_row.ready = true;
    /* Coalesce the done event and persisted full message, including before ACK. */
    for (unsigned i = 0; i < s_pending_count; i++) {
        if (!strcmp(s_pending[i].msg, s_row.msg)) { s_pending[i] = s_row; return; }
    }
    /* Keep the two newest finals if the voice task has not drained the queue.
     * Before ACK they are provisional: unrelated traffic must not fail a turn
     * or grow memory without bound. Remember eviction for a useful timeout. */
    if (s_pending_count == 2) {
        if (!s_note_id[0]) s_early_evicted = true;
        s_pending[0] = s_pending[1];
        s_pending_count--;
    }
    s_pending[s_pending_count++] = s_row;
}

static void row_data(rx_t *rx, const uint8_t *data, size_t len, bool end)
{
    if (rx->status != 200) return;
    for (size_t i = 0; i < len; i++) {
        if (data[i] == '\n') {
            subscription_event();
            parser_reset();
        } else parser_byte(data[i]);
    }
    if (end) { subscription_event(); parser_reset(); }
}

static void rx_clear(rx_t *rx)
{
    rx->status = 0;
    rx->done = rx->overflow = false;
    rx->len = 0;
    if (!rx->cap) {
        parser_reset();
        s_pending_count = 0;
        s_last_seq = 0;
        s_early_evicted = false;
        s_note_id[0] = s_parent_id[0] = 0;
        memset(&s_delta, 0, sizeof(s_delta));
    }
}

static void on_frame(void *ctx, int status, const uint8_t *data, size_t len, bool end)
{
    uintptr_t token = (uintptr_t)ctx;
    rx_t *rx = &s_rx[token & 1];
    xSemaphoreTake(s_rx_lock, portMAX_DELAY);
    if ((uint32_t)(token >> 1) == rx->gen && !rx->done) {
        if (status) {
            rx->status = status;
        }
        if (!rx->cap) {
            row_data(rx, data, len, end && status >= 0);
        } else if (len && rx->len + len >= rx->cap) {
            rx->overflow = true;
        } else if (len) {
            memcpy(rx->body + rx->len, data, len);
            rx->len += len;
            rx->body[rx->len] = '\0';
        }
        rx->done = end || status < 0;
    }
    xSemaphoreGive(s_rx_lock);
}

/* Starts a request whose reply lands in slot `slot`. False if Link's session is down. */
static bool request(int slot, const char *verb, const char *path, bool json, bool end_body)
{
    char req_id[40];
    snprintf(req_id, sizeof(req_id), "muse-%08" PRIx32 "-%08" PRIx32, esp_random(), esp_random());
    const char *headers[] = { "x-request-id", req_id, "x-app-id", "hatch-web",
                              json ? "Content-Type" : NULL, "application/json",
                              "Accept", slot == RX_SUB ? "application/x-ndjson" : "application/json", NULL };
    rx_t *rx = &s_rx[slot];
    xSemaphoreTake(s_rx_lock, portMAX_DELAY);
    rx->gen++;
    rx_clear(rx);
    if (rx->cap) {
        rx->body[0] = '\0';
    }
    uintptr_t token = (uintptr_t)rx->gen << 1 | slot;
    xSemaphoreGive(s_rx_lock);
    s_stream[slot] = muse_link_req_open(verb, path, headers, end_body, on_frame, (void *)token);
    return s_stream[slot] != 0;
}

/* Drops slot `slot`'s request, if any, and whatever of its reply is still coming. */
static void drop(int slot)
{
    if (s_stream[slot]) {
        muse_link_req_cancel(s_stream[slot]);
        s_stream[slot] = 0;
    }
    xSemaphoreTake(s_rx_lock, portMAX_DELAY);
    s_rx[slot].gen++;
    rx_clear(&s_rx[slot]);
    xSemaphoreGive(s_rx_lock);
}

/* True once slot `slot`'s reply is complete (or the request died). */
static bool received(int slot)
{
    xSemaphoreTake(s_rx_lock, portMAX_DELAY);
    bool done = s_stream[slot] && s_rx[slot].done;
    xSemaphoreGive(s_rx_lock);
    if (done) {
        s_stream[slot] = 0;
    }
    return done;
}

static void emit(muse_hatch_ev_t type, const char *text)
{
    ev_t ev = { .type = type };
    strlcpy(ev.text, text ? text : "", sizeof(ev.text));
    xQueueSend(s_events, &ev, 0);
}

static void end_turn(void)
{
    drop(RX_NOTE);
    drop(RX_SUB);
    free(s_turn.stage);
    free(s_turn.chunk);
    s_turn.stage = NULL;
    s_turn.chunk = NULL;
    s_turn.phase = T_IDLE;
}

static void fail(const char *why)
{
    ESP_LOGW(TAG, "turn failed: %s", why);
    end_turn();
    strlcpy(s_turn.error, why, sizeof(s_turn.error));
    emit(MUSE_HATCH_EV_ERROR, why);
}

/* ---- The note ---- */

/* Sends the staged PCM as one body chunk; whole chunks are a multiple of 3 bytes, so only the last pads. */
static bool send_stage(bool last)
{
    size_t n = muse_hatch_base64(s_turn.stage, s_turn.stage_len, (char *)s_turn.chunk);
    if (last) {
        memcpy(s_turn.chunk + n, MUSE_HATCH_NOTE_TAIL, sizeof(MUSE_HATCH_NOTE_TAIL) - 1);
        n += sizeof(MUSE_HATCH_NOTE_TAIL) - 1;
    }
    s_turn.stage_len = 0;
    return muse_link_req_send(s_stream[RX_NOTE], s_turn.chunk, n, last, SEND_WAIT_MS);
}

/* ---- The reply ---- */

static void on_ack(void)
{
    rx_t *rx = &s_rx[RX_NOTE];
    if (rx->status != 200 || rx->overflow) {
        ESP_LOGW(TAG, "chat/stream: %d", rx->status);
        fail(rx->status < 0 ? "LOST CONNECTION TO MUSE" : "MUSE DIDN'T TAKE IT");
        return;
    }
    cJSON *root = cJSON_Parse(rx->body);
    cJSON *result = cJSON_GetObjectItem(root, "result");
    const char *id = cJSON_GetStringValue(cJSON_GetObjectItem(cJSON_IsObject(result) ? result : root, "message_id"));
    strlcpy(s_turn.note_id, id ? id : "", sizeof(s_turn.note_id));
    const char *parent = cJSON_GetStringValue(cJSON_GetObjectItem(cJSON_IsObject(result) ? result : root, "reply_to_message_id"));
    strlcpy(s_turn.parent_id, parent ? parent : "", sizeof(s_turn.parent_id));
    cJSON_Delete(root);
    if (!s_turn.note_id[0]) {
        ESP_LOGW(TAG, "chat/stream ack without a message id");
        fail("MUSE DIDN'T TAKE IT");
        return;
    }
    xSemaphoreTake(s_rx_lock, portMAX_DELAY);
    strlcpy(s_note_id, s_turn.note_id, sizeof(s_note_id));
    strlcpy(s_parent_id, s_turn.parent_id, sizeof(s_parent_id));
    unsigned kept = 0;
    for (unsigned i = 0; i < s_pending_count; i++) {
        if (related(&s_pending[i])) s_pending[kept++] = s_pending[i];
    }
    s_pending_count = kept;
    if (!related(&s_delta)) memset(&s_delta, 0, sizeof(s_delta));
    xSemaphoreGive(s_rx_lock);
    s_turn.phase = T_REPLY;
    emit(MUSE_HATCH_EV_SENT, NULL);
}

/* Completed assistant events have already been correlated under the receive lock. */
static void on_row(const row_t *r)
{
    for (unsigned i = 0; i < s_turn.seen_count; i++) {
        if (!strcmp(r->msg, s_turn.seen[i])) return;
    }
    if (r->text[0]) {
        if (s_turn.seen_count == 2) {
            memcpy(s_turn.seen[0], s_turn.seen[1], sizeof(s_turn.seen[0]));
            s_turn.seen_count = 1;
        }
        strlcpy(s_turn.seen[s_turn.seen_count++], r->msg, sizeof(s_turn.seen[0]));
        if (s_turn.text[0]) text_append(s_turn.text, sizeof(s_turn.text), " ");
        text_append(s_turn.text, sizeof(s_turn.text), r->text);
        if (!s_turn.replied) {
            s_turn.t_show = esp_timer_get_time();
        }
        s_turn.replied = true;
        s_turn.t_reply = esp_timer_get_time();
    }
}

static void subscription_error(int status)
{
    if (status == 403) fail("MUSE REPLY ACCESS DENIED (403)");
    else if (status == 401) fail("MUSE REPLY AUTH REQUIRED (401)");
    else if (status <= 0 || status == 200) fail("LOST CONNECTION TO MUSE");
    else {
        char why[EV_TEXT];
        snprintf(why, sizeof(why), "MUSE REPLY ERROR (HTTP %d)", status);
        fail(why);
    }
}

/* How far through the reply reading has got. */
static size_t read_at(int64_t now)
{
    return (size_t)((now - s_turn.t_show) * READ_CHARS_PER_S / 1000000);
}

/* Scrolls the reply through the caption at reading pace; true once it's all been shown. */
static bool scroll(int64_t now)
{
    size_t len = strlen(s_turn.text);
    size_t at = read_at(now);
    char line[EV_TEXT];
    if (muse_hatch_caption_at(s_turn.text, at < len ? at : len - 1, line, sizeof(line))
        && strcmp(line, s_turn.shown)) {
        strlcpy(s_turn.shown, line, sizeof(s_turn.shown));
        emit(MUSE_HATCH_EV_REPLY, line);
    }
    return at >= len;
}

/* Moves the turn along; runs on the voice task each time it asks for events. */
static void pump(void)
{
    int64_t now = esp_timer_get_time();
    if (s_turn.phase == T_ACK && received(RX_NOTE)) {
        on_ack();
    }
    if (s_turn.phase == T_IDLE) return;
    /* Preserve early events until the POST ACK supplies the note IDs. */
    static row_t pending; /* voice task only; avoid a large stack frame */
    xSemaphoreTake(s_rx_lock, portMAX_DELAY);
    int status = s_rx[RX_SUB].status;
    bool closed = s_rx[RX_SUB].done;
    bool early_evicted = s_early_evicted;
    xSemaphoreGive(s_rx_lock);
    if (status < 0 || status >= 400) {
        subscription_error(status);
        return;
    }
    if (s_turn.phase == T_REPLY) {
        for (;;) {
            xSemaphoreTake(s_rx_lock, portMAX_DELAY);
            bool have = s_pending_count > 0;
            if (have) {
                pending = s_pending[0];
                if (--s_pending_count) s_pending[0] = s_pending[1];
            }
            xSemaphoreGive(s_rx_lock);
            if (!have) break;
            on_row(&pending);
        }
        if (closed && !s_turn.replied) {
            subscription_error(status);
            return;
        }
    }
    if (s_turn.phase != T_REPLY) {
        if (s_turn.phase == T_ACK && now - s_turn.t_end > REPLY_TIMEOUT_US) {
            fail("NO REPLY FROM MUSE");
        }
        return;
    }
    if (s_turn.replied) {
        if (scroll(now) && now - s_turn.t_reply > SETTLE_US) {
            end_turn();
            emit(MUSE_HATCH_EV_DONE, NULL);
        }
    } else if (now - s_turn.t_end > REPLY_TIMEOUT_US) {
        fail(early_evicted ? "REPLY BUFFER LIMIT - TRY AGAIN" : "NO REPLY FROM MUSE");
    }
}

/* ---- Public ---- */

void muse_hatch_start(void)
{
    s_rx_lock = xSemaphoreCreateMutex();
    s_events = xQueueCreate(8, sizeof(ev_t));
    static char ack[ACK_MAX];
    s_rx[RX_NOTE].body = ack;
    s_rx[RX_NOTE].cap = sizeof(ack);
}

void muse_hatch_status(muse_hatch_status_t *out)
{
    if (!muse_link_hatch_linked()) {
        out->state = MUSE_HATCH_NOT_SET;
        strlcpy(out->detail, "Pair in the Muse app", sizeof(out->detail));
    } else if (!muse_wifi_connected()) {
        out->state = MUSE_HATCH_OFFLINE;
        strlcpy(out->detail, "Waiting for Wi-Fi", sizeof(out->detail));
    } else if (muse_link_req_ready()) {
        out->state = MUSE_HATCH_REACHABLE;
        strlcpy(out->detail, "Through Home Link, text replies", sizeof(out->detail));
    } else {
        out->state = MUSE_HATCH_TESTING;
        strlcpy(out->detail, "Connecting...", sizeof(out->detail));
    }
}

void muse_hatch_test(void)
{
}

void muse_hatch_config_changed(void)
{
}

void muse_hatch_set_resting(bool resting)
{
    (void)resting;   /* Link's session does the polling */
}

const char *muse_hatch_state_name(muse_hatch_state_t state)
{
    switch (state) {
    case MUSE_HATCH_NOT_SET: return "Not set up";
    case MUSE_HATCH_OFFLINE: return "Offline";
    case MUSE_HATCH_UNTESTED: return "Saved";
    case MUSE_HATCH_TESTING: return "Connecting";
    case MUSE_HATCH_REACHABLE: return "Connected";
    case MUSE_HATCH_UNREACHABLE: return "Can't connect";
    }
    return "";
}

bool muse_hatch_ready(void)
{
    return s_events && muse_link_hatch_linked() && muse_wifi_connected() && muse_link_req_ready();
}

void muse_hatch_turn_begin(void)
{
    end_turn();
    xQueueReset(s_events);
    memset(&s_turn, 0, sizeof(s_turn));
    s_turn.stage = malloc(STAGE_BYTES);
    s_turn.chunk = malloc(CHUNK_BYTES + sizeof(MUSE_HATCH_NOTE_TAIL));
    if (!s_turn.stage || !s_turn.chunk) {
        fail("OUT OF MEMORY");
        return;
    }
    if (!request(RX_NOTE, "POST", "/chat/stream", true, false)
        || !muse_link_req_send(s_stream[RX_NOTE], MUSE_HATCH_NOTE_HEAD, sizeof(MUSE_HATCH_NOTE_HEAD) - 1, false, SEND_WAIT_MS)) {
        fail("CAN'T REACH MUSE");
        return;
    }
    muse_hatch_wav_header(s_turn.stage, MIC_RATE);
    s_turn.stage_len = MUSE_HATCH_WAV_HEADER;
    s_turn.phase = T_TALKING;
}

void muse_hatch_turn_audio(const int16_t *pcm, size_t frames)
{
    const uint8_t *p = (const uint8_t *)pcm;
    size_t n = frames * 2;
    while (s_turn.phase == T_TALKING && n) {
        size_t take = STAGE_BYTES - s_turn.stage_len < n ? STAGE_BYTES - s_turn.stage_len : n;
        memcpy(s_turn.stage + s_turn.stage_len, p, take);
        s_turn.stage_len += take;
        p += take;
        n -= take;
        if (s_turn.stage_len == STAGE_BYTES && !send_stage(false)) {
            fail("CAN'T KEEP UP");
        }
    }
}

void muse_hatch_turn_end(void)
{
    if (s_turn.phase != T_TALKING) {
        /* Failed while recording: that error went to the recording caption. */
        emit(MUSE_HATCH_EV_ERROR, s_turn.error[0] ? s_turn.error : "CAN'T REACH MUSE");
        return;
    }
    /* Subscribe only after recording: keep inbound reply traffic out of the
     * real-time audio upload. Queue it before the note's final body chunk. */
    if (!request(RX_SUB, "POST", "/chat/subscribe", true, false)
        || !muse_link_req_send(s_stream[RX_SUB], "{}", 2, true, SEND_WAIT_MS)) {
        fail("CAN'T SUBSCRIBE TO MUSE");
        return;
    }
    if (!send_stage(true)) {
        fail("CAN'T KEEP UP");
        return;
    }
    free(s_turn.stage);
    free(s_turn.chunk);
    s_turn.stage = NULL;
    s_turn.chunk = NULL;
    s_turn.t_end = esp_timer_get_time();
    s_turn.phase = T_ACK;

}

void muse_hatch_turn_cancel(void)
{
    end_turn();
    xQueueReset(s_events);
}

muse_hatch_ev_t muse_hatch_turn_event(char *text, size_t cap)
{
    pump();
    ev_t ev;
    if (xQueueReceive(s_events, &ev, 0) != pdTRUE) {
        return MUSE_HATCH_EV_NONE;
    }
    strlcpy(text, ev.text, cap);
    return ev.type;
}

bool muse_hatch_turn_caption(size_t played, char *out, size_t cap)
{
    (void)played;   /* no speech: the reply's page follows the reading pace */
    size_t len = strlen(s_turn.text);
    if (s_turn.phase != T_REPLY || !s_turn.replied || !len) {
        return false;
    }
    size_t at = read_at(esp_timer_get_time());
    return muse_hatch_caption_at(s_turn.text, at < len ? at : len - 1, out, cap);
}

size_t muse_hatch_turn_read(int16_t *pcm, size_t frames, int wait_ms)
{
    (void)pcm;
    (void)frames;
    if (wait_ms > 0) {
        vTaskDelay(pdMS_TO_TICKS(wait_ms) ? pdMS_TO_TICKS(wait_ms) : 1);
    }
    return 0;
}

size_t muse_hatch_mp3_selftest(int16_t **pcm)
{
    *pcm = NULL;
    return 0;
}
