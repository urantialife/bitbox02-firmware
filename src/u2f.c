// Copyright 2019 Shift Cryptosecurity AG
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <string.h>

#include <commander/commander.h>
#include <drivers/driver_init.h>
#include <keystore.h>
#include <pukcc/curve_p256.h>
#include <pukcc/pukcc.h>
#include <queue.h>
#include <random.h>
#include <screen.h>
#include <ui/screen_process.h>
#include <ui/screen_stack.h>
#include <ui/component.h>
#include <ui/components/ui_components.h>
#include <u2f.h>
#include <usb/u2f/u2f_hid.h>
#include <usb/u2f/u2f_keys.h>
#include <usb/usb_frame.h>
#include <usb/usb_packet.h>
#include <usb/usb_processing.h>
#include <util.h>
#include <wally_crypto.h>

// TODO - use ATECC chip for NIST-P signing
// TODO - get code to pass v1 live testing: tests_u2f_hid and tests_u2f_standard

static Packet* _reg_out_packet;
static Packet* _auth_out_packet;
static const U2F_REGISTER_REQ* _reg_request;
static const U2F_AUTHENTICATE_REQ* _auth_request;

typedef struct {
    uint8_t cla, ins, p1, p2;
    uint8_t lc1, lc2, lc3;
    uint8_t data[];
} USB_APDU;

static bool _done = false;

static bool _is_done(void) {
    return _done;
}

/////////////////
// FIXME - sham function
// TODO  - u2f counter - in flash? use monotonic counter?
static uint32_t memory_u2f_count_iter(void)
{
    static uint32_t ctr = 0;
    return ctr++;
}
/////////////////

#define APDU_LEN(A) (uint32_t)(((A).lc1 << 16) + ((A).lc2 << 8) + ((A).lc3))
#define U2F_TIMEOUT 500 // [msec]
#define U2F_KEYHANDLE_LEN (U2F_NONCE_LENGTH + SHA256_DIGEST_LENGTH)

#if (U2F_EC_KEY_SIZE != SHA256_DIGEST_LENGTH) || (U2F_EC_KEY_SIZE != U2F_NONCE_LENGTH)
#error "Incorrect macro values for u2f"
#endif

static uint32_t _cid = 0;
volatile bool _state_continue = false;
volatile uint16_t _current_time_ms = 0;
const uint8_t _hijack_code[U2F_HIJACK_ORIGIN_TOTAL][U2F_APPID_SIZE] = {
    {
        /* Corresponds to U2F client challenge filled with `0xdb` */
        /* Origin `https://digitalbitbox.com` */
        0x17, 0x9d, 0xc3, 0x1c, 0x3a, 0xd4, 0x0f, 0x05, 0xf0, 0x71, 0x71,
        0xed, 0xf4, 0x46, 0x4a, 0x71, 0x0a, 0x2d, 0xd4, 0xde, 0xc7, 0xe6,
        0x14, 0x41, 0xc5, 0xbd, 0x24, 0x97, 0x8a, 0x99, 0x2a, 0x1a,
    },
    {
        /* Origin `https://www.myetherwallet.com` */
        0x8e, 0x57, 0xf6, 0x48, 0xb9, 0x1b, 0x24, 0xfe, 0x27, 0x92, 0x3a,
        0x75, 0xef, 0xa1, 0xd0, 0x62, 0xdc, 0xb5, 0x4d, 0x41, 0xfd, 0x0b,
        0xee, 0x33, 0x9e, 0xf2, 0xa2, 0xb4, 0x55, 0x0c, 0xbe, 0x05,
    },
    {
        /* Origin `https://vintage.myetherwallet.com` */
        0x0f, 0x5b, 0x76, 0xef, 0x29, 0x8f, 0x15, 0x0b, 0x4d, 0x39, 0x9d,
        0x2c, 0x3c, 0xb9, 0x0e, 0x86, 0x54, 0xa3, 0x7c, 0x60, 0x5f, 0x73,
        0x35, 0x68, 0xee, 0x68, 0xec, 0x41, 0x48, 0x8d, 0x53, 0x14,
    },
    {
        /* Origin `https://mycrypto.com` */
        0xbd, 0x22, 0x66, 0x24, 0x02, 0x18, 0x8c, 0x4d, 0xba, 0x4b, 0xb3,
        0xd7, 0xe3, 0x98, 0x00, 0x7c, 0x5b, 0x98, 0x6f, 0x46, 0x27, 0x1f,
        0x6d, 0xf9, 0x2e, 0x24, 0x01, 0xa7, 0xce, 0xfd, 0x1a, 0xa8,
    }};

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpacked"
#pragma GCC diagnostic ignored "-Wattributes"

typedef struct __attribute__((__packed__)) {
    uint8_t reserved;
    uint8_t appId[U2F_APPID_SIZE];
    uint8_t challenge[U2F_NONCE_LENGTH];
    uint8_t keyHandle[U2F_KEYHANDLE_LEN];
    uint8_t pubKey[U2F_EC_POINT_SIZE];
} U2F_REGISTER_SIG_STR;

typedef struct  __attribute__((__packed__)) {
    uint8_t appId[U2F_APPID_SIZE];
    uint8_t flags;
    uint8_t ctr[4];
    uint8_t challenge[U2F_NONCE_LENGTH];
} U2F_AUTHENTICATE_SIG_STR;

#pragma GCC diagnostic pop

static uint32_t _next_cid(void)
{
    do {
        _cid = (random_byte_mcu() << 0) +
               (random_byte_mcu() << 8) +
               (random_byte_mcu() << 16) +
               (random_byte_mcu() << 24);
    } while (_cid == 0 || _cid == U2FHID_CID_BROADCAST);
    return _cid;
}

static void _fill_message(const uint8_t* data, const uint32_t len, Packet *out_packet)
{
    util_zero(out_packet->data_addr, sizeof(out_packet->data_addr));
    memcpy(out_packet->data_addr, data, len);
    out_packet->cid = _cid;
    out_packet->cmd = U2FHID_MSG;
    out_packet->len = len;
}

static void _error_hid(uint32_t fcid, uint8_t err, Packet *out_packet)
{
    util_zero(out_packet->data_addr, sizeof(out_packet->data_addr));
    out_packet->data_addr[0] = err;
    out_packet->cid = fcid;
    out_packet->cmd = U2FHID_ERROR;
    out_packet->len = 1;
}

static void _error(const uint16_t err, Packet* out_packet)
{
    uint8_t data[2];
    data[0] = err >> 8 & 0xFF;
    data[1] = err & 0xFF;
    _fill_message(data, 2, out_packet);
}

static void _version(const USB_APDU* a, Packet* out_packet)
{
    if (APDU_LEN(*a) != 0) {
        _error(U2F_SW_WRONG_LENGTH, out_packet);
        _done = true;
        return;
    }

    static const uint8_t version_response[] = {'U', '2', 'F', '_', 'V', '2', 0x90, 0x00};
    _fill_message(version_response, sizeof(version_response), out_packet);
    _done = true;
}

/**
 * Generates a key for the given app id, salted with the passed nonce.
 * @param[in] appId The app id of the RP which requests a registration or authentication process.
 * @param[in] nonce A random nonce with which the seed for the private key is salted.
 * @param[out] privkey The generated private key.
 * @param[out] mac The message authentication code for the private key.
 */
//UTIL_WARN_UNUSED_RESULT static bool _keyhandle_gen(const uint8_t* appId, uint8_t* nonce, uint8_t* privkey, uint8_t* mac)// TODO - enforce handling return value
static bool _keyhandle_gen(const uint8_t* appId, uint8_t* nonce, uint8_t* privkey, uint8_t* mac)
{
    uint8_t hash[SHA256_DIGEST_LENGTH];
    for (;;) {
        uint8_t handle[U2F_APPID_SIZE + 4];
        uint8_t seed[32];
        uint32_t seed_length;
        memcpy(handle, "u2f:", 4);
        memcpy(handle + 4, appId, U2F_APPID_SIZE);
        if (!keystore_copy_seed(seed, &seed_length)) {
            // TODO: return an error if the keystore hasn't been unlocked yet.
            // return false;
        }
        memset(seed, 0, sizeof(seed));// FIXME - remove when keystore_copy_seed is enabled
        wally_hmac_sha256(seed, seed_length, handle, sizeof(handle), hash, HMAC_SHA256_LEN);
        wally_hmac_sha256(hash, HMAC_SHA256_LEN, nonce, U2F_NONCE_LENGTH, privkey, HMAC_SHA256_LEN);
        wally_hmac_sha256(hash, HMAC_SHA256_LEN, privkey, U2F_EC_KEY_SIZE, mac, HMAC_SHA256_LEN);

        // if (ecc_isValid(privkey, ECC_SECP256r1)) {// TODO - check if key is valid
        if (1) {
             return true;
        }

        memcpy(nonce, mac, U2F_NONCE_LENGTH);
    }
}

static int _sig_to_der(const uint8_t *sig, uint8_t *der)
{
    int i;
    uint8_t *p = der, *len, *len1, *len2;
    *p = 0x30;
    p++; // sequence
    *p = 0x00;
    len = p;
    p++; // len(sequence)

    *p = 0x02;
    p++; // integer
    *p = 0x00;
    len1 = p;
    p++; // len(integer)

    // process R
    i = 0;
    while (sig[i] == 0 && i < 32) {
        i++; // skip leading zeroes
    }
    if (sig[i] >= 0x80) { // put zero in output if MSB set
        *p = 0x00;
        p++;
        *len1 = *len1 + 1;
    }
    while (i < 32) { // copy bytes to output
        *p = sig[i];
        p++;
        *len1 = *len1 + 1;
        i++;
    }

    *p = 0x02;
    p++; // integer
    *p = 0x00;
    len2 = p;
    p++; // len(integer)

    // process S
    i = 32;
    while (sig[i] == 0 && i < 64) {
        i++; // skip leading zeroes
    }
    if (sig[i] >= 0x80) { // put zero in output if MSB set
        *p = 0x00;
        p++;
        *len2 = *len2 + 1;
    }
    while (i < 64) { // copy bytes to output
        *p = sig[i];
        p++;
        *len2 = *len2 + 1;
        i++;
    }

    *len = *len1 + *len2 + 4;
    return *len + 2;
}

static void _continue_registration(component_t* component)
{
    (void) component;
    ui_screen_stack_pop();

    uint8_t privkey[U2F_EC_KEY_SIZE];
    uint8_t nonce[U2F_NONCE_LENGTH];
    uint8_t mac[HMAC_SHA256_LEN];
    uint8_t sig[64];
    uint8_t data[sizeof(U2F_REGISTER_RESP) + 2];
    U2F_REGISTER_SIG_STR sig_base;
    U2F_REGISTER_RESP* response = (U2F_REGISTER_RESP*)data;
    util_zero(data, sizeof(data));

    random_32_bytes_mcu(nonce);

    _keyhandle_gen(_reg_request->appId, nonce, privkey, mac);

    ////ecc_get_public_key65(privkey, (uint8_t *)&response->pubKey, ECC_SECP256r1);// TODO

    response->registerId = U2F_REGISTER_ID;
    response->keyHandleLen = U2F_KEYHANDLE_LEN;

    memcpy(response->keyHandleCertSig, mac, sizeof(mac));
    memcpy(response->keyHandleCertSig + sizeof(mac), nonce, sizeof(nonce));
    memcpy(response->keyHandleCertSig + response->keyHandleLen, U2F_ATT_CERT, sizeof(U2F_ATT_CERT));

    // Add signature using attestation key
    sig_base.reserved = 0;
    memcpy(sig_base.appId, _reg_request->appId, U2F_APPID_SIZE);
    memcpy(sig_base.challenge, _reg_request->challenge, U2F_NONCE_LENGTH);
    memcpy(sig_base.keyHandle, &response->keyHandleCertSig, U2F_KEYHANDLE_LEN);
    memcpy(sig_base.pubKey, &response->pubKey, U2F_EC_POINT_SIZE);

    /* TODO - use atecc chip
    if (pukcc_ecdsa_sign(
            U2F_ATT_PRIV_KEY, (uint8_t*)&sig_base, sizeof(sig_base), sig, curve_p256)) {
        _error(U2F_SW_WRONG_DATA, _reg_out_packet);
        return;
    }
    */

    uint8_t* resp_sig = response->keyHandleCertSig + response->keyHandleLen + sizeof(U2F_ATT_CERT);
    int der_len = _sig_to_der(sig, resp_sig);

    // Append success bytes
    memcpy(
        response->keyHandleCertSig + response->keyHandleLen + sizeof(U2F_ATT_CERT) + der_len,
        "\x90\x00",
        2);

    int len = 1 /* registerId */ + U2F_EC_POINT_SIZE + 1 /* keyhandleLen */ +
              response->keyHandleLen + sizeof(U2F_ATT_CERT) + der_len + 2;

    _fill_message(data, len, _reg_out_packet);
    _done = true;
}

static void _cancel_registration(component_t* component)
{
    (void) component;
    ui_screen_stack_pop();
    _error(U2F_SW_CONDITIONS_NOT_SATISFIED, _reg_out_packet);
    _done = true;
}

/**
 * Initiates the U2F registration workflow.
 * @param[in] apdu The APDU packet.
 */
static void _register(const USB_APDU* apdu, Packet* out_packet)
{
    if (APDU_LEN(*apdu) != sizeof(U2F_REGISTER_REQ)) {
        _error(U2F_SW_WRONG_LENGTH, out_packet);
        _done = true;
        return;
    }
    _reg_out_packet = out_packet;
    _reg_request = (const U2F_REGISTER_REQ*) apdu->data;
    ui_screen_stack_push(confirm_create("U2F", "Register?", _continue_registration, _cancel_registration));
}

static void _hijack(const U2F_AUTHENTICATE_REQ* req, Packet *out_packet)
{
    // TODO - copy from v1 once finalized
    (void)req;
    (void)out_packet;
}

static void _continue_authentication(component_t* component)
{
    (void) component;
    uint8_t privkey[U2F_EC_KEY_SIZE];
    uint8_t nonce[U2F_NONCE_LENGTH];
    uint8_t mac[HMAC_SHA256_LEN];
    uint8_t sig[64];
    U2F_AUTHENTICATE_SIG_STR sig_base;

    memcpy(nonce, _auth_request->keyHandle + sizeof(mac), sizeof(nonce));
    _keyhandle_gen(_auth_request->appId, nonce, privkey, mac);

    if (!MEMEQ(_auth_request->keyHandle, mac, SHA256_DIGEST_LENGTH)) {
        _error(U2F_SW_WRONG_DATA, _auth_out_packet);
        return;
    }

    uint8_t buf[sizeof(U2F_AUTHENTICATE_RESP) + 2];
    U2F_AUTHENTICATE_RESP* response = (U2F_AUTHENTICATE_RESP*)&buf;

    const uint32_t ctr = memory_u2f_count_iter();
    response->flags = U2F_AUTH_FLAG_TUP;
    response->ctr[0] = (ctr >> 24) & 0xff;
    response->ctr[1] = (ctr >> 16) & 0xff;
    response->ctr[2] = (ctr >> 8) & 0xff;
    response->ctr[3] = ctr & 0xff;

    // Sign
    memcpy(sig_base.appId, _auth_request->appId, U2F_APPID_SIZE);
    sig_base.flags = response->flags;
    memcpy(sig_base.ctr, response->ctr, 4);
    memcpy(sig_base.challenge, _auth_request->challenge, U2F_NONCE_LENGTH);

    /* TODO - use atecc chip
    if (pukcc_ecdsa_sign(privkey, (uint8_t*)&sig_base, sizeof(sig_base), sig, curve_p256)) {
        _error(U2F_SW_WRONG_DATA, _auth_out_packet);
        return;
    }
    */
    int der_len = _sig_to_der(sig, response->sig);

    // Append success bytes
    memcpy(buf + sizeof(U2F_AUTHENTICATE_RESP) - U2F_MAX_EC_SIG_SIZE + der_len, "\x90\x00", 2);
    _fill_message(buf, sizeof(U2F_AUTHENTICATE_RESP) - U2F_MAX_EC_SIG_SIZE + der_len + 2, _auth_out_packet);
    _done = true;
}

static void _cancel_authentication(component_t* component)
{
    (void) component;
    _error(U2F_SW_CONDITIONS_NOT_SATISFIED, _auth_out_packet);
    _done = true;
}

static void _authenticate(const USB_APDU* apdu, Packet* out_packet)
{
    if (APDU_LEN(*apdu) < U2F_KEYHANDLE_LEN) { // actual size could vary
        _error(U2F_SW_WRONG_LENGTH, out_packet);
        _done = true;
        return;
    }

    _auth_request = (const U2F_AUTHENTICATE_REQ *)apdu->data;
    _auth_out_packet = out_packet;

    for (uint8_t i = 0; i < U2F_HIJACK_ORIGIN_TOTAL; i++) {
        // As an alternative interface, hijack the U2F AUTH key handle data field.
        // Slower but works in browsers for specified sites without requiring an extension.
        if (MEMEQ(_auth_request->appId, _hijack_code[i], U2F_APPID_SIZE)) {
            _hijack(_auth_request, out_packet);
            _done = true;
            return;
        }
    }

    if (apdu->p1 == U2F_AUTH_CHECK_ONLY) {
        _error(U2F_SW_CONDITIONS_NOT_SATISFIED, out_packet);
        _done = true;
        return;
    }

    if (apdu->p1 != U2F_AUTH_ENFORCE) {
        _error(U2F_SW_WRONG_DATA, out_packet);
        _done = true;
        return;
    }

    ui_screen_stack_push(confirm_create("U2F", "Authenticate?", _continue_authentication, _cancel_authentication));
}

static void _cmd_ping(const Packet* in_packet, Packet* out_packet, const size_t max_out_len)
{
    (void)max_out_len;
    util_zero(out_packet->data_addr, sizeof(out_packet->data_addr));
    memcpy(out_packet->data_addr, in_packet->data_addr, USB_DATA_MAX_LEN);
    out_packet->len = in_packet->len;
    out_packet->cmd = U2FHID_PING;
    out_packet->cid = _cid;
}

static void _cmd_wink(const Packet* in_packet, Packet* out_packet, const size_t max_out_len)
{
    (void)max_out_len;

    if (in_packet->len > 0) {
        _error_hid(_cid, U2FHID_ERR_INVALID_LEN, out_packet);
        return;
    }

    util_zero(out_packet->data_addr, sizeof(out_packet->data_addr));
    out_packet->len = 0;
    out_packet->cmd = U2FHID_WINK;
    out_packet->cid = _cid;
}

/* FIXME - likely delete, as never used so far...
static void _cmd_sync(const Packet* in_packet, Packet* out_packet, const size_t max_out_len)
{
    (void)in_packet;
    (void)out_packet;
    (void)max_out_len;
}

static void _cmd_lock(const Packet* in_packet, Packet* out_packet, const size_t max_out_len)
{
    (void)in_packet;
    (void)out_packet;
    (void)max_out_len;
}
*/

/**
 * Synchronize a channel and optionally requests a unique 32-bit channel identifier (CID)
 * that can be used by the requesting application during its lifetime.
 */
static void _cmd_init(const Packet* in_packet, Packet* out_packet, const size_t max_out_len)
{
    if (U2FHID_INIT_RESP_SIZE >= max_out_len) {
        _error_hid(in_packet->cid, U2FHID_ERR_OTHER, out_packet);
        return;
    }

    const U2FHID_INIT_REQ* init_req = (const U2FHID_INIT_REQ*)&in_packet->data_addr;
    U2FHID_INIT_RESP response;

    if (in_packet->cid == 0) {
        _error_hid(in_packet->cid, U2FHID_ERR_INVALID_CID, out_packet);
        return;
    }

    out_packet->cid = in_packet->cid;
    out_packet->cmd = U2FHID_INIT;
    out_packet->len = U2FHID_INIT_RESP_SIZE;

    util_zero(&response, sizeof(response));
    memcpy(response.nonce, init_req->nonce, sizeof(init_req->nonce));
    response.cid = in_packet->cid == U2FHID_CID_BROADCAST ? _next_cid() : in_packet->cid;
    response.versionInterface = U2FHID_IF_VERSION;
    response.versionMajor = DIGITAL_BITBOX_VERSION_MAJOR;
    response.versionMinor = DIGITAL_BITBOX_VERSION_MINOR;
    response.versionBuild = DIGITAL_BITBOX_VERSION_PATCH;
    response.capFlags = U2FHID_CAPFLAG_WINK;
    util_zero(out_packet->data_addr, sizeof(out_packet->data_addr));
    memcpy(out_packet->data_addr, &response, sizeof(response));
}

/**
 * Process a U2F message
 */
// TODO - likely need to handle and return appropriate error messages for U2F specification
static void _cmd_msg(const Packet* in_packet, Packet* out_packet, const size_t max_out_len)
{
    (void)max_out_len;

    _done = false;
    const USB_APDU* apdu = (const USB_APDU*)in_packet->data_addr;

    if ((APDU_LEN(*apdu) + sizeof(USB_APDU)) > in_packet->len) {
        return;
        //return U2FHID_ERR_INVALID_LEN;
    }

    if (apdu->cla != 0) {
        _error(U2F_SW_CLA_NOT_SUPPORTED, out_packet);
        return;
        //return U2FHID_ERR_NONE;
    }

    switch (apdu->ins) {
    case U2F_REGISTER:
        _register(apdu, out_packet);
        break;
    case U2F_AUTHENTICATE:
        _authenticate(apdu, out_packet);
        break;
    case U2F_VERSION:
        _version(apdu, out_packet);
        break;
    default:
        _error(U2F_SW_INS_NOT_SUPPORTED, out_packet);
        return;
    }
    ui_screen_process(_is_done);// TODO - check if every branch leads to setting _is_done = true prior to returning
    //return U2FHID_ERR_NONE;
}


// TODO - currently not called - see v1 code for example usage
void u2f_device_timeout(void)
{
    if (!_state_continue) {
        return;
    }

    _current_time_ms += 40;

    if (_current_time_ms > U2F_TIMEOUT) {
        // TODO - enable
        //u2f_device_reset_state();
        //_error_hid(_cid, U2FHID_ERR_MSG_TIMEOUT, out_packet);
        // usb_reply_queue_send();
    }
}

/**
 * Set up the U2F commands.
 */
void u2f_device_setup(void)
{
    const CMD_Callback u2f_cmd_callbacks[] = {
        {U2FHID_PING, _cmd_ping},
        {U2FHID_WINK, _cmd_wink},
        {U2FHID_INIT, _cmd_init},
        {U2FHID_MSG, _cmd_msg},
    };
    usb_processing_register_cmds(
        u2f_cmd_callbacks, sizeof(u2f_cmd_callbacks) / sizeof(CMD_Callback));
}



/////////////////////////////////////////////////////////////////////////////////

/* v1 code artifacts that may or may not be needed
 *
 *
static void u2f_device_reset_state(void)
{
    memset(&reader, 0, sizeof(reader));
    _state_continue = false;
}

static void u2f_device_cmd_cont(const USB_FRAME *f)
{
    (void) f;

    if ((reader.buf_ptr - reader.buf) < (signed)reader.len) {
        // Need more data
        return;
    }

    _state_continue = false;

    if (0) {
    //if ( (reader.cmd < U2FHID_VENDOR_FIRST) &&// FIXME -
            //!(memory_report_ext_flags() & MEM_EXT_MASK_U2F) ) {
        //// Abort U2F commands if the U2F bit is not set (==U2F disabled).
        //// Vendor specific commands are passed through.
        //_error_hid(_cid, U2FHID_ERR_CHANNEL_BUSY, out_packet);
    } else {
        // Received all data
        switch (reader.cmd) {
            case U2FHID_PING:
                _cmd_ping(reader.buf, reader.len);
                break;
            case U2FHID_MSG:
                _cmd_msg((USB_APDU *)reader.buf, reader.len);
                break;
            case U2FHID_WINK:
                _cmd_wink(reader.buf, reader.len);
                break;
            case U2FHID_HWW: {
                //char *report;
                reader.buf[MIN(reader.len, sizeof(reader.buf) - 1)] = '\0';// NULL terminate
                //report = commander((const char *)reader.buf);
                //usb_reply_queue_load_msg(U2FHID_HWW, (const uint8_t *)report, strlens(report),
_cid);// FIXME - // FIXME - need to split inot 64byte packets for queue push break;
            }
            default:
                _error_hid(_cid, U2FHID_ERR_INVALID_CMD, out_packet);
                break;
        }
    }

    // Finished
    u2f_device_reset_state();
    _cid = 0;
}

static void u2f_device_cmd_init(const USB_FRAME *f)
{
    if (f->cid == U2FHID_CID_BROADCAST || f->cid == 0) {
        _error_hid(f->cid, U2FHID_ERR_INVALID_CID, out_packet);
        return;
    }

    if ((unsigned)U2FHID_MSG_LEN(*f) > sizeof(reader.buf)) {
        _error_hid(f->cid, U2FHID_ERR_INVALID_LEN, out_packet);
        return;
    }

    memset(&reader, 0, sizeof(reader));
    reader.seq = 0;
    reader.buf_ptr = reader.buf;
    reader.len = U2FHID_MSG_LEN(*f);
    reader.cmd = f->type;
    memcpy(reader.buf_ptr, f->init.data, sizeof(f->init.data));
    reader.buf_ptr += sizeof(f->init.data);
    _cid = f->cid;

    _current_time_ms = 0;
    _state_continue = true;
    u2f_device_cmd_cont(f);
}

void u2f_device_run(const USB_FRAME *f)
{
    if ((f->type & U2FHID_TYPE_MASK) == U2FHID_TYPE_INIT) {

        if (f->init.cmd == U2FHID_INIT) {
            _cmd_init(f);
            if (f->cid == _cid) {
                u2f_device_reset_state();
            }
        } else if (_state_continue) {
            if (f->cid == _cid) {
                queue_clear();
                u2f_device_reset_state();
                _error_hid(f->cid, U2FHID_ERR_INVALID_SEQ, out_packet);
            } else {
                _error_hid(f->cid, U2FHID_ERR_CHANNEL_BUSY, out_packet);
            }
        } else {
            u2f_device_cmd_init(f);
        }
        goto exit;
    }

    if ((f->type & U2FHID_TYPE_MASK) == U2FHID_TYPE_CONT) {

        if (!_state_continue) {
            goto exit;
        }

        if (_cid != f->cid) {
            _error_hid(f->cid, U2FHID_ERR_CHANNEL_BUSY, out_packet);
            goto exit;
        }

        if (reader.seq != f->cont.seq) {
            queue_clear();
            u2f_device_reset_state();
            _error_hid(f->cid, U2FHID_ERR_INVALID_SEQ, out_packet);
            goto exit;
        }

        // Check bounds
        if ((reader.buf_ptr - reader.buf) >= (signed) reader.len
                || (reader.buf_ptr + sizeof(f->cont.data) - reader.buf) > (signed) sizeof(
                    reader.buf)) {
            goto exit;
        }

        reader.seq++;
        memcpy(reader.buf_ptr, f->cont.data, sizeof(f->cont.data));
        reader.buf_ptr += sizeof(f->cont.data);
        u2f_device_cmd_cont(f);
    }

exit:
    (void)f;// FIXME - to avoid compile warning
    //usb_reply_queue_send();// FIXME - // FIXME -
}
*/

