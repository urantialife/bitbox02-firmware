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
#ifndef TESTING
#include "drivers/driver_init.h"
#include "qtouch.h"
#endif
#include <workflow/mnemonic.h>
#include <workflow/workflow.h>

#include <wally_bip39.h>

#include <ui/screen_process.h>

#include "hardfault.h"
#include "keystore.h"
#include "memory.h"
#include "random.h"
#include "screen.h"
#include "sd.h"
#include "util.h"

#include "securechip/securechip.h"

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-function"

uint32_t __stack_chk_guard = 0;

extern void __attribute__((noreturn)) __stack_chk_fail(void);
void __attribute__((noreturn)) __stack_chk_fail(void)
{
    screen_print_debug("Stack smashing detected", 0);
    while (1) {
    }
}

static bool _mock_get_bip_39_mnemonic(char** mnemonic)
{
    const char* wordlist =
        "flight donkey evolve skirt inspire balcony accident aisle walk vivid weasel region "
        "sadness immense index champion almost avocado castle chaos defense crystal device emotion";
    *mnemonic = strdup(wordlist);
    return true;
}

static bool _unlock(const char* password)
{
    (void)password;
    Abort("unlock shouldn't be called in this test case");
    return false;
}

static void _create_and_store_seed(const char* password)
{
    if (!keystore_create_and_store_seed(password)) {
        Abort("create_and_store_seed");
    }
}

static workflow_interface_functions_t _workflow_interface_functions = {
    .create_and_store_seed = _create_and_store_seed,
    .is_seeded = memory_is_seeded,
    .unlock = _unlock,
    .sd_card_inserted = sd_card_inserted,
    .get_bip39_mnemonic = _mock_get_bip_39_mnemonic,
    .get_bip39_word = keystore_get_bip39_word,
    .get_bip39_wordlist_length = keystore_get_bip39_wordlist_length};

int main(void)
{
    system_init();
    screen_init();
    qtouch_init();

    workflow_set_interface_functions(&_workflow_interface_functions);
    workflow_show_mnemonic_create();

    ui_screen_process(NULL);
}

#pragma GCC diagnostic pop
