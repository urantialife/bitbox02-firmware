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

#include "common_main.h"
#include "drivers/driver_init.h"
#include "hardfault.h"
#include "keystore.h"
#include "memory.h"
#include "qtouch.h"
#include "screen.h"
#include "sd.h"
#include "ui/screen_process.h"
#include "workflow/workflow.h"

static workflow_interface_functions_t _workflow_interface_functions = {
    .is_seeded = memory_is_seeded,
    .sd_card_inserted = sd_card_inserted,
    .get_bip39_mnemonic = keystore_get_bip39_mnemonic,
    .get_bip39_word = keystore_get_bip39_word,
    .get_bip39_wordlist_length = keystore_get_bip39_wordlist_length};

uint32_t __stack_chk_guard = 0;

int main(void)
{
    init_mcu();
    system_init();
    __stack_chk_guard = common_stack_chk_guard();
    screen_init();
    screen_splash();
    qtouch_init();
    common_main();
    // dev convenience
    // if (memory_is_seeded()) { memory_reset_hww(); }
    workflow_set_interface_functions(&_workflow_interface_functions);
    workflow_change_state(WORKFLOW_STATE_CHOOSE_ORIENTATION);
    ui_screen_process(NULL);
}
