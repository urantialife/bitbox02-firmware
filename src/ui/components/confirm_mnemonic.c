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

#include <stdio.h>
#include <string.h>

#include <hardfault.h>
#include <ui/components/ui_components.h>
#include <ui/ui_util.h>

#include "confirm_mnemonic.h"

typedef struct {
    char title[100];
} confirm_mnemonic_data_t;

/**
 * Collects all component functions.
 */
static const component_functions_t _component_functions = {
    .cleanup = ui_util_component_cleanup,
    .render = ui_util_component_render_subcomponents,
    .on_event = ui_util_on_event_noop,
};

/**
 * Creates a screen that allows to confirm the mnemonic words.
 */
component_t* confirm_mnemonic_create(
    const char** wordlist,
    uint8_t length,
    uint8_t index,
    void (*check_word)(uint8_t))
{
    confirm_mnemonic_data_t* data = malloc(sizeof(confirm_mnemonic_data_t));
    if (!data) {
        Abort("Error: malloc confirm_mnemonic data");
    }
    memset(data, 0, sizeof(confirm_mnemonic_data_t));

    component_t* confirm_mnemonic = malloc(sizeof(component_t));
    if (!confirm_mnemonic) {
        Abort("Error: malloc confirm_mnemonic");
    }
    memset(confirm_mnemonic, 0, sizeof(component_t));
    confirm_mnemonic->f = &_component_functions;
    confirm_mnemonic->data = data;

    confirm_mnemonic->dimension.width = SCREEN_WIDTH;
    confirm_mnemonic->dimension.height = SCREEN_HEIGHT;

    snprintf(data->title, 100, "%02d:", index + 1);
    ui_util_add_sub_component(
        confirm_mnemonic, label_create(data->title, NULL, LEFT_TOP, confirm_mnemonic));

    ui_util_add_sub_component(
        confirm_mnemonic,
        scroll_through_all_variants_create(
            wordlist, check_word, length, false, NULL, confirm_mnemonic));

    return confirm_mnemonic;
}
