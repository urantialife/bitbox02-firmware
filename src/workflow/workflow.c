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

#include "attestation.h"
#include "password.h"
#include "unlock.h"
#include "workflow.h"

#include <hardfault.h>
#include <hww.h>
#include <sd.h>
#include <ui/components/ui_components.h>
#include <ui/screen_stack.h>
#include <usb/usb.h>
#include <util.h>

static workflow_interface_functions_t* _interface_functions = NULL;
void workflow_set_interface_functions(workflow_interface_functions_t* ifs)
{
    _interface_functions = ifs;
}

workflow_interface_functions_t* workflow_get_interface_functions(void)
{
    return _interface_functions;
}

static void _confirm_dismiss(component_t* component)
{
    (void)component;
    ui_screen_stack_switch(waiting_create());
}

void workflow_confirm_dismiss(const char* title, const char* body)
{
    ui_screen_stack_switch(confirm_create(title, body, _confirm_dismiss, NULL));
}

static void _select_orientation_done(bool upside_down)
{
    if (upside_down) {
        screen_rotate();
    }
    component_t* show_logo = show_logo_create(workflow_start, 0);
    ui_screen_stack_switch(show_logo);
}

void workflow_start(void)
{
    usb_start(hww_setup);
    ui_screen_stack_pop_all();
    ui_screen_stack_push(info_centered_create("See the BitBox App", NULL));
}

void workflow_change_state(workflow_state_t state)
{
    switch (state) {
    case WORKFLOW_STATE_CHOOSE_ORIENTATION: {
        _select_orientation_done(false);
        break;
        component_t* select_orientation = orientation_arrows_create(_select_orientation_done);
        ui_screen_stack_switch(select_orientation);
        break;
    }
    default:
        Abort("invalid state");
        break;
    }
}
