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

#include <hardfault.h>
#include <touch/gestures.h>

#include "ui_components.h"

#include "../event.h"
#include "screen.h"
#include "scroll_through_all_variants.h"

// the rate at which the _update_positions function is called
static const uint8_t UPDATE_RATE = 30;
// keeps track of the times that the _slide function is called, to trigger the call of
// _update_positions.
static uint8_t _update_iteration = 0;

/**
 * Scroll-through data.
 */
typedef struct {
    const char** words;
    component_t** labels;
    uint8_t length;
    uint8_t index;
    char index_str[4];
    component_t* index_label;
    bool show_index;
    int32_t diff_to_middle;
    void (*callback)(uint8_t);
    component_t* right_bottom;
    void (*continue_on_last)(void);
} scroll_through_all_variants_data_t;

static const uint8_t part_width = 15;

static void _display_index(component_t* scroll_through_all_variants)
{
    scroll_through_all_variants_data_t* data =
        (scroll_through_all_variants_data_t*)scroll_through_all_variants->data;
    snprintf(data->index_str, sizeof(data->index_str), "%02u", (data->index + 1));
    label_update(data->index_label, data->index_str);
}

static void _update_positions(component_t* scroll_through_all_variants, int32_t velocity)
{
    scroll_through_all_variants_data_t* data =
        (scroll_through_all_variants_data_t*)scroll_through_all_variants->data;
    // init to very high number (2^31 - 1).
    int32_t min_diff_to_middle = 2147483647;
    for (int i = 0; i < data->length; i++) {
        ui_util_position_left_center_offset(
            scroll_through_all_variants,
            data->labels[i],
            data->labels[i]->position.left + velocity);

        int32_t diff_to_middle = data->labels[i]->position.left +
                                 data->labels[i]->dimension.width / 2 - SCREEN_WIDTH / 2;
        if (abs(diff_to_middle) < min_diff_to_middle) {
            min_diff_to_middle = abs(diff_to_middle);
            data->index = i;
            data->diff_to_middle = diff_to_middle;
        }
    }
    if (data->show_index) {
        _display_index(scroll_through_all_variants);
    }
}

static void _init_positions(component_t* scroll_through_all_variants)
{
    scroll_through_all_variants_data_t* data =
        (scroll_through_all_variants_data_t*)scroll_through_all_variants->data;
    int32_t middle_pos = SCREEN_WIDTH / 2;
    for (int i = 0; i < data->length; i++) {
        int32_t current_pos = middle_pos - data->labels[i]->dimension.width / 2;
        ui_util_position_left_center_offset(
            scroll_through_all_variants, data->labels[i], current_pos);
        if (i + 1 < data->length) {
            middle_pos = middle_pos + SCREEN_WIDTH / 2 - part_width +
                         data->labels[i + 1]->dimension.width / 2;
        }
    }
}

/**
 * Moves to the previous or next word in the words list.
 */
static void _slide(gestures_slider_data_t* gestures_slider_data, component_t* component)
{
    if (_update_iteration % UPDATE_RATE == 0) {
        if (abs(gestures_slider_data->velocity) > 0) {
            _update_positions(component, gestures_slider_data->velocity / 2);
        }
        _update_iteration = 0;
    }
    _update_iteration++;
}

// animate quicker and snap to the item that is most visible. Update index.
static void _slide_release(gestures_slider_data_t* gestures_slider_data, component_t* component)
{
    (void)gestures_slider_data;
    scroll_through_all_variants_data_t* data = (scroll_through_all_variants_data_t*)component->data;
    _update_positions(component, -1 * data->diff_to_middle);
}

static void _back(component_t* component)
{
    scroll_through_all_variants_data_t* data =
        (scroll_through_all_variants_data_t*)component->parent->data;
    uint8_t new_index = data->index > 0 ? data->index - 1 : data->index;
    int32_t diff_to_middle = (data->labels[new_index]->position.left +
                              data->labels[new_index]->dimension.width / 2 - SCREEN_WIDTH / 2) *
                             -1;
    _update_positions(component->parent, diff_to_middle);
}

static void _forward(component_t* component)
{
    scroll_through_all_variants_data_t* data =
        (scroll_through_all_variants_data_t*)component->parent->data;
    uint8_t new_index = data->index < (data->length - 1) ? data->index + 1 : data->index;
    int32_t diff_to_middle = (data->labels[new_index]->position.left +
                              data->labels[new_index]->dimension.width / 2 - SCREEN_WIDTH / 2) *
                             -1;
    _update_positions(component->parent, diff_to_middle);
}

static void _continue(component_t* button)
{
    scroll_through_all_variants_data_t* data =
        (scroll_through_all_variants_data_t*)button->parent->data;
    data->continue_on_last();
}

static void _select(component_t* button)
{
    scroll_through_all_variants_data_t* data =
        (scroll_through_all_variants_data_t*)button->parent->data;
    data->callback(data->index);
}

/**
 * Render the UI component.
 */
static void _render(component_t* component)
{
    scroll_through_all_variants_data_t* data = (scroll_through_all_variants_data_t*)component->data;

    if (data->index == data->length - 1 && data->continue_on_last != NULL) {
        button_update(data->right_bottom, "Continue", _continue);
    }
    UG_S16 x1 = data->labels[data->index]->position.left - 1;
    UG_S16 x2 = x1 + data->labels[data->index]->dimension.width - 1;
    UG_S16 y =
        data->labels[data->index]->position.top + data->labels[data->index]->dimension.height + 2;
    UG_DrawLine(x1, y, x2, y, screen_front_color);

    ui_util_component_render_subcomponents(component);
}

static void _on_event(const event_t* event, component_t* component)
{
    gestures_slider_data_t* slider_data = (gestures_slider_data_t*)event->data;
    switch (event->id) {
    case EVENT_TOP_SLIDE:
    case EVENT_BOTTOM_SLIDE:
        _slide(slider_data, component);
        break;
    case EVENT_TOP_SLIDE_RELEASED:
    case EVENT_BOTTOM_SLIDE_RELEASED:
        _slide_release(slider_data, component);
        break;
    default:
        break;
    }
}

/**
 * Clean-up the component.
 */
static void _cleanup(component_t* component)
{
    scroll_through_all_variants_data_t* data = (scroll_through_all_variants_data_t*)component->data;
    free(data->labels);
    // component and component data are cleaned up in ui_util_component_cleanup.
    ui_util_component_cleanup(component);
}

/********************************** Component Functions **********************************/

/**
 * Collects all component functions.
 */
static const component_functions_t _component_functions = {
    .cleanup = _cleanup,
    .render = _render,
    .on_event = _on_event,
};

/********************************** Create Instance **********************************/

/**
 * Creates a scroll through list that renders the current word in the center and parts of the words
 * before and after on the left and right.
 * @param[in] words The words that are displayed on the screen, and through which you can slide
 * through.
 * @param[in] callback If specified, the callback will be called if the user selects a word. The
 * parameter is the index of the selected word.
 * @param[in] length The word list length.
 * @param[in] show_index If true, displays the index of the current word (starting at 1).
 * @param[in] parent The parent component.
 */
component_t* scroll_through_all_variants_create(
    const char** words,
    void (*callback)(uint8_t),
    const uint8_t length,
    bool show_index,
    void (*continue_on_last)(void),
    component_t* parent)
{
    component_t** labels = malloc(sizeof(component_t*) * length);
    if (!labels) {
        Abort("Error: malloc scroll through labels");
    }
    scroll_through_all_variants_data_t* data = malloc(sizeof(scroll_through_all_variants_data_t));
    if (!data) {
        Abort("Error: malloc scroll through data");
    }
    memset(data, 0, sizeof(scroll_through_all_variants_data_t));

    component_t* scroll_through_all_variants = malloc(sizeof(component_t));
    if (!scroll_through_all_variants) {
        Abort("Error: malloc scroll through");
    }
    memset(scroll_through_all_variants, 0, sizeof(component_t));

    scroll_through_all_variants->parent = parent;
    scroll_through_all_variants->f = &_component_functions;

    scroll_through_all_variants->dimension.width = SCREEN_WIDTH;
    scroll_through_all_variants->dimension.height = SCREEN_HEIGHT;

    data->labels = labels;
    data->words = words;
    data->callback = callback;
    data->length = length;
    data->index = 0;
    data->show_index = show_index;

    scroll_through_all_variants->data = data;

    for (int i = 0; i < length; i++) {
        component_t* label = label_create(words[i], NULL, CENTER, scroll_through_all_variants);
        ui_util_add_sub_component(scroll_through_all_variants, label);
        labels[i] = label;
    }
    if (show_index) {
        data->index_label = label_create("01", NULL, CENTER_BOTTOM, scroll_through_all_variants);
        _display_index(scroll_through_all_variants);
        ui_util_add_sub_component(scroll_through_all_variants, data->index_label);
    }
    ui_util_add_sub_component(
        scroll_through_all_variants,
        button_create("", top_slider, 0, _back, scroll_through_all_variants));
    ui_util_add_sub_component(
        scroll_through_all_variants,
        button_create("", top_slider, SCREEN_WIDTH, _forward, scroll_through_all_variants));
    ui_util_add_sub_component(
        scroll_through_all_variants,
        button_create("", bottom_slider, 0, _back, scroll_through_all_variants));

    data->right_bottom =
        button_create("", bottom_slider, SCREEN_WIDTH, _forward, scroll_through_all_variants);
    data->continue_on_last = continue_on_last;
    ui_util_add_sub_component(scroll_through_all_variants, data->right_bottom);

    if (callback != NULL) {
        ui_util_add_sub_component(
            scroll_through_all_variants,
            button_create(
                "", bottom_slider, SCREEN_WIDTH / 2, _select, scroll_through_all_variants));
    }
    _init_positions(scroll_through_all_variants);
    return scroll_through_all_variants;
}
