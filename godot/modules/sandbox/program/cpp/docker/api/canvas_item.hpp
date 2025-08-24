/**************************************************************************/
/*  canvas_item.hpp                                                       */
/**************************************************************************/
/*                         This file is part of:                          */
/*                             GODOT ENGINE                               */
/*                        https://godotengine.org                         */
/**************************************************************************/
/* Copyright (c) 2014-present Godot Engine contributors (see AUTHORS.md). */
/* Copyright (c) 2007-2014 Juan Linietsky, Ariel Manzur.                  */
/*                                                                        */
/* Permission is hereby granted, free of charge, to any person obtaining  */
/* a copy of this software and associated documentation files (the        */
/* "Software"), to deal in the Software without restriction, including    */
/* without limitation the rights to use, copy, modify, merge, publish,    */
/* distribute, sublicense, and/or sell copies of the Software, and to     */
/* permit persons to whom the Software is furnished to do so, subject to  */
/* the following conditions:                                              */
/*                                                                        */
/* The above copyright notice and this permission notice shall be         */
/* included in all copies or substantial portions of the Software.        */
/*                                                                        */
/* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,        */
/* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF     */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. */
/* IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY   */
/* CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,   */
/* TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE      */
/* SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.                 */
/**************************************************************************/

#pragma once
#include "dictionary.hpp"
#include "node.hpp"
#include "rid.hpp"
#include "transform2d.hpp"

struct CanvasItem : public Node {
	using Node::Node;
	PROPERTY(visible, bool);
	PROPERTY(modulate, Color);
	PROPERTY(self_modulate, Color);
	PROPERTY(show_behind_parent, bool);
	PROPERTY(top_level, bool);
	PROPERTY(clip_children, int64_t);
	PROPERTY(light_mask, int64_t);
	PROPERTY(visibility_layer, int64_t);
	PROPERTY(z_index, int64_t);
	PROPERTY(z_as_relative, bool);
	PROPERTY(y_sort_enabled, bool);
	PROPERTY(texture_filter, int64_t);
	PROPERTY(texture_repeat, int64_t);
	PROPERTY(material, Object);
	PROPERTY(use_parent_material, bool);
	VMETHOD(_draw);
	VMETHOD(_top_level_raise_self);
	VMETHOD(_edit_set_state);
	METHOD(Dictionary, _edit_get_state);
	VMETHOD(_edit_set_position);
	METHOD(Vector2, _edit_get_position);
	VMETHOD(_edit_set_scale);
	METHOD(Vector2, _edit_get_scale);
	VMETHOD(_edit_set_rect);
	METHOD(Rect2, _edit_get_rect);
	METHOD(bool, _edit_use_rect);
	VMETHOD(_edit_set_rotation);
	METHOD(double, _edit_get_rotation);
	METHOD(bool, _edit_use_rotation);
	VMETHOD(_edit_set_pivot);
	METHOD(Vector2, _edit_get_pivot);
	METHOD(bool, _edit_use_pivot);
	METHOD(Transform2D, _edit_get_transform);
	METHOD(::RID, get_canvas_item);
	METHOD(void, set_visible);
	METHOD(bool, is_visible);
	METHOD(bool, is_visible_in_tree);
	VMETHOD(show);
	VMETHOD(hide);
	VMETHOD(queue_redraw);
	VMETHOD(move_to_front);
	METHOD(void, set_as_top_level);
	METHOD(bool, is_set_as_top_level);
	METHOD(void, set_light_mask);
	METHOD(int64_t, get_light_mask);
	METHOD(void, set_modulate);
	METHOD(Color, get_modulate);
	METHOD(void, set_self_modulate);
	METHOD(Color, get_self_modulate);
	METHOD(void, set_z_index);
	METHOD(int64_t, get_z_index);
	METHOD(void, set_z_as_relative);
	METHOD(bool, is_z_relative);
	METHOD(void, set_y_sort_enabled);
	METHOD(bool, is_y_sort_enabled);
	METHOD(void, set_draw_behind_parent);
	METHOD(bool, is_draw_behind_parent_enabled);
	VMETHOD(draw_line);
	VMETHOD(draw_dashed_line);
	VMETHOD(draw_polyline);
	VMETHOD(draw_polyline_colors);
	VMETHOD(draw_arc);
	VMETHOD(draw_multiline);
	VMETHOD(draw_multiline_colors);
	VMETHOD(draw_rect);
	VMETHOD(draw_circle);
	VMETHOD(draw_texture);
	VMETHOD(draw_texture_rect);
	VMETHOD(draw_texture_rect_region);
	VMETHOD(draw_msdf_texture_rect_region);
	VMETHOD(draw_lcd_texture_rect_region);
	VMETHOD(draw_style_box);
	VMETHOD(draw_primitive);
	VMETHOD(draw_polygon);
	VMETHOD(draw_colored_polygon);
	VMETHOD(draw_string);
	VMETHOD(draw_multiline_string);
	VMETHOD(draw_string_outline);
	VMETHOD(draw_multiline_string_outline);
	VMETHOD(draw_char);
	VMETHOD(draw_char_outline);
	VMETHOD(draw_mesh);
	VMETHOD(draw_multimesh);
	VMETHOD(draw_set_transform);
	VMETHOD(draw_set_transform_matrix);
	VMETHOD(draw_animation_slice);
	VMETHOD(draw_end_animation);
	METHOD(Transform2D, get_transform);
	METHOD(Transform2D, get_global_transform);
	METHOD(Transform2D, get_global_transform_with_canvas);
	METHOD(Transform2D, get_viewport_transform);
	METHOD(Rect2, get_viewport_rect);
	METHOD(Transform2D, get_canvas_transform);
	METHOD(Transform2D, get_screen_transform);
	METHOD(Vector2, get_local_mouse_position);
	METHOD(Vector2, get_global_mouse_position);
	METHOD(::RID, get_canvas);
	METHOD(Object, get_canvas_layer_node);
	METHOD(Object, get_world_2d);
	METHOD(void, set_material);
	METHOD(Object, get_material);
	METHOD(void, set_use_parent_material);
	METHOD(bool, get_use_parent_material);
	METHOD(void, set_notify_local_transform);
	METHOD(bool, is_local_transform_notification_enabled);
	METHOD(void, set_notify_transform);
	METHOD(bool, is_transform_notification_enabled);
	VMETHOD(force_update_transform);
	METHOD(Vector2, make_canvas_position_local);
	METHOD(Object, make_input_local);
	METHOD(void, set_visibility_layer);
	METHOD(int64_t, get_visibility_layer);
	METHOD(void, set_visibility_layer_bit);
	METHOD(bool, get_visibility_layer_bit);
	METHOD(void, set_texture_filter);
	METHOD(int64_t, get_texture_filter);
	METHOD(void, set_texture_repeat);
	METHOD(int64_t, get_texture_repeat);
	METHOD(void, set_clip_children_mode);
	METHOD(int64_t, get_clip_children_mode);
	static constexpr int64_t NOTIFICATION_TRANSFORM_CHANGED = 2000;
	static constexpr int64_t NOTIFICATION_LOCAL_TRANSFORM_CHANGED = 35;
	static constexpr int64_t NOTIFICATION_DRAW = 30;
	static constexpr int64_t NOTIFICATION_VISIBILITY_CHANGED = 31;
	static constexpr int64_t NOTIFICATION_ENTER_CANVAS = 32;
	static constexpr int64_t NOTIFICATION_EXIT_CANVAS = 33;
	static constexpr int64_t NOTIFICATION_WORLD_2D_CHANGED = 36;
	static constexpr int64_t TEXTURE_FILTER_PARENT_NODE = 0;
	static constexpr int64_t TEXTURE_FILTER_NEAREST = 1;
	static constexpr int64_t TEXTURE_FILTER_LINEAR = 2;
	static constexpr int64_t TEXTURE_FILTER_NEAREST_WITH_MIPMAPS = 3;
	static constexpr int64_t TEXTURE_FILTER_LINEAR_WITH_MIPMAPS = 4;
	static constexpr int64_t TEXTURE_FILTER_NEAREST_WITH_MIPMAPS_ANISOTROPIC = 5;
	static constexpr int64_t TEXTURE_FILTER_LINEAR_WITH_MIPMAPS_ANISOTROPIC = 6;
	static constexpr int64_t TEXTURE_FILTER_MAX = 7;
	static constexpr int64_t TEXTURE_REPEAT_PARENT_NODE = 0;
	static constexpr int64_t TEXTURE_REPEAT_DISABLED = 1;
	static constexpr int64_t TEXTURE_REPEAT_ENABLED = 2;
	static constexpr int64_t TEXTURE_REPEAT_MIRROR = 3;
	static constexpr int64_t TEXTURE_REPEAT_MAX = 4;
	static constexpr int64_t CLIP_CHILDREN_DISABLED = 0;
	static constexpr int64_t CLIP_CHILDREN_ONLY = 1;
	static constexpr int64_t CLIP_CHILDREN_AND_DRAW = 2;
	static constexpr int64_t CLIP_CHILDREN_MAX = 3;
};
