/**************************************************************************/
/*  domain.h                                                              */
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

// SPDX-FileCopyrightText: 2021 University of Maryland
// SPDX-License-Identifier: BSD-3-Clause-Clear
// Author: Dana Nau <nau@umd.edu>, July 7, 2021

#include "multigoal.h"

#include "core/variant/typed_array.h"

class PlannerPlan;
class PlannerDomain : public Resource {
	GDCLASS(PlannerDomain, Resource);
	friend PlannerPlan;

private:
	Dictionary action_dictionary;
	Dictionary task_method_dictionary;
	Dictionary unigoal_method_dictionary;
	TypedArray<Callable> multigoal_method_list;

public:
	PlannerDomain();

public:
	void add_actions(TypedArray<Callable> p_actions);
	void add_task_methods(String p_task_name, TypedArray<Callable> p_methods);
	void add_unigoal_methods(String p_task_name, TypedArray<Callable> p_methods);
	void add_multigoal_methods(TypedArray<Callable> p_methods);

public:
	static Variant method_verify_goal(Dictionary p_state, String p_method, String p_state_var, String p_arguments, Variant p_desired_values, int p_depth, int verbose);

protected:
	static void _bind_methods();
};
