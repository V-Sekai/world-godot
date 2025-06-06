/**************************************************************************/
/*  plan.cpp                                                              */
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

#include "plan.h"

#include "core/variant/callable.h"
#include "core/variant/typed_array.h"

#include "modules/goal_task_planner/domain.h"
#include "modules/goal_task_planner/multigoal.h"

int PlannerPlan::get_verbose() const {
	return verbose;
}

TypedArray<PlannerDomain> PlannerPlan::get_domains() const {
	return domains;
}

Ref<PlannerDomain> PlannerPlan::get_current_domain() const {
	return current_domain;
}

void PlannerPlan::set_verbose(int p_verbose) {
	verbose = p_verbose;
}

void PlannerPlan::set_domains(TypedArray<PlannerDomain> p_domain) {
	domains = p_domain;
}

Variant PlannerPlan::_apply_action_and_continue(Dictionary p_state, Array p_first_task, Array p_todo_list, Array p_plan, int p_depth) {
	Callable action = current_domain->action_dictionary[p_first_task[0]];

	if (verbose >= 2) {
		Array action_info = p_first_task.slice(1);
		action_info.insert(0, action.get_method());
		print_line("Depth: " + itos(p_depth) + ", Action: " + _item_to_string(action_info));
	}

	Array arguments = p_first_task.slice(1);
	arguments.insert(0, p_state);
	Variant new_state = action.callv(arguments);

	if (new_state) {
		if (verbose >= 3) {
			print_line("Intermediate computation: Action applied successfully.");
			print_line("New state: " + String(new_state));
		}
		Array new_plan = p_plan;
		new_plan.push_back(p_first_task);
		return _seek_plan(new_state, p_todo_list, new_plan, p_depth + 1);
	}

	if (verbose >= 3) {
		print_line("Intermediate computation: Failed to apply action. The new state is not valid.");
		print_line("New state: " + String(new_state));
		print_line("Task: ");
		for (int i = 0; i < p_first_task.size(); ++i) {
			print_line(String(p_first_task[i]));
			print_line("State: " + _item_to_string(p_state));
		}

		if (verbose >= 2) {
			Array action_info = p_first_task.slice(1);
			action_info.insert(0, action.get_method());
			ERR_PRINT("Recursive call: Not applicable action: " + _item_to_string(action_info));
		}
	}
	return false;
}

Variant PlannerPlan::_refine_task_and_continue(const Dictionary p_state, const Array p_task1, const Array p_todo_list, const Array p_plan, const int p_depth) {
	Array relevant = current_domain->task_method_dictionary[p_task1[0]];
	if (verbose >= 3) {
		print_line("Depth: " + itos(p_depth) + ", Task " + _item_to_string(p_task1) + ", Todo List " + _item_to_string(p_todo_list) + ", Plan " + _item_to_string(p_plan));
	}
	for (int i = 0; i < relevant.size(); i++) {
		Callable method = relevant[i];
		Array arguments;
		arguments.push_back(p_state);
		Array argument_slices = p_task1.slice(1);
		arguments.append_array(argument_slices);
		if (verbose >= 2) {
			print_line("Depth: " + itos(p_depth) + ", Trying method: " + _item_to_string(method));
		}
		Variant result = method.callv(arguments);
		if (result.is_array()) {
			Array subgoals = result;
			Array todo_list;
			if (!subgoals.is_empty()) {
				todo_list.append_array(subgoals);
			}
			if (!p_todo_list.is_empty()) {
				todo_list.append_array(p_todo_list);
			}
			Variant plan = _seek_plan(p_state, todo_list, p_plan, p_depth + 1);
			if (plan.is_array()) {
				return plan;
			}
		} else {
			if (verbose >= 3) {
				ERR_PRINT("Not applicable");
			}
		}
	}

	if (verbose >= 2) {
		ERR_PRINT("Recursive call: Failed to achieve task: " + _item_to_string(p_task1));
	}

	return false;
}

Variant PlannerPlan::_refine_multigoal_and_continue(const Dictionary p_state, const Ref<PlannerMultigoal> p_first_goal, const Array p_todo_list, const Array p_plan, const int p_depth) {
	if (verbose >= 3) {
		print_line("Depth: " + itos(p_depth) + ", Multigoal: " + p_first_goal->get_name() + ": " + _item_to_string(p_first_goal));
	}

	Array relevant = current_domain->multigoal_method_list;

	if (verbose >= 3) {
		Array string_array;
		for (int i = 0; i < relevant.size(); i++) {
			print_line(String("Methods ") + String(relevant[i].call("get_method")));
		}
	}
	Array todo_list = p_todo_list;
	for (int i = 0; i < relevant.size(); i++) {
		if (verbose >= 2) {
			print_line("Depth: " + itos(p_depth) + ", Trying method: " + String(relevant[i].call("get_method")) + ": ");
		}
		Callable callable = relevant[i];
		Variant result = callable.call(p_state, p_first_goal);
		if (result.is_array()) {
			Array subgoals = result;
			Array subtodo_list;
			if (verbose >= 3) {
				print_line("Intermediate computation: Method applicable.");
				print_line("Depth: " + itos(p_depth) + ", Subgoals: " + _item_to_string(subgoals));
			}
			if (!subgoals.is_empty()) {
				subtodo_list.append_array(subgoals);
			}
			if (verify_goals) {
				subtodo_list.push_back(varray("_verify_mg", callable.get_method(), p_first_goal, p_depth, verbose));
			}
			if (!p_todo_list.is_empty()) {
				subtodo_list.append_array(p_todo_list);
			}
			todo_list.clear();
			todo_list = subtodo_list;
			Variant plan = _seek_plan(p_state, todo_list, p_plan, p_depth + 1);
			if (plan.is_array()) {
				return plan;
			}
		}
	}

	if (verbose >= 2) {
		ERR_PRINT("Recursive call: Failed to achieve multigoal: " + _item_to_string(p_first_goal));
	}

	return false;
}

Variant PlannerPlan::_refine_unigoal_and_continue(const Dictionary p_state, const Array p_goal1, const Array p_todo_list, const Array p_plan, const int p_depth) {
	if (verbose >= 3) {
		String goals_list = vformat("Depth: %d, Goals: %s", p_depth, _item_to_string(p_goal1));
	}

	String state_variable_name = p_goal1[0];
	String argument = p_goal1[1];
	Variant value = p_goal1[2];

	Dictionary state_variable = p_state[state_variable_name];

	if (state_variable[argument] == value) {
		if (verbose >= 3) {
			print_line("Intermediate computation: Goal already achieved.");
		}
		return _seek_plan(p_state, p_todo_list, p_plan, p_depth + 1);
	}

	Array relevant = current_domain->unigoal_method_dictionary[state_variable_name];
	if (verbose >= 3) {
		print_line("Methods: " + _item_to_string(relevant));
	}
	Array todo_list = p_todo_list;
	for (int i = 0; i < relevant.size(); i++) {
		Callable method = relevant[i];
		if (verbose >= 2) {
			print_line("Depth: " + itos(p_depth) + ", Trying method: " + _item_to_string(method));
		}
		Variant result = method.call(p_state, argument, value);
		if (result.is_array()) {
			Array subgoals = result;
			Array subtodo_list;
			if (!subgoals.is_empty()) {
				subtodo_list.append_array(subgoals);
			}
			if (verify_goals) {
				subtodo_list.push_back(varray("_verify_g", method.get_method(), state_variable_name, argument, value, p_depth, verbose));
			}
			if (!todo_list.is_empty()) {
				subtodo_list.append_array(todo_list);
			}
			todo_list.clear();
			todo_list = subtodo_list;
			if (verbose >= 3) {
				print_line("Depth: " + itos(p_depth) + ", Seeking todo list " + _item_to_string(todo_list));
			}
			Variant plan = _seek_plan(p_state, todo_list, p_plan, p_depth + 1);
			if (plan.is_array()) {
				return plan;
			}
		} else {
			if (verbose >= 3) {
				ERR_PRINT("Not applicable");
			}
		}
	}

	if (verbose >= 2) {
		ERR_PRINT(vformat("Recursive call: Failed to achieve goal: %s", _item_to_string(p_goal1)));
	}

	return false;
}

Variant PlannerPlan::find_plan(Dictionary p_state, Array p_todo_list) {
	if (verbose >= 1) {
		print_line("verbose=" + itos(verbose) + ":");
		print_line("    state = " + _item_to_string(p_state) + "\n    todo_list = " + _item_to_string(p_todo_list));
	}

	Variant result = _seek_plan(p_state, p_todo_list, Array(), 0);

	if (verbose >= 1) {
		print_line("result = " + _item_to_string(result));
	}

	return result;
}

Variant PlannerPlan::_seek_plan(Dictionary p_state, Array p_todo_list, Array p_plan, int p_depth) {
	if (verbose >= 2) {
		print_line("Depth: " + itos(p_depth) + ", Todo List: " + _item_to_string(p_todo_list));
	}

	if (p_todo_list.is_empty()) {
		if (verbose >= 3) {
			print_line("Depth: " + itos(p_depth) + " no more tasks or goals, return plan: " + _item_to_string(p_plan));
		}
		return p_plan;
	}
	Variant todo_item = p_todo_list.front();
	p_todo_list = p_todo_list.slice(1);
	if (Object::cast_to<PlannerMultigoal>(todo_item)) {
		return _refine_multigoal_and_continue(p_state, todo_item, p_todo_list, p_plan, p_depth);
	} else if (todo_item.is_array()) {
		Array item = todo_item;
		Dictionary actions = current_domain->action_dictionary;
		Dictionary tasks = current_domain->task_method_dictionary;
		Dictionary unigoals = current_domain->unigoal_method_dictionary;
		Variant item_name = item.front();
		if (actions.has(item_name)) {
			return _apply_action_and_continue(p_state, item, p_todo_list, p_plan, p_depth);
		} else if (tasks.has(item_name)) {
			return _refine_task_and_continue(p_state, item, p_todo_list, p_plan, p_depth);
		} else if (unigoals.has(item_name)) {
			return _refine_unigoal_and_continue(p_state, item, p_todo_list, p_plan, p_depth);
		}
	}
	return false;
}

String PlannerPlan::_item_to_string(Variant p_item) {
	return String(p_item);
}

Dictionary PlannerPlan::run_lazy_lookahead(Dictionary p_state, Array p_todo_list, int p_max_tries) {
	if (verbose >= 1) {
		print_line(vformat("run_lazy_lookahead: verbose = %s, max_tries = %s", verbose, p_max_tries));
		print_line(vformat("Initial state: %s", p_state.keys()));
		print_line(vformat("To do: %s", p_todo_list));
	}

	Dictionary ordinals;
	ordinals[1] = "st";
	ordinals[2] = "nd";
	ordinals[3] = "rd";

	for (int tries = 1; tries <= p_max_tries; tries++) {
		if (verbose >= 1) {
			print_line(vformat("run_lazy_lookahead: %sth call to find_plan: %s", tries, ordinals.get(tries, "")));
		}

		Variant plan = find_plan(p_state, p_todo_list);
		if (plan == Variant(false)) {
			if (verbose >= 1) {
				ERR_PRINT(vformat("run_lazy_lookahead: find_plan has failed after %s calls.", tries));
			}
			return p_state;
		}

		if (plan.is_array() && Array(plan).is_empty()) {
			if (verbose >= 1) {
				print_line(vformat("run_lazy_lookahead: Empty plan => success\nafter %s calls to find_plan.", tries));
			}
			if (verbose >= 2) {
				print_line(vformat("run_lazy_lookahead: final state %s", p_state));
			}
			return p_state;
		}

		if (plan.is_array()) {
			Array action_list = plan;
			for (int i = 0; i < action_list.size(); i++) {
				Array action = action_list[i];
				Callable action_name = current_domain->action_dictionary[action[0]];
				if (verbose >= 1) {
					String action_arguments;
					Array actions = action.slice(1, action.size());
					for (Variant element : actions) {
						action_arguments += String(" ") + String(element);
					}
					print_line(vformat("run_lazy_lookahead: Task: %s, %s", action_name.get_method(), action_arguments));
				}

				Dictionary new_state = _apply_task_and_continue(p_state, action_name, action.slice(1, action.size()));
				if (!new_state.is_empty()) {
					if (verbose >= 2) {
						print_line(new_state);
					}
					p_state = new_state;
				} else {
					if (verbose >= 1) {
						ERR_PRINT(vformat("run_lazy_lookahead: WARNING: action %s failed; will call find_plan.", action_name));
					}
					break;
				}
			}
		}

		if (verbose >= 1 && !p_state.is_empty()) {
			print_line("RunLazyLookahead> Plan ended; will call find_plan again.");
		}
	}

	if (verbose >= 1) {
		ERR_PRINT("run_lazy_lookahead: Too many tries, giving up.");
	}
	if (verbose >= 2) {
		print_line(vformat("run_lazy_lookahead: final state %s", p_state));
	}

	return p_state;
}

Variant PlannerPlan::_apply_task_and_continue(Dictionary p_state, Callable p_command, Array p_arguments) {
	if (verbose >= 3) {
		print_line(vformat("_apply_task_and_continue %s, args = %s", p_command.get_method(), _item_to_string(p_arguments)));
	}
	Array argument;
	argument.push_back(p_state);
	argument.append_array(p_arguments);
	Variant next_state = p_command.callv(argument);
	if (!next_state) {
		if (verbose >= 3) {
			print_line(vformat("Not applicable command %s", argument));
		}
		return false;
	}

	if (verbose >= 3) {
		print_line("Applied");
		print_line(next_state);
	}
	return next_state;
}

void PlannerPlan::_bind_methods() {
	ClassDB::bind_method(D_METHOD("get_verify_goals"), &PlannerPlan::get_verify_goals);
	ClassDB::bind_method(D_METHOD("set_verify_goals", "value"), &PlannerPlan::set_verify_goals);
	ADD_PROPERTY(PropertyInfo(Variant::BOOL, "verify_goals"), "set_verify_goals", "get_verify_goals");

	ClassDB::bind_method(D_METHOD("get_verbose"), &PlannerPlan::get_verbose);
	ClassDB::bind_method(D_METHOD("set_verbose", "level"), &PlannerPlan::set_verbose);
	ADD_PROPERTY(PropertyInfo(Variant::INT, "verbose"), "set_verbose", "get_verbose");

	ClassDB::bind_method(D_METHOD("get_domains"), &PlannerPlan::get_domains);
	ClassDB::bind_method(D_METHOD("set_domains", "domain"), &PlannerPlan::set_domains);
	ADD_PROPERTY(PropertyInfo(Variant::ARRAY, "domains", PROPERTY_HINT_RESOURCE_TYPE, "Domain"), "set_domains", "get_domains");

	ClassDB::bind_method(D_METHOD("get_current_domain"), &PlannerPlan::get_current_domain);
	ClassDB::bind_method(D_METHOD("set_current_domain", "current_domain"), &PlannerPlan::set_current_domain);
	ADD_PROPERTY(PropertyInfo(Variant::OBJECT, "current_domain", PROPERTY_HINT_RESOURCE_TYPE, "Domain"), "set_current_domain", "get_current_domain");

	ClassDB::bind_method(D_METHOD("find_plan", "state", "todo_list"), &PlannerPlan::find_plan);
	ClassDB::bind_method(D_METHOD("run_lazy_lookahead", "state", "todo_list", "max_tries"), &PlannerPlan::run_lazy_lookahead, DEFVAL(10));
}

bool PlannerPlan::get_verify_goals() const {
	return verify_goals;
}

void PlannerPlan::set_verify_goals(bool p_value) {
	verify_goals = p_value;
}
