from domain import *
from logic_operator import model_action_mapping
from pysmt.shortcuts import *
from ast import literal_eval as make_tuple
from abstraction  import add_variable_by_type


translation_value_map = dict()

def read_trace(file_name):
    with open(file_name, 'r') as trace_file:
        actions = []
        traces = trace_file.readlines()
        instate = None
        for trace in traces:
            res, out = parse_step(trace, instate)
            if res is not None:
                actions.append(res)
            if out is not None:
                instate = out

        return actions



def parse_tuple(string):
    clean_up = string.strip()
    if not( clean_up.startswith('(') and clean_up.endswith(')')):
        return None
    else:
        clean_up = clean_up[1:-1]
        res = clean_up.split(",")
        return tuple([item.strip() for item in res])


def parse_step(step_line, target):
    try:
        in_state, info, out_state = make_tuple(step_line)
        if (target is not None and int(in_state) != target):
            return None, target
        format_step = info.split("!IDS_OF")
        step_info = dict()
        attribute_ordering = []
        first_time = True
        for key_value in format_step:
            try:
                k_value = key_value.strip()
                key, value = parse_tuple(k_value)
                step_info[key] = value
                attribute_ordering.append(key)
            except:
                if first_time:
                    model_name = key_value
                    first_time = False
                continue

        if "ACTION" in step_info.keys():
            action = create_action(step_info)
            model_action_mapping[type(action).action_name] = (model_name, attribute_ordering)
            return action, int(out_state)
        else:
            return None, int(out_state)
    except:
        return None, None

def match_without_case(target, collection):
    for col in collection:
        if col.upper() == target.upper():
            return col

    return None


def create_action(step_info):
    action_name = step_info.get("ACTION")
    action_name = match_without_case(action_name, ACTION_MAP.keys())
    if action_name is not None:
        Action= ACTION_MAP.get(action_name)
        action = Action(permanent=False)
        for key, value in step_info.items():
            #if we have a specified argument
            key = match_without_case(key, Action.index_map.keys())
            if key is not None:
                if key == "time":
                    value = Int(int(value))
                if key == "permission":
                    value = Int(int(value))
                else:
                    value = read_argument_value(type(action).args_to_type.get(key), value)
                setattr(action, key, value)
                add_variable_by_type(type(action).args_to_type.get(key), value)
        action.presence = TRUE()
        return action
    else:
        return

def read_argument_value(value_type, value):
    values = translation_value_map.get(value_type, None)
    if values is None:
        values = dict()
        translation_value_map[value_type] = values

    translated_value = values.get(value, None)
    if translated_value is None:
        translated_value = Int(len(list(values.keys())))
        values[value] = translated_value
    return translated_value
