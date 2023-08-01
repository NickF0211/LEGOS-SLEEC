from type_constructor import create_type, create_action, create_pair_action
from random import randint
type_dict = dict()

'''
TODO: define your data type here
'''
_int = create_type("int", type_dict)
t = create_type("time", type_dict, lower_bound=0)
var = create_type("var", type_dict)
#other data types....

'''
TODO: define your data actions here: INPUT
'''
Var = create_action("Var", [("v", "var")],type_dict)
TimeStamp = create_action("TimeStamp", [("time", "time")],type_dict)


'''
TODO: record the complete list of data actions: INPUT
'''
ACTION = [TimeStamp, Var]

'''
TODO: Hidden or AUX data actions: INPUT
'''
state_action = [TimeStamp, Var]

