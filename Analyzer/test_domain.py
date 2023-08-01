from type_constructor import create_type, create_action, create_pair_action
from random import randint
type_dict = dict()

#data types
_int = create_type("int", type_dict)
pid = create_type("pid", type_dict, lower_bound=0)
tid = create_type("tid", type_dict, lower_bound=0)
amount = create_type("amount", type_dict, lower_bound=0)
time = create_type("time", type_dict, lower_bound=0)
var = create_type("var", type_dict)

#data actions
Var = create_action("Var", [("v", "var")],type_dict)
Balance = create_action("Balance", [("pid", "pid"), ("amount", "int"), ("time", "time")], type_dict)
Trans = create_action("Trans", [("sender", "pid"), ("receiver", "pid"),("tid", "tid"), ("amount", "amount"), ("time", "time")],type_dict)
Deposit = create_action("Deposit", [("pid", "pid"), ("amount", "amount"), ("time", "time")], type_dict)
Withdraw = create_action("WithDraw", [("pid", "pid"), ("amount", "amount"), ("time", "time")], type_dict)
Authorize = create_action("Authorize", [("eid", "eid"), ("tid", "tid"), ("time", "time")],type_dict)
Report = create_action("Report", [("tid", "tid"),("time", "time")],type_dict)
TimeStamp = create_action("TimeStamp", [("time", "time")],type_dict)

#these are actions that you care about
ACTION = [TimeStamp, Trans, Authorize, Report, Balance, Deposit, Withdraw, Var]

#these are hidden / auxiliary actions for reasoning
state_action = [TimeStamp, Var]

