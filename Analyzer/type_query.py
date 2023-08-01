from type_constructor import create_type, create_action
from resource_type import resource_type, consumable_resource_type

def get_action_name(action_id):
    if action_id == 1:
        return "access"
    elif action_id == 2:
        return "disclose"


type_dict = dict()
time = create_type("time", type_dict, lower_bound=0, upper_bound=10)
sid = create_type("sid", type_dict, lower_bound = 0, upper_bound = 10)
aid = create_type("aid", type_dict, lower_bound = 0, upper_bound = 10)
pid = create_type("pid", type_dict, lower_bound = 0, upper_bound = 100)
pvalue = create_type("pvalue", type_dict)
purpose = create_type("purpose", type_dict, lower_bound=0, upper_bound=5)
expertise = create_type("expertise", type_dict, lower_bound=0, upper_bound=3)
action = create_type("action", type_dict, lower_bound=1, upper_bound=2)


Collect = create_action("Collect", [("time", "time"), ("subject", "sid"),
                                    ("pid", "pid"), ("pvalue", "pvalue"), ("purpose","purpose")],type_dict)

Update = create_action("Update", [("time", "time"), ("subject", "sid"),
                                    ("pid", "pid"), ("pvalue", "pvalue")],type_dict)

Has_Expertise = create_action("Has_Expertise",  [("time", "time"),
                                                 ("expertise", "expertise"), ("purpose", "purpose")],type_dict)

Access = create_action("Access", [("time", "time"),
                                                 ("pid", "pid"), ("a1", "aid")],type_dict)

Disclose = create_action("Disclose", [("time", "time"),
                                                 ("a1", "aid"), ("pid", "pid"), ("pvalue", "pvalue"),
                                      ("a2", "aid")],type_dict)

Consent = create_action("Consent", [("time", "time"),
                                                 ("action", "action"), ("a1", "aid"), ("pid", "pid"),
                                      ("a2", "aid")], type_dict)

Authorize= create_action("Authorize", [("time", "time"),
                                                 ("action", "action"), ("a1", "aid"), ("pid", "pid")], type_dict)

Revoke = create_action("Revoke",  [("time", "time"),  ("a1", "aid"), ("pid", "pid")], type_dict)


Actions = [Collect, Update, Has_Expertise, Access, Disclose, Consent, Authorize, Revoke]

resource_constraint = resource_type([(Collect, ["pid"])], [(Update, ["pid"]), (Access, ["pid"]), (Disclose, ["pid"]), (Consent, ["pid"]),
                                                           (Authorize, ["pid"]), (Revoke, ["pid"])])
consume_constraint = consumable_resource_type([(Consent, ["a1", "pid"])], [(Access, ["a1", "pid"])], [(Revoke, ["a1", "pid"])] )






for action in Actions:
    action()
resource_constraint()
print(consume_constraint())
