from type_constructor import create_type, create_action, create_pair_action

type_dict = dict()
time = create_type("time", type_dict, lower_bound=0, upper_bound=100000)
sid = create_type("sid", type_dict, lower_bound = 0, upper_bound = 100)
aid = create_type("aid", type_dict, lower_bound = 0, upper_bound = 100)
pid = create_type("pid", type_dict, lower_bound = 0, upper_bound = 1000)
pvalue = create_type("pvalue", type_dict)
purpose = create_type("purpose", type_dict, lower_bound=0, upper_bound=2)
expertise = create_type("expertise", type_dict, lower_bound=0, upper_bound=3)
action = create_type("action", type_dict, lower_bound=1, upper_bound=2)
message = create_type("message", type_dict, lower_bound=0, upper_bound=10)
balance = create_type("balance", type_dict, lower_bound=0)
var = create_type("value", type_dict)








Var =create_action("Var", ["value", "value"], type_dict)
TimeStamp = create_action("TimeStamp", [("time", "time")],type_dict, abstraction=False)

Balance = create_action("Balance", [("time", "time"), ("subject", "sid"), ("balance", "balance")], type_dict, abstraction=False)

Collect = create_action("Collect", [("time", "time"), ("subject", "sid"),
                                    ("pid", "pid"), ("pvalue", "pvalue"), ("purpose","purpose")],type_dict)

Notify = create_action("Notify", [("time", "time"), ("subject", "sid"),
                                    ("message", "message")],type_dict)

Request_Update, Update = create_pair_action("Update", [("time", "time"), ("subject", "sid"),
                                    ("pid", "pid"), ("pvalue", "pvalue")],type_dict)

Has_Expertise = create_action("Has_Expertise",  [("time", "time"),
                                                 ("expertise", "expertise"), ("purpose", "purpose")],type_dict)

Request_Access = create_action("Request_Access", [("time", "time"),
                                                 ("pid", "pid"), ("a1", "aid")],type_dict)
Access = create_action("Access", [("time", "time"),
                                                 ("pid", "pid"), ("a1", "aid"), ("pvalue", "pvalue")],type_dict)
Request_Use = create_action("Request_Use", [("time", "time"),
                                                 ("pid", "pid"), ("a1", "aid")],type_dict)
Use = create_action("Use", [("time", "time"),
                                                 ("pid", "pid"), ("a1", "aid")],type_dict)

Request_Disclose = create_action("Request_Disclose", [("time", "time"),
                                                 ("a1", "aid"), ("pid", "pid"), ("pvalue", "pvalue"),
                                      ("a2", "aid")],type_dict)
Disclose = create_action("Disclose", [("time", "time"),
                                                 ("a1", "aid"), ("pid", "pid"), ("pvalue", "pvalue"),
                                      ("a2", "aid")],type_dict)

Request_Consent =create_action("Request_Consent", [("time", "time"),
                                                 ("action", "action"), ("a1", "aid"), ("pid", "pid"),
                                      ("a2", "aid")], type_dict)

Consent = create_action("Consent", [("time", "time"),
                                                 ("action", "action"), ("a1", "aid"), ("pid", "pid"),
                                      ("a2", "aid")], type_dict)

Patient_Consent = create_action("Patient_Consent", [("time", "time"),("subject", "sid")], type_dict)

Authorize= create_action("Authorize", [("time", "time"),
                                                 ("permission", "action"), ("a1", "aid"), ("pid", "pid")], type_dict)

Revoke = create_action("Revoke",  [("time", "time"),  ("a1", "aid"), ("pid", "pid")], type_dict)

Assign_Expertise = create_action("Assign_expertise",  [("time", "time"),  ("expertise", "expertise"), ("a1", "aid")], type_dict)

Request_Erase, Erase = create_pair_action("Erase", [("subject", "sid"), ("pid", "pid"), ("time", "time")], type_dict)
Request_Patient_Access, Patient_Access = create_pair_action("Patient_Access", [("subject", "sid"), ("pid", "pid"),  ("pvalue", "pvalue"), ("time", "time")], type_dict)

Request_Action = [Request_Access, Request_Consent, Request_Disclose, Request_Use, Request_Erase, Request_Patient_Access, Request_Update]
ACTION = Request_Action + [Patient_Access, Collect, Update, Has_Expertise, Access, Disclose, Consent, Authorize, Revoke, Assign_Expertise, Patient_Consent, Use, Erase, TimeStamp , Balance]
ACTION_MAP = {}
for act in ACTION:
    ACTION_MAP[act.action_name.upper()] = act

#additional correction if needed
ACTION_MAP.update( { "Collect".upper(): Collect, "Update".upper():Update, "Has_Expertise".upper(): Has_Expertise, "Access".upper(): Access, "Disclose".upper(): Disclose,
               "Consent".upper() : Consent, "Authorize".upper(): Authorize, "Revoke".upper(): Revoke, "Assign_Expertise".upper(): Assign_Expertise,
               "Patient_consent".upper(): Patient_Consent, "USE":Use})

state_action = [Balance, TimeStamp]

#now creates abstraction
#create_abstraction("pid", upper_bound=6)
#create_abstraction("sid", upper_bound=4)
#create_abstraction("pvalue", upper_bound=4)
#create_abstraction("time", upper_bound=15, ordered=True)