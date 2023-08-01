from logic_operator import *
from type_constructor import union
import time
from analyzer import check_property_refining

'''
TODO: The domain file need to be linked
'''
from template_domain import *



'''
TODO: rules go here
'''
complete_rules =[]
'''
EXAMPLES
#rule_1: a person only withdraw or deposite once per hour
in_out_action = union(Deposit, Withdraw)
complete_rules.append(forall([in_out_action, in_out_action], lambda act1, act2:  OR(EQ(act1, act2), NOT(AND(act1.pid ==  act2.pid,
                                                                                                            act1.time == act2.time)))))

#a person can withdraw or transfer money out if he has sufficent balance
complete_rules.append(forall(Withdraw, lambda withdraw: balance(withdraw.pid, withdraw.time) > withdraw.amount))

complete_rules.append(forall(Trans, lambda trans: balance(trans.sender, trans.time) > trans.amount))


#balance rule: the balance correctly reflect the balance of an account
complete_rules.append(forall(Balance, lambda b: AND(is_invovled(b.pid, b.time),
                                                   b.amount == balance(b.pid, b.time))))
'''

'''
property go here
'''
target_rule = eventually(TimeStamp, lambda t: t.time > 0)

if __name__ == '__main__':
    start = time.time()
    '''
    TODO: Specify parameters, the following parameters need to 
    be changed based on parsed input  
    '''
    is_minimized = True
    max_vol = 1000


    check_property_refining(target_rule, set(), complete_rules, ACTION, state_action, True, disable_minimization=False,
                            min_solution=is_minimized, vol_bound = max_vol, ignore_state_action = True)
    print(time.time() - start)