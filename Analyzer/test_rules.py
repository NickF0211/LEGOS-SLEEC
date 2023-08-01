from logic_operator import *
from test_domain import *
from type_constructor import union
import time
from analyzer import check_property_refining, prove_by_induction

#rules go here
def balance(pid, time):
    deposit_sum = Sum(Deposit, lambda deposit: deposit.amount, lambda deposit: AND(EQ(deposit.pid, pid),
                                                                                    deposit.time < time))
    withdraw_sum = Sum(Withdraw, lambda withdraw: withdraw.amount, lambda withdraw: AND(EQ(withdraw.pid, pid),
                                                                                    withdraw.time < time))

    transfer_in_sum = Sum(Trans, lambda trans:  trans.amount,
                       lambda trans: AND(trans.time < time,
                                         EQ(trans.receiver, pid) ))
    trans_out_sum = Sum(Trans, lambda trans:  trans.amount,
                       lambda trans: AND(trans.time < time,
                                         EQ(trans.sender, pid) ))


    return deposit_sum - withdraw_sum + transfer_in_sum - trans_out_sum

def is_invovled(pid, time):
    cond1 =  once(in_out_action, lambda act: AND(act.time < time,
                                               EQ(act.pid, pid)), time -1)

    cond2 = once(Trans, lambda trans: AND(trans < time,
                                          OR(EQ(trans.sender, pid),
                                             EQ(trans.receiver, pid))), time -1)
    return OR(cond1, cond2)

complete_rules =[]
#rule_1: a person only withdraw or deposite once per hour
in_out_action = union(Deposit, Withdraw)
complete_rules.append(forall([in_out_action, in_out_action], lambda act1, act2:  OR(EQ(act1, act2), NOT(AND(EQ(act1.pid, act2.pid),
                                                                                                            EQ(act1.time , act2.time))))))

#a person can withdraw or transfer money out if he has sufficent balance
complete_rules.append(forall(Withdraw, lambda withdraw: balance(withdraw.pid, withdraw.time) >= withdraw.amount))

complete_rules.append(forall(Trans, lambda trans: balance(trans.sender, trans.time) >= trans.amount))


#balance rule: the balance correctly reflect the balance of an account
complete_rules.append(forall(Balance, lambda b: AND(is_invovled(b.pid, b.time),
                                                   b.amount == balance(b.pid, b.time))))

complete_rules.append(forall(in_out_action, lambda act: act.amount < 5))
#property go here
target_rule = exist([Var, Var], lambda v1, v2: balance(v1.v, v2.v) > 31 )

add_background_theories(ACTION, state_action, complete_rules)

if __name__ == '__main__':
    start = time.time()
    # p = exist(aircraft, lambda g1: next(g1, lambda g2: AND(NOT(g1.fault_communications_adsb), NOT(g2.fault_communications_adsb)) ))
    check_property_refining(target_rule, set(), complete_rules, ACTION, state_action, True, disable_minimization=False,
                            min_solution=False, final_min_solution=True, ignore_state_action=False)
    print(time.time() - start)