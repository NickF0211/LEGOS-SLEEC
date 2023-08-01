from pysmt.fnode import FNode

from logic_operator import *
from logic_operator import _polymorph_args_to_tuple


def unless(*args, reference=None):
    # if no consequence, then the defeater is on the condition
    cum_condition = TRUE()
    constraints = []
    processed = _polymorph_args_to_tuple(args)
    for i in range(len(processed)-1, -1, -1):
        condition, action = processed[i]
        if reference:
            if i == 0:
                pass
            else:
                d = reference.defeater[i -1]
                t_cond, t_resp = d.expr, d.response
                condition = check_and_mark(condition, t_cond)
                action = check_and_mark(action, t_resp)

        constraints.append(Implication(AND(cum_condition, condition), action))
        cum_condition = AND(cum_condition, NOT(condition))
    return AND(constraints)


# TODO, convert to xor
def otherwise(cond, primary, alt):
    return Implication(cond, OR(primary, alt))


M = None


def complie_measure(MEASURE):
    global M
    M = MEASURE


def check_and_mark(expr, reference):
    if reference and isinstance(expr, FNode) and expr.get_type() == BOOL:
        expr = Bool_Terminal(expr)
        text_ref[expr] = reference
    return expr


def when(trigger, action, rule_condition=None, reference=None):
    if reference:
        t_trigger = reference.trigger
        t_condition = reference.condition
    else:
        t_trigger = t_condition = None


    if rule_condition is None:
        return forall(trigger, lambda t, t_trigger=t_trigger: exist(M, lambda m: AND(EQ(t.time, m.time),
                                                                action(t, m)
                                                                )), reference=t_trigger)
    else:
        return forall(trigger, lambda t, t_trigger=t_trigger, t_condition = t_condition: exist(M, lambda m: AND(EQ(t.time, m.time),
                                                                OR(check_and_mark(NOT(rule_condition(t, m)), t_condition),
                                                                            action(t, m))
                                                                )), reference=t_trigger)


def when_concern(trigger, action, rule_condition=None, reference=None):
    if reference:
        t_trigger = reference.trigger
        t_condition = reference.condition
    else:
        t_trigger = t_condition = None

    if rule_condition is None:
        return exist(trigger, lambda t, t_trigger=t_trigger: exist(M, lambda m: AND(EQ(t.time, m.time),
                                                                                     action(t, m)
                                                                                     )), reference=t_trigger)
    else:
        return exist(trigger,
                      lambda t, t_trigger=t_trigger, t_condition=t_condition: exist(M, lambda m: AND(EQ(t.time, m.time),
                                                                                                     AND(check_and_mark(
                                                                                                             rule_condition(t, m),
                                                                                                         t_condition),
                                                                                                        action(t, m))
                                                                                                     )),
                      reference=t_trigger)

def when_premise(trigger, rule_condition, reference=None):
    if rule_condition is None:
        return exist([trigger, M], lambda t, m: EQ(t.time, m.time))
    else:
        return exist([trigger, M], lambda t, m: AND(EQ(t.time, m.time), rule_condition(t, m)))


def happen_within(target_class, reference, start, end, constraints=None, ref=None):
    def make_constraint(t, reference=reference, start=start, end=end, ref=ref):
        lower_limit = t.time >= reference.time + start
        upper_limit = t.time <= reference.time + end

        if ref and ref.limit:
            lower_limit = t.time >= reference.time + start
            upper_limit = t.time <= reference.time + end
            lower_limit = Bool_Terminal(lower_limit)
            upper_limit = Bool_Terminal(upper_limit)

            text_ref[lower_limit] = ref.limit.start
            text_ref[upper_limit] = ref.limit.end
            res = AND(upper_limit, lower_limit)
        else:
            res = AND(upper_limit, lower_limit)
        return res

    def make_constraint_unlimited(t, reference=reference, ref=ref):
        term = t.time >= reference.time
        if ref:
            res = Bool_Terminal(term)
            text_ref[res] = ref.inf
        else:
            res = term
        return res

    if ref is not None:
        event = ref.event
    else:
        event = None

    if end >= 0:
        if constraints is None:
            return exist(target_class, lambda t: make_constraint(t, reference, start, end, ref), reference=event)
        else:
            return exist(target_class,
                         lambda t: AND(make_constraint(t, reference, start, end, ref), constraints(t, reference)),
                         reference=event)
    else:
        if constraints is None:
            return exist(target_class, lambda t: make_constraint_unlimited(t, reference, ref), reference=event)
        else:
            return exist(target_class,
                         lambda t: AND(make_constraint_unlimited(t, reference, ref), constraints(t, reference)),
                         reference=event)


class Concern():
    def __init__(self, trigger, action, rule_condition=None, reference=None, next= None):
        self.concern = when_concern(trigger, action, rule_condition=rule_condition, reference=reference)
        self.next = next

    def get_concern(self):
        if not self.next:
            return self.concern
        else:
            return AND(self.next.get_concern(), self.concern)

class WhenRule():

    def __init__(self, trigger, action, rule_condition=None, reference=None):
        self.rule = when(trigger, action, rule_condition=rule_condition, reference=reference)
        self.premise = when_premise(trigger, rule_condition=rule_condition, reference=reference)

    def get_rule(self):
        return self.rule

    def get_premise(self):
        return self.premise

    def encode(self):
        return encode(self.get_rule())
