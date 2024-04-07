import derivation_rule
from analyzer import check_property_refining, clear_all
from logic_operator import *
from proof_reader import check_and_minimize
from sleecOp import EventRelation
from sleecParser import isXinstance, read_model_file, mm, parse_definitions, constants, scalar_type, reset_rules, \
    parse_rules, parse_concerns, get_high_light, find_relative_pos, registered_type, scalar_mask, parse_relations, \
    get_relational_constraints, clear_relational_constraints
from pysmt.shortcuts import *

from trace_ult import model_based_inst
from type_constructor import create_action, create_type, union

blocked_actions = {}

MAX_TIME_UNIT = 99999


def reset_all():
    blocked_actions.clear()
    Constant.Constant_map.clear()
    Obligation.Obg_by_head.clear()


class Term:

    def __repr__(self):
        return str(self)

    def __add__(self, other):
        return add(self, other)

    def __sub__(self, other):
        return minus(self, other)

    def __neg__(self):
        return neg(self)

    def __mul__(self, other):
        if isinstance(self, Constant):
            return mul(self, other)
        elif isinstance(other, Constant):
            return mul(other, self)
        else:
            # We disable non-linear term
            assert False

    def __gt__(self, other):
        return gt(self, other)

    def __lt__(self, other):
        return lt(self, other)

    def __ge__(self, other):
        return ge(self, other)

    def __le__(self, other):
        return le(self, other)

    def __eq__(self, other):
        return eq(self, other)

    def __ne__(self, other):
        return neq(self, other)

    def encode(self, measure):
        pass


class Constant(Term):
    Constant_map = dict()

    def __init__(self, val):
        self.val = val
        Constant.Constant_map[val] = self

    def __str__(self):
        return str(self.val)

    def encode(self, measure):
        return self.val

    def poke(self):
        return self.val


def INF():
    return Constant(MAX_TIME_UNIT)


def ZERO():
    return Constant(0)


def cons(val):
    if val in Constant.Constant_map:
        return Constant.Constant_map[val]
    else:
        return Constant(val)


class NATMeasure(Term):
    def __init__(self, var):
        self.var = var

    def __str__(self):
        return self.var

    def encode(self, measure):
        return getattr(measure, self.var)

    def poke(self):
        return False


class BinaryArithmetic(Term):
    def __init__(self, left, right, op):
        self.left = left
        self.right = right
        self.op = op

    def __str__(self):
        return "({} {} {})".format(self.left, self.op, self.right)

    def encode(self, measure):
        return op_str_sleec(self.op)(self.left.encode(measure), self.right.encode(measure))

    def poke(self):
        left_p = self.left.poke()
        right_p = self.right.poke()
        if left_p is not False and right_p is not False:
            if self.op == "+":
                return left_p + right_p
            elif self.op == "-":
                return left_p - right_p
            elif self.op == "*":
                return left_p * right_p
            else:
                return False
        else:
            return False


def add(left: Term, right: Term):
    if isinstance(left, Constant) and isinstance(right, Constant):
        return cons(left.val + right.val)
    else:
        return BinaryArithmetic(left, right, '+')


def minus(left: Term, right: Term):
    if isinstance(left, Constant) and isinstance(right, Constant):
        return cons(left.val - right.val)
    else:
        return BinaryArithmetic(left, right, '-')


def mul(left: Constant, right: Term):
    if isinstance(right, Constant) and isinstance(left, Constant):
        return cons(left.val * right.val)
    else:
        return BinaryArithmetic(left, right, '*')


def neg(term: Term):
    return minus(cons(0), term)


class Prop:

    def __repr__(self):
        return str(self)

    def encode(self, t_measure):
        pass


class BinaryComparison(Prop):

    def __init__(self, left, right, op):
        self.left = left
        self.right = right
        # assert isinstance(left, Term)
        # assert isinstance(right, Term)
        self.op = op

    def __str__(self):
        return "({} {} {})".format(self.left, self.op, self.right)

    def encode(self, t_measure):
        return op_str_sleec(self.op)(self.left.encode(t_measure), self.right.encode(t_measure))


def ge(left: Term, right: Term):
    if isinstance(left, Constant) and isinstance(right, Constant):
        return left.val >= right.val
    else:
        return BinaryComparison(left, right, '>=')


def le(left: Term, right: Term):
    if isinstance(left, Constant) and isinstance(right, Constant):
        return left.val <= right.val
    else:
        return BinaryComparison(left, right, '<=')


def gt(left: Term, right: Term):
    if isinstance(left, Constant) and isinstance(right, Constant):
        return left.val > right.val
    else:
        return BinaryComparison(left, right, '>')


def lt(left: Term, right: Term):
    if isinstance(left, Constant) and isinstance(right, Constant):
        return left.val < right.val
    else:
        return BinaryComparison(left, right, '<')


def eq(left: Term, right: Term):
    if isinstance(left, Constant) and isinstance(right, Constant):
        return left.val == right.val
    else:
        return BinaryComparison(left, right, '=')


def neq(left: Term, right: Term):
    if isinstance(left, Constant) and isinstance(right, Constant):
        return left.val != right.val
    else:
        return BinaryComparison(left, right, '!=')


class BoolMeasure(Prop):
    def __init__(self, var):
        self.var = var

    def __str__(self):
        return str(self.var)

    def encode(self, measure):
        return getattr(measure, self.var)


class Negation(Prop):

    def __init__(self, expr: Prop):
        self.expr = expr

    def __str__(self):
        return "(not {})".format(self.expr)

    def encode(self, t_measure):
        return NOT(self.expr.encode(t_measure))


class BinaryLogic(Prop):

    def __init__(self, left: Prop, right: Prop, op):
        self.left = left
        self.right = right
        self.op = op

    def __str__(self):
        return "({} {} {})".format(self.left, self.op, self.right)

    def encode(self, measure):
        return op_str_sleec_bool(self.op)(self.left.encode(measure), self.right.encode(measure))


def sand(left, right):
    if left is True:
        return right
    elif right is True:
        return left
    elif left is False or right is False:
        return False
    else:
        return BinaryLogic(left, right, 'and')


def snot(expr):
    if expr is False:
        return True
    elif expr is True:
        return False
    else:
        return Negation(expr)


def sor(left, right):
    if left is False:
        return right
    elif right is False:
        return left
    elif left is True or right is True:
        return True
    else:
        return BinaryLogic(left, right, 'or')
    # return sand(snot(left), snot(right))


class Event:

    def __init__(self, expr, neg: bool):
        self.expr = expr
        self.neg = neg

    def __neg__(self):
        return Event(self.expr, not self.neg)

    def __str__(self):
        if self.neg:
            return "not_{}".format(self.expr)
        else:
            return str(self.expr)

    def __eq__(self, other):
        return self.is_conflicting(other)

    def __repr__(self):
        return str(self)

    def is_conflicting(self, other):
        return self.expr == other.expr and self.neg != other.neg

    def is_identical(self, other):
        return self.expr == other.expr and self.neg == other.neg

    def __hash__(self):
        return hash(str(self))


class TimeWindow:
    def __init__(self, start, end):
        self.start = start
        self.end = end

    # TODO: currently only support end-point
    def encode(self, event_obj, measure):
        start_time = self.start.encode(measure)
        end_time = self.end.encode(measure)
        return measure.time + start_time <= event_obj.time <= measure.time + end_time

    def encode_limited_pos(self, event_obj, measure, last_time):
        return AND(measure.time + self.end.encode(measure) > last_time, NOT(self.encode(event_obj, measure)))

    def encode_limited_neg(self, event_obj, measure, last_time):
        return And(event_obj.time <= last_time
                   , self.encode(event_obj, measure))

    def is_overlapping(self, other, measure):
        self_end_poke = self.end.poke()
        other_end_poke = other.end.poke()
        if self_end_poke is not False and other_end_poke is not False:
            return self_end_poke >= other_end_poke
        else:
            return self.end.encode(measure) >= other.end.encode(measure)

    def poke_overlapping(self, other):
        # check if potenially overlapping
        self_end_poke = self.end.poke()
        other_end_poke = other.end.poke()
        if other_end_poke is False or self_end_poke is False:
            return True
        else:
            return self_end_poke >= other_end_poke

    def is_inf(self):
        return self.start == ZERO() and self.end == INF()

    def is_inst(self):
        return (self.start == ZERO() or not self.start) and (self.end == ZERO() or not self.end)

    def __str__(self):
        if self.is_inf():
            return "eventually"

        if self.start and self.start != ZERO():
            return "[{}, {}] seconds".format(self.start, self.end)
        else:
            return "{} seconds".format(self.end)


def create_and_append(col, key, item):
    if key not in col:
        col[key] = set()
    col[key].add(item)


def find_conflicting_obligation_by_head(head: Event):
    neg_head = -head
    return Obligation.Obg_by_head.get(str(neg_head), [])


class Obligation:
    Obg_by_head = {}

    def __init__(self, head: Event, deadline: TimeWindow, parent_rule=None):
        self.head = head
        self.deadline = deadline
        self.conflicting_obgs = []
        self.parent = None
        self.parent_rule = parent_rule
        create_and_append(Obligation.Obg_by_head, str(self.head), self)

    def __repr__(self):
        return str(self)

    def is_inst(self):
        return self.deadline.is_inst()

    def get_deadline(self, trigger_measure):
        if self.is_inst():
            return trigger_measure.time
        else:
            return trigger_measure.time + self.deadline.end.encode(trigger_measure)

    def is_conflicting(self, other):
        return self.head.is_conflicting(other.head)

    def conflict(self, other, measure):
        if self.is_conflicting(other):
            if self.head.neg:
                return self.deadline.is_overlapping(other.deadline, measure)
            else:
                return other.deadline.is_overlapping(self.deadline, measure)
        else:
            return False

    def poke_conflict(self, other):
        if self.is_conflicting(other):
            if self.head.neg:
                return self.deadline.poke_overlapping(other.deadline)
            else:
                return other.deadline.poke_overlapping(self.deadline)
        else:
            return False

    def find_conflicting_obligations(self):
        if self.conflicting_obgs:
            return self.conflicting_obgs
        else:
            neg_head = -self.head
            n_obgs = Obligation.Obg_by_head.get(str(neg_head), [])
            self.conflicting_obgs = [n_obg for n_obg in n_obgs if self.poke_conflict(n_obg)]
            return self.conflicting_obgs

    def encode_limited(self, t_measure, c_measure, A_Mapping):
        return NOT(self.violated(t_measure, c_measure, A_Mapping))

    def _violated(self, trigger_measure, current_measure, A_Mapping, neg):
        if neg:
            return exist(A_Mapping[self.head.expr],
                         lambda r, trigger_measure=trigger_measure, current_measure=current_measure:
                         self.deadline.encode_limited_neg(r, trigger_measure, current_measure.time))
        else:
            return forall(A_Mapping[self.head.expr],
                          lambda r, trigger_measure=trigger_measure, current_measure=current_measure:
                          self.deadline.encode_limited_pos(r, trigger_measure, current_measure.time))

    def violated(self, trigger_measure, current_measure, A_Mapping):
        if self.head.neg:
            return self._violated(trigger_measure, current_measure, A_Mapping, True)
        else:
            return self._violated(trigger_measure, current_measure, A_Mapping, False)

    def fulfilled(self, trigger_measure, current_measure, A_Mapping):
        if self.head.neg:
            return self._violated(trigger_measure, current_measure, A_Mapping, False)
        else:
            return self._violated(trigger_measure, current_measure, A_Mapping, True)

    def active(self, trigger_measures, current_measure, A_Mapping):
        # An obligation is active if it is neither fulfilled nor violated
        return AND(NOT(self.violated(trigger_measures, current_measure, A_Mapping)),
                   NOT(self.fulfilled(trigger_measures, current_measure, A_Mapping)))

    def forced(self, trigger_measures, current_measure, A_Mapping):
        return self.parent.forced(trigger_measures, current_measure, A_Mapping)

    def triggered(self, trigger_measures, current_measure, A_Mapping):
        return self.parent.triggered(trigger_measures, current_measure, A_Mapping)

    def blocked(self, trigger_measures, current_measure, A_Mapping):
        return exist(blocked_actions[self.head],
                     lambda ba, self=self: AND(EQ(ba.time, trigger_measures.time), EQ(ba.end,
                                                                                      self.get_deadline(
                                                                                          trigger_measures)),
                                               ba.time <= ba.end))

    def __str__(self):
        if not self.deadline.is_inf():
            return "{} within {}".format(str(self.head), str(self.deadline))
        else:
            return "{} eventually".format(str(self.head))

    def __hash__(self):
        return hash(str(self))


class Conditional_Obligation:
    def __init__(self, condition: Prop, obligation: Obligation):
        self.parent = None
        self.parent_rule = None
        self.pre = None
        self.next = None
        self.condition = condition
        self.obligation = obligation

    def encode_limited(self, t_measure, cur_measure, A_Mapping):
        if self.condition is True:
            return self.obligation.encode_limited(t_measure, cur_measure, A_Mapping)
        else:
            return Implication(self.get_condition(t_measure),
                               self.obligation.encode_limited(t_measure, cur_measure, A_Mapping))

    def get_condition(self, m):
        if self.condition is True:
            return TRUE()
        elif self.condition is False:
            return FALSE()
        else:
            return self.condition.encode(m)

    def triggered(self, trigger_measures, current_measure, A_Mapping):
        if self.pre is None:
            return AND(self.parent_rule.triggered(trigger_measures, current_measure, A_Mapping),
                       self.get_condition(trigger_measures))
        else:
            condition_measure = self.get_condition(trigger_measures)
            if self.pre.is_inst():
                return AND(condition_measure, AND(
                    self.pre.triggered(trigger_measures, current_measure, A_Mapping),
                    Implication(trigger_measures.time > current_measure.time,
                                self.pre.blocked(trigger_measures, current_measure, A_Mapping)),
                    Implication(trigger_measures.time <= current_measure.time,
                                self.pre.violated(trigger_measures, current_measure, A_Mapping))
                ))
            else:
                # pre is violated
                return AND(
                    condition_measure,
                    exist(A_Mapping["Measure"], lambda t1_measure, trigger_measure=trigger_measures, self=self:
                    AND(
                        EQ(t1_measure.time + self.pre.get_deadline(t1_measure), trigger_measure.time),
                        self.pre.triggered(t1_measure, current_measure, A_Mapping),
                        Implication(trigger_measures.time > current_measure.time,
                                    self.pre.blocked(t1_measure, current_measure, A_Mapping)),
                        Implication(trigger_measures.time <= current_measure.time,
                                    self.pre.violated(t1_measure, current_measure, A_Mapping))
                    )))

    def __str__(self):
        if self.condition is True:
            return str(self.obligation)
        else:
            return "({} => {})".format(str(self.condition), str(self.obligation))

    def __repr__(self):
        return str(self)

    def __hash__(self):
        return hash(str(self))

    def is_inst(self):
        return self.obligation.is_inst()

    def blocked(self, trigger_measures, current_measure, A_Mapping):
        if self.condition is True:
            return self.obligation.blocked(trigger_measures, current_measure, A_Mapping)
        elif self.condition is False:
            return FALSE()
        else:
            return AND(self.get_condition(trigger_measures),
                       self.obligation.blocked(trigger_measures, current_measure, A_Mapping))

    def violated(self, trigger_measure, current_measure, A_Mapping):
        if self.condition is True:
            return self.obligation.violated(trigger_measure, current_measure, A_Mapping)
        elif self.condition is False:
            return FALSE()
        else:
            return AND(self.get_condition(trigger_measure),
                       self.obligation.violated(trigger_measure, current_measure, A_Mapping))

    def forced(self, trigger_measure, current_measure, A_Mapping):
        active = self.obligation.active(trigger_measure, current_measure, A_Mapping)
        if self.next is None:
            return active
        else:
            return AND(active, exist(A_Mapping["Measure"], lambda m, trigger_measure=trigger_measure, self=self:
            AND(EQ(m.time, self.get_next_time(trigger_measure)),
                self.next.all_blocked(m, current_measure, A_Mapping))
                                     ))

    def all_blocked(self, trigger_measure, current_measure, A_Mapping):
        current_block = self.blocked(trigger_measure, current_measure, A_Mapping)
        if self.next is None:
            return current_block
        else:
            return AND(current_block,
                       exist(A_Mapping["Measure"], lambda future_m, trigger_measure=trigger_measure, self=self:
                       AND(
                           EQ(future_m.time, trigger_measure.time + self.get_deadline(trigger_measure)),
                           self.next.all_blocked(future_m, current_measure, A_Mapping))
                             ))

    def get_deadline(self, trigger_measure):
        return self.obligation.get_deadline(trigger_measure)

    def get_next_time(self, trigger_measure):
        return trigger_measure.time + self.get_deadline(trigger_measure)


class ObligationChain:
    def __init__(self, obligations: [Conditional_Obligation]):
        self.obligations = obligations

    def __repr__(self):
        return str(self)

    def __str__(self):
        return "( {} )".format(' otherwise '.join([str(obg) for obg in self.obligations]))

    def __add__(self, other):
        return ObligationChain(self.obligations + other.obligations)

    def triggered(self, trigger_measures, current_measure, A_Mapping):
        head = self.obligations[0]
        return head.get_condition(trigger_measures)

    def _encode_limited(self, t_measure, cur_measure, A_Mapping, index=0):
        if index >= len(self.obligations):
            return FALSE()
        else:
            cur_obg = self.obligations[index]
            is_inst = cur_obg.is_inst()
            if is_inst:
                return OR(cur_obg.encode_limited(t_measure, cur_measure, A_Mapping),
                          self._encode_limited(t_measure, cur_measure, A_Mapping, index + 1))
            else:
                # the time point where one fails
                return OR(
                    cur_obg.encode_limited(t_measure, cur_measure, A_Mapping),
                    exist(A_Mapping["Measure"],
                          lambda new_t_measure, t_measure=t_measure, cur_measure=cur_measure, index=index,
                                 cur_obg=cur_obg:
                          AND(EQ(new_t_measure.time,
                                 t_measure.time + cur_obg.obligation.deadline.end.encode(t_measure)),
                              self._encode_limited(new_t_measure, cur_measure, A_Mapping, index + 1)))
                )

    def encode_limited(self, t_measure, cur_measure, A_Mapping):
        return self._encode_limited(t_measure, cur_measure, A_Mapping)

    def _blocked(self, trigger_measures, current_measure, A_Mapping, index=0):
        if index >= len(self.obligations):
            return TRUE()
        else:
            cur_obg = self.obligations[index]
            is_inst = cur_obg.is_inst()
            if is_inst:
                return AND(cur_obg.blocked(trigger_measures, current_measure, A_Mapping),
                           self._blocked(trigger_measures, current_measure, A_Mapping, index + 1))
            else:
                # the time point where one fails
                return AND(
                    cur_obg.blocked(trigger_measures, current_measure, A_Mapping),
                    exist(A_Mapping["Measure"],
                          lambda new_t_measure, t_measure=trigger_measures, cur_measure=current_measure, index=index,
                                 cur_obg=cur_obg:
                          AND(EQ(new_t_measure.time,
                                 t_measure.time + cur_obg.obligation.deadline.end.encode(t_measure)),
                              self._blocked(new_t_measure, cur_measure, A_Mapping, index + 1)))
                )

    def blocked(self, trigger_measures, current_measure, A_Mapping):
        return self._blocked(trigger_measures, current_measure, A_Mapping)


class NormalizedRule:

    def __init__(self, triggering_event: Event, oc: ObligationChain, og_rule=None):
        assert not triggering_event.neg
        self.triggering_event = triggering_event
        self.oc = oc
        self.og_rule = og_rule

    def triggered(self, trigger_measures, current_measure, A_Mapping):
        return exist(A_Mapping[self.triggering_event.expr],
                     lambda trigger, self=self: AND(EQ(trigger.time, trigger_measures.time),
                                                    trigger_measures.time <= current_measure.time,
                                                    ))

    def triggered_now(self, trigger_measures, current_measure, A_Mapping):
        return AND(exist(A_Mapping[self.triggering_event.expr],
                         lambda trigger, trigger_measures=trigger_measures, current_measure=current_measure, self=self:
                         AND(EQ(trigger.time, trigger_measures.time),
                             trigger_measures.time <= current_measure.time,
                             )),
                   self.oc.triggered(trigger_measures, current_measure, A_Mapping))

    def __str__(self):
        return "when {} then {}".format(str(self.triggering_event), str(self.oc))

    def __repr__(self):
        return str(self)

    def register_obligations(self):
        # add back edge from obligation to the rule
        for i in range(len(self.oc.obligations)):
            obg = self.oc.obligations[i]

            if i > 0:
                obg.pre = self.oc.obligations[i - 1]
                self.oc.obligations[i - 1].next = obg
            else:
                obg.pre = None

            obg.parent = self.oc
            obg.obligation.parent = obg

            obg.obligation.parent_rule = self
            obg.parent_rule = self

    def get_obgs(self):
        return self.oc.obligations

    def encode_limited(self, cur_measure, A_Mapping, exception=None):
        if exception:
            return forall(A_Mapping[self.triggering_event.expr],
                          lambda trigger, cur_measure=cur_measure, exception=exception:
                          Implication(trigger.time <= cur_measure.time,
                                      exist(A_Mapping["Measure"],
                                            lambda t_measure, cur_measure=cur_measure, exception=exception: Implication(
                                                NEQ(exception, t_measure),
                                                self.oc.encode_limited(t_measure,
                                                                       cur_measure,
                                                                       A_Mapping)))))
        else:
            return forall(A_Mapping[self.triggering_event.expr],
                          lambda trigger: Implication(trigger.time <= cur_measure.time,
                                                      exist(A_Mapping["Measure"],
                                                            lambda t_measure: self.oc.encode_limited(t_measure,
                                                                                                     cur_measure,
                                                                                                     A_Mapping))))


def certasin_product(prs1: [Conditional_Obligation], prs2: [Conditional_Obligation]):
    res = []
    for pr1 in prs1:
        for pr2 in prs2:
            res.append(pr1 + pr2)
    return res


def parse_rules_norm(rb):
    rules = []
    for r in rb.rules:
        rules.extend(norm_parse_element(r, True))
    return rules


def parse_sleec_norm(model_file, read_file=True):
    if read_file:
        model_str = read_model_file(model_file)
    else:
        model_str = model_file
    # Parse the model using the metamodel
    model = mm.model_from_str(model_str)
    Action_Mapping = parse_definitions(model.definitions)
    Actions = list(Action_Mapping.values())

    rules = parse_rules_norm(model.ruleBlock)
    og_rules = parse_rules(model.ruleBlock, Action_Mapping)
    if model.concernBlock:
        concerns = parse_concerns(model.concernBlock, Action_Mapping)
    else:
        concerns = []

    if model.relBlock:
        relations = parse_relations(model.relBlock, Action_Mapping)
    else:
        relations = []

    return model, rules, Action_Mapping, Actions, og_rules, concerns, relations


def norm_parse_element(node, cond=None):
    if isinstance(node, int) or isinstance(node, str):
        return node
    if node is None:
        return node
    if node == []:
        return None
    if isXinstance(node, "Rule"):
        res = norm_parse_rule(node, cond=None)
    # elif isXinstance(node, "Concern"):
    #     res = parse_rule(node, Action_Mapping, head, measure, is_concern=True)
    elif isXinstance(node, "Trigger"):
        res = norm_parse_trigger(node, cond)
    elif isXinstance(node, "Event"):
        res = norm_parse_event(node, cond)
    elif isXinstance(node, "Response") or isXinstance(node, "InnerResponse"):
        res = norm_parse_response(node, cond)
    elif isXinstance(node, "Occ"):
        res = norm_parse_occ(node, cond)
    elif isXinstance(node, "TimeLimit"):
        res = norm_parse_timelimit(node, cond)
    elif isXinstance(node, "Value"):
        res = norm_parse_value(node, cond)
    elif isXinstance(node, "Alternative"):
        res = norm_parse_response(node.response, cond)
    elif isXinstance(node, "NumTerminal"):
        res = norm_parse_numterminal(node, cond)
    elif isXinstance(node, "NumMeasure"):
        res = norm_parse_num_measure(node, cond)
    elif isXinstance(node, "BoolMeasure"):
        res = norm_parse_bool_measure(node, cond)
    elif isXinstance(node, "ScalarMeasure"):
        res = norm_parse_scalar_measure(node, cond)
    elif isXinstance(node, "NumericalOp"):
        res = norm_parse_num_op(node, cond)
    elif isXinstance(node, "BoolBinaryOp"):
        res = norm_parse_bool_bin_op(node, cond)
    elif isXinstance(node, "NumBinOp"):
        res = norm_parse_num_bin_op(node, cond)
    # elif isXinstance(node, "Defeater"):
    #     res = parse_defeater(node, Action_Mapping, head, measure)
    elif isXinstance(node, "Negation"):
        res = norm_parse_negation(node, cond)
    elif isXinstance(node, "ScalarBinaryOp"):
        res = norm_parse_scalar_binary_op(node, cond)
    elif isXinstance(node, "ScalarTerminal"):
        res = norm_parse_scalar_terminal(node, cond)
    elif isXinstance(node, "ScaleParam"):
        res = norm_parse_scale_param(node, cond)
    elif isXinstance(node, "BoolTerminal"):
        res = norm_parse_bool_terminal(node, cond)
    elif isXinstance(node, "Constant"):
        res = norm_parse_value(node.value, cond)
    elif isXinstance(node, "TimeValue"):
        res = norm_parse_timevalue(node, cond)
    else:
        assert False

    return res


def norm_parse_rule(node, cond=True):
    triggering_event = norm_parse_element(node.trigger, cond)
    triggering_condition = norm_parse_element(node.condition, cond) if node.condition else True
    prs = norm_parse_element(node.response, triggering_condition)
    results = []
    for pr in prs:
        nr = NormalizedRule(triggering_event, pr, node)
        results.append(nr)
        nr.register_obligations()
    return results


def norm_parse_trigger(node, cond):
    return Event(norm_parse_element(node.event, cond), neg=False)


def norm_parse_event(node, cond):
    return node.name


def norm_parse_occ(node, cond):
    negation = node.neg
    event = norm_parse_element(node.event, cond)
    if node.limit:
        start, end = norm_parse_element(node.limit, cond)
    else:
        start = end = Constant(0)

    if not node.limit:
        if node.inf:
            start = ZERO()
            end = INF()
        else:
            start = end = Constant(0)
    event = event if not negation else -event
    return Obligation(event, TimeWindow(start, end))


def norm_parse_response(node, cond):
    # occ = norm_parse_element(node.occ, cond)
    # alt = norm_parse_element(node.alternative, cond)

    if not node.defeater:
        if node.alternative is None:
            return [ObligationChain([Conditional_Obligation(cond, norm_parse_element(node.occ, cond))])]
        else:
            return certasin_product([
                ObligationChain([Conditional_Obligation(cond, norm_parse_element(node.occ, cond))])
            ],
                norm_parse_element(node.alternative, True))
    else:
        results = []
        for defeater in node.defeater[::-1]:
            cur_cond = norm_parse_element(defeater.expr)
            if defeater.response is not None:
                total_cond = sand(cond, cur_cond)
                responses = norm_parse_element(defeater.response, total_cond)
                results.extend(responses)
            cond = sand(snot(cur_cond), cond)

        if node.alternative is None:
            default = [
                ObligationChain([Conditional_Obligation(cond, norm_parse_element(node.occ, cond))])
            ]
        else:
            default = certasin_product([
                ObligationChain([Conditional_Obligation(cond, norm_parse_element(node.occ, cond))])
            ],
                norm_parse_element(node.alternative, True))

        results.extend(default)
        return results


def norm_parse_timelimit(node, cond):
    if node.start:
        start = norm_parse_element(node.start, cond)
    else:
        start = ZERO()

    if node.end:
        end = norm_parse_element(node.end, cond)
    else:
        end = ZERO()
    return start, end


def norm_parse_value(node, cond):
    if node.value is not None:
        return Constant(node.value)
    else:
        return Constant(constants[node.constant])


def norm_parse_numterminal(node, cond):
    if node.value is not None:
        return norm_parse_element(node.value, cond)
    else:
        return norm_parse_element(node.ID, cond)


def norm_parse_num_measure(node, cond):
    return NATMeasure(node.name)


def norm_parse_bool_measure(node, cond):
    return BoolMeasure(node.name)


def norm_parse_scalar_measure(node, cond):
    return NATMeasure(node.name)


def norm_op_str_sleec(op):
    if op == ">":
        return gt
    elif op == ">=":
        return ge
    elif op == "<=":
        return le
    elif op == "<":
        return lt
    elif op == "+":
        return add
    elif op == "-":
        return minus
    elif op == "*":
        return mul
    elif op == "=":
        return eq
    elif op == "<>":
        return neq
    else:
        assert False


def norm_parse_num_op(node, cond):
    lhs = norm_parse_element(node.lhs, cond)
    rhs = norm_parse_element(node.rhs, cond)
    func = norm_op_str_sleec(node.op)
    res = func(lhs, rhs)
    return res


def norm_parse_bool_bin_op(node, cond):
    lhs = norm_parse_element(node.lhs, cond)
    rhs = norm_parse_element(node.rhs, cond)
    if node.op == "and":
        return sand(lhs, rhs)
    elif node.op == "or":
        return sor(lhs, rhs)
    else:
        assert False


def norm_parse_num_bin_op(node, cond):
    lhs = norm_parse_element(node.lhs, cond)
    rhs = norm_parse_element(node.rhs, cond)
    func = norm_op_str_sleec(node.op)
    return func(lhs, rhs)


def norm_parse_negation(node, cond):
    return Negation(norm_parse_element(node.expr, cond))


def norm_parse_scalar_binary_op(node, cond):
    lhs = norm_parse_element(node.lhs, cond)
    rhs = norm_parse_element(node.rhs, cond)
    func = norm_op_str_sleec(node.op)
    res = func(lhs, rhs)
    return res


def norm_parse_scalar_terminal(node, cond):
    if node.value is not None:
        return norm_parse_element(node.value, cond)
    else:
        return norm_parse_element(node.ID, cond)


def norm_parse_scale_param(node, cond):
    return Constant(scalar_type[node.name])


def norm_parse_bool_terminal(node, cond):
    if node.value is not None:
        res = norm_parse_element(node.value, cond)
    else:
        res = norm_parse_element(node.ID, cond)

    return res


def norm_parse_timevalue(node, cond):
    if node.unit == "seconds":
        mul = 1
    elif node.unit == "minutes":
        mul = 60
    elif node.unit == "hours":
        mul = 3600
    elif node.unit == "days":
        mul = 3600 * 24
    else:
        print("invalid time unit")
        assert False

    return norm_parse_element(node.value, cond) * Constant(mul)


def add_blocked_obgs(ACTIONS, rules):
    type_dict = {}
    create_type("time", type_dict, lower_bound=0)
    for rule in rules:
        for cobg in rule.get_obgs():
            obg = cobg.obligation
            head = obg.head
            if head not in blocked_actions:
                action = create_action("blocked_{}".format(str(head)), [("time", "time"), ("end", "time")],
                                       type_dict)
                blocked_actions[head] = action
                ACTIONS.append(action)
    return ACTIONS


def cast_to_symbolic(expression):
    if expression is True:
        return TRUE()
    elif expression is False:
        return FALSE()
    elif isinstance(expression, int):
        return Int(expression)
    else:
        return expression


def blocked_axiom_interpret(current_measure, blocked_obj, A_Mapping, blocked_obg: Event):
    # assert type(blocked_obj) == blocked_actions[blocked_obg]
    conflicts_obgs = find_conflicting_obligation_by_head(blocked_obg)
    # TODO: filtering ineffective blocking
    if not conflicts_obgs:
        return FALSE()
    else:
        def inter_block(c_obg, t_measure, c_measure, blocked_obg, blocked_obj, A_Mapping):
            # blocking = cast_to_symbolic(blocked_obg.conflict(c_obg, c_measure))
            #
            # if blocking is False:
            #     return FALSE()
            triggered = c_obg.triggered(t_measure, c_measure, A_Mapping)
            forced = c_obg.forced(t_measure, c_measure, A_Mapping)
            if not blocked_obg.neg:
                termination = AND(c_obg.get_deadline(t_measure) >= blocked_obj.end)
                overlapping = t_measure >= blocked_obj
                follow_up = Implication(NOT(termination),
                                        exist(type(blocked_obj), lambda block_obj1, block_obj=blocked_obj:
                                        AND(EQ(block_obj1.end, block_obj.end),
                                            block_obj1.time > blocked_obj.time)))
                return AND(triggered, forced, overlapping, follow_up)
            else:
                c_obg_end = c_obg.get_deadline(t_measure)
                termination = AND(c_obg_end <= blocked_obj.end, c_obg_end >= blocked_obj.time)
                return AND(triggered, forced, termination)

        Measure = A_Mapping["Measure"]
        return exist(Measure, lambda t_measure, c_measure=current_measure,
                                     blocked_obg=blocked_obg, blocked_obj=blocked_obj:
        AND(
            LE(t_measure.time, blocked_obj.time),
            # Implication(blocked_obj.end > blocked_obj.time, c_measure.time >= t_measure.time),
            OR([inter_block(c_obg, t_measure, c_measure, blocked_obg, blocked_obj, A_Mapping)
                for c_obg in
                find_conflicting_obligation_by_head(blocked_obg)]),
        ))


def get_blocked_axioms(A_Mapping, current_measure):
    rules = []
    for obg in blocked_actions:
        blocked_obg = blocked_actions[obg]
        rules.append(forall(blocked_obg, lambda ba, obg=obg, current_measure=current_measure:
        blocked_axiom_interpret(current_measure, ba, A_Mapping, obg)))
    return rules


def process_conflict(relations):
    for rel in relations:
        if isinstance(rel, EventRelation) and rel.op == "conflict":
            obg = Obligation(Event(rel.reference.rhs.name, neg=True), deadline=TimeWindow(Constant(0),  Constant(0)))
            cobg =  Conditional_Obligation(True, obg)
            obgc = ObligationChain([cobg])
            nr = NormalizedRule(Event(rel.reference.lhs.name, neg=False), obgc, rel.reference)
            nr.register_obligations()

            obg = Obligation(Event(rel.reference.lhs.name, neg=True), deadline=TimeWindow(Constant(0), Constant(0)))
            cobg = Conditional_Obligation(True, obg)
            obgc = ObligationChain([cobg])
            nr = NormalizedRule(Event(rel.reference.rhs.name, neg=False), obgc, rel.reference)
            nr.register_obligations()


def check_situational_conflict(model_str, multi_entry=False):
    output = ""
    result = False
    adj_hl = []
    multi_output = []
    model, rules, Action_Mapping, Actions, og_rules, concerns, relations = parse_sleec_norm(model_str, read_file=False)
    for rule in rules:
        print(rule)

    Measure = Action_Mapping["Measure"]
    measure_inv = forall([Measure, Measure], lambda m1, m2: Implication(EQ(m1.time, m2.time), EQ(m1, m2)))
    add_blocked_obgs(Actions, rules)
    process_conflict(relations)
    for r in rules:
        c_measure = Measure()
        if multi_entry:
            output = ""
            adj_hl = []

        fol_rules = [c_measure.presence]
        fol_rules.extend(get_blocked_axioms(Action_Mapping, c_measure))
        print("checking {}".format(str(r)))
        for r_prime in rules:
            if r != r_prime:
                fol_rules.append(r_prime.encode_limited(c_measure, Action_Mapping))
            else:
                fol_rules.append(r.encode_limited(c_measure, Action_Mapping, exception=c_measure))

        fol_rules.append(r.triggered_now(c_measure, c_measure, Action_Mapping))
        # head = r.oc.obligations[0]
        fol_rules.append(r.oc.blocked(c_measure, c_measure, Action_Mapping))
        fol_rules.append(measure_inv)

        relations_constraints = get_relational_constraints(relations)
        fol_rules.extend(relations_constraints)
        res = check_property_refining(AND(fol_rules), set(), set(),
                                      Actions, [], True,
                                      min_solution=False,
                                      final_min_solution=True, restart=False, boundary_case=False,
                                      universal_blocking=False, vol_bound=10, ret_model=True, scalar_mask=scalar_mask
                                      )
        if isinstance(res, tuple):
            trace, sat_model = res
            inst_actions = model_based_inst(sat_model, Actions, completeness=True, time=c_measure.time, measure_class=Measure)

            clear_all(Actions)
            reset_rules(og_rules)
            measure_inv.clear()
            derivation_rule.reset()
            clear_relational_constraints(relations_constraints)

            reset_rules(og_rules)
            measure_inv.clear()
            derivation_rule.reset()
            rule_number = model.ruleBlock.rules.index(r.og_rule)
            target_rule = og_rules[rule_number]
            res = check_property_refining(AND(target_rule.get_premise(), AND(AND(inst_actions), measure_inv)), [],
                                          [r.get_rule() for r in og_rules] + get_relational_constraints(relations),
                                          Actions, [], True,
                                          min_solution=False,
                                          final_min_solution=True, restart=False, boundary_case=False,
                                          universal_blocking=False,
                                          record_proof=True)
            if res == 0:
                output += "Situational conflict under situation :\n{}\n".format(trace)
                try:
                    result = True
                    UNSAT_CORE, derivation = check_and_minimize("proof.txt", "simplified.txt")
                    i = rule_number
                    print("UNSAT CORE")
                    reasons = []
                    # for r in UNSAT_CORE:
                    #     id = r.id
                    #     if id == 0:
                    #         adjust_index = i
                    #     elif id > len(og_rules):
                    #         continue
                    #     else:
                    #         adjust_index = id - 1
                    for r in UNSAT_CORE:
                        id = r.id
                        if id == 0:
                            adjust_index = i
                            rule_model = model.ruleBlock.rules[adjust_index]
                        elif id > len(og_rules):
                            if model.relBlock and id - 1 < len(model.relBlock.relations) + len(og_rules):
                                adjust_index = id - 1
                                rule_model = model.relBlock.relations[id - 1 - len(og_rules)]
                            else:
                                continue
                        else:
                            adjust_index = id - 1
                            rule_model = model.ruleBlock.rules[adjust_index]

                        # rule_model = model.ruleBlock.rules[adjust_index]
                        # start, end = rule_model._tx_position, rule_model._tx_position_end
                        if adjust_index == i:
                            target = rule_model
                            # print("Redundant SLEEC rule:")
                            # print(model_str[start: end])
                            # print("-" * 100)
                        else:
                            reasons.append(rule_model)
                            # reasons += (model_str[start: end]) + '\n' + "-" * 100 + '\n'

                    local_index = {}

                    start, end = target._tx_position, target._tx_position_end
                    output += "For rule:\n"
                    new_start = len(output)
                    local_index[(start, end)] = new_start
                    output += "{}\n".format(model_str[start: end])
                    output += ("-" * 100 + '\n')
                    output += ("-" * 100 + '\n')
                    output += "Because of the following SLEEC rule:\n"
                    output += ("-" * 100 + '\n')
                    for r in reasons:
                        start, end = r._tx_position, r._tx_position_end
                        new_start = len(output)
                        local_index[(start, end)] = new_start
                        output += "{}\n".format(model_str[start: end])
                        output += ("-" * 100 + '\n')

                    print(output)

                    print("TO BE HIGHLIGHTED")
                    hls = get_high_light(derivation)
                    for s, e in hls:
                        s, e = find_relative_pos(s, e, local_index)
                        adj_hl.append((s, e))
                        print("{} : [{}, {}]".format(output[s: e], s, e))

                    if multi_entry:
                        multi_output.append((output, adj_hl))
                except:
                    rule_model = model.ruleBlock.rules[rule_number]
                    start, end = rule_model._tx_position, rule_model._tx_position_end
                    output += "For rule:\n"
                    output += "{}\n".format(model_str[start: end])
                    output += ("-" * 100 + '\n')
                    continue
            else:
                # print(res)
                rule_model = model.ruleBlock.rules[rule_number]
                start, end = rule_model._tx_position, rule_model._tx_position_end
                # output += "For rule:\n"
                # output += "{}\n".format(model_str[start: end])
                # output += ("-" * 100 + '\n')
                print("worth checking: {}\n".format(model_str[start: end]))

        clear_all(Actions)
        reset_rules(og_rules)
        measure_inv.clear()
        derivation_rule.reset()
        clear_relational_constraints(relations)

    derivation_rule.reset()
    clear_relational_constraints(relations)
    reset_all()
    scalar_mask.clear()
    scalar_type.clear()
    registered_type.clear()
    text_ref.clear()

    if multi_entry:
        return multi_output
    else:
        return result, output, adj_hl

# if __name__ == "__main__":
#     model_str = read_model_file("/Users/nickfeng/SFAH19/runtime-verif/SleecFrontEnd/dressingrobot-3.sleec")
#     check_situational_conflict(model_str)
