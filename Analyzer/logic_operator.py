from ordered_set import OrderedSet
from pysmt.shortcuts import *

from type_constructor import Action, UnionAction

import itertools

controll_varaible_eq = dict()
controll_varaible_eq_r = dict()
raw_control_variable = OrderedSet()
controll_variable = OrderedSet()
controll_variable_scope = dict()
control_var_sym = dict()

learned_inv = []
model_action_mapping = dict()

# a reference table to keep track of the reference of a node
text_ref = {}


class Control_Tree():

    def __init__(self, control_vs, trees, name="control_v"):
        self.control_vs = control_vs
        self.trees = trees
        self.name = name

    def add_child(self, child_vs, child_trees):
        self.control_vs += child_vs
        self.trees += child_trees


def look_for_child_control_variable(formula):
    collection = OrderedSet()
    fv = get_free_variables(formula)
    for v in fv:
        if v.symbol_name().startswith("control_v_"):
            collection.add(v)
    return collection


def build_tree(control_vs, args):
    trees = []
    for control_v, arg in zip(control_vs, args):

        control_set = look_for_child_control_variable(arg)
        tree = OrderedSet()
        for child in control_set:
            ct = controll_variable_scope.get(child, None)
            if ct is not None:
                tree.add(ct)
        trees.append(tree)

        controll_varaible_eq[arg] = control_v
        controll_varaible_eq_r[control_v] = arg

    c_tree = Control_Tree(control_vs, trees)
    for control_v in control_vs:
        controll_variable_scope[control_v] = c_tree

    controll_variable.add(c_tree)
    for child_ts in trees:
        for child_t in child_ts:
            if (child_t in controll_variable):
                controll_variable.remove(child_t)


def build_symmetry_mapping(constraints):
    cs = [look_for_child_control_variable(cons) for cons in constraints]
    collections = []
    for control_v in cs:
        index = 0
        while len(control_v) > 0:
            if len(collections) <= index:
                sym = OrderedSet()
                collections.append(sym)
            else:
                sym = collections[index]
            sym.add(control_v.pop())
            index += 1

    for col in collections:
        sym_set = col
        for v in col:
            sym_res = control_var_sym.get(v, None)
            if sym_res is not None:
                sym_set = sym_set.union(sym_res)
        for v in col:
            control_var_sym[v] = sym_set

        new_constraint = [controll_varaible_eq_r[v] for v in col]
        build_symmetry_mapping(new_constraint)


def get_symmetry(assignments):
    new_constraint = OrderedSet()
    for ass in assignments:
        sym_set = control_var_sym.get(ass, None)
        if sym_set is not None:
            new_con = Or(sym_set)
            if new_con not in new_constraint:
                new_constraint.add(Or(sym_set))
                continue
        new_constraint.add(ass)

    return list(new_constraint)


def symmetry_sub(formula):
    result = []
    for f in formula:
        if f.is_symbol():
            convs = look_for_child_control_variable(f)
            res = get_symmetry(convs)
            f = substitute(f, dict([(con, res) for con, res in zip(convs, res)]))
        result.append(f)
    return result


from collections.abc import Iterable


class illFormedFormulaException(Exception):
    pass


def _polymorph_args_to_tuple(args, should_tuple=False):
    """ Helper function to return a tuple of arguments from args.

    This function is used to allow N-ary operators to express their arguments
    both as a list of arguments or as a tuple of arguments: e.g.,
       And([a,b,c]) and And(a,b,c)
    are both valid, and they are converted into a tuple (a,b,c) """

    if len(args) == 1 and isinstance(args[0], Iterable):
        args = args[0]
    if should_tuple:
        return tuple(args)
    else:
        return list(tuple(args))


def encode(formula, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):
    if isinstance(formula, Operator):
        res = formula.encode(assumption=assumption, include_new_act=include_new_act, exception=exception,
                             disable=disable, proof_writer=proof_writer)
        if formula.subs is not None:
            for target, src in formula.subs.items():
                res = target.sym_subs(src, encode(res, assumption=assumption, include_new_act=include_new_act,
                                                  exception=exception, disable=disable, proof_writer=proof_writer))
        return res
    else:
        if proof_writer:
            proof_writer.add_definition(formula, derived=False)
        return formula


def to_string(formula):
    if isinstance(formula, Operator):
        return formula.to_string()
    elif isinstance(formula, str):
        return formula
    else:
        return serialize(formula)


def invert(formula):
    if isinstance(formula, Operator):
        res = formula.invert()
        res.subs = formula.subs
        return res
    else:
        return Not(formula)


def DNF(formula):
    dnfs = to_DNF(formula)
    return [AND(dnf) for dnf in dnfs]


def to_DNF(formula):
    if isinstance(formula, Operator):
        return formula.to_DNF()
    else:
        return [simplify(formula)]


def to_CNF(formula):
    if isinstance(formula, Operator):
        return formula.to_CNF()
    else:
        return [simplify(formula)]


def sub(formula, source, target):
    if isinstance(formula, Operator):
        formula.sub(source, target)
        return formula
    else:
        return target.sym_subs(source, formula)


def slicing(formula, actions, reverse=False):
    if isinstance(formula, Operator):
        return formula.slicing(actions, reverse=reverse)
    else:
        bounded_variables = []
        fb = get_free_variables(formula)
        for action in actions:
            bounded_variables += action.get_all_variables()

        if len(set(fb) - set(bounded_variables)) == 0:
            if reverse:
                return None
            else:
                return formula
        else:
            if reverse:
                return formula
            else:
                return None


def update_context_map(context_map, action, context):
    attribute_of_interests = action.extract_mentioned_attributes(context)
    action_type = type(action)
    res = context_map.get(action_type, OrderedSet())
    res = res.union(attribute_of_interests)
    context_map[action_type] = res
    return context_map


def merge_context_map(map1, map2):
    for key, value in map2.items():
        m1_value = map1.get(key, OrderedSet())
        map1[key] = m1_value.union(value)

    return map1


def get_func_args(func):
    assert isinstance(func, type(get_func_args))
    return func.__code__.co_varnames


def exist(Action_Class, func, input_subs=None, reference=None):
    if isinstance(Action_Class, type([])):
        func_vars = list(get_func_args(func))
        # assert len(Action_Class) == len(func_vars)
        assert len(Action_Class) > 0
        if len(Action_Class) == 1:
            if input_subs:
                return exist(Action_Class[0], func, input_subs=input_subs[0])
            else:
                return exist(Action_Class[0], func)
        else:
            if input_subs:
                cur_input = input_subs[0]
                input_subs = input_subs[1:]
            else:
                cur_input = None
                input_subs = None
            new_func = lambda x: exist(Action_Class[1:], lambda *args: func(x, *args), input_subs=input_subs)
            return exist(Action_Class[0], new_func, input_subs=cur_input)
    elif isinstance(Action_Class, type):
        return Exists(Action_Class, _func(func), input_subs=input_subs, reference=reference)
    elif isinstance(Action_Class, UnionAction):
        return OR([Exists(AC, _func(func), input_subs=input_subs) for AC in Action_Class.actions])
    else:
        raise AssertionError


def forall(Action_Class, func, reference=None):
    if isinstance(Action_Class, type([])):
        func_vars = list(get_func_args(func))
        assert len(Action_Class) == len(func_vars)
        assert len(Action_Class) > 0
        if len(Action_Class) == 1:
            return forall(Action_Class[0], func)
        else:
            new_func = lambda x: forall(Action_Class[1:], lambda *args: func(x, *args))
            return forall(Action_Class[0], new_func)
    elif isinstance(Action_Class, type):
        return Forall(Action_Class, _func(func), reference=reference)
    elif isinstance(Action_Class, UnionAction):
        return AND([Forall(AC, _func(func)) for AC in Action_Class.actions])
    else:
        raise AssertionError


def _Summation(Action_class, value_func, filter_func):
    result = Summation.Sum_map.get((Action_class, value_func, filter_func), None)
    if result is None:
        result = Summation(Action_class, value_func, filter_func)
        Summation.Sum_map[(Action_class, value_func, filter_func)] = result
    else:
        print("summed before")
    return result


def ret_one(_):
    return Int(1)


def Count(Action_Class, filter_func, trigger_act=None, input_subs=None):
    return Summation(Action_Class, _func(ret_one), _func(filter_func), trigger_act=trigger_act, is_count=True,
                     input_subs=input_subs)


def Sum(Action_Class, value_func, filter_func, trigger_act=None, input_subs=None):
    if isinstance(Action_Class, type([])):
        func_vars_value = list(get_func_args(value_func))
        func_vars_filter = list(get_func_args(filter_func))
        assert len(Action_Class) == len(func_vars_value)
        assert len(Action_Class) == len(func_vars_filter)
        assert len(Action_Class) > 0

        if len(Action_Class) == 1:
            return Summation(Action_Class[0], value_func, filter_func)
        else:
            new_func_value = lambda x: Sum(Action_Class[1:], lambda *args: value_func(x, *args))
            new_func_filter = lambda x: Sum(Action_Class[1:], lambda *args: filter_func(x, *args))
            return Sum(Action_Class[0], new_func_value, new_func_filter)
    elif isinstance(Action_Class, type):
        return Summation(Action_Class, _func(value_func), _func(filter_func), trigger_act=trigger_act,
                         input_subs=input_subs)
    elif isinstance(Action_Class, UnionAction):
        return C_Summation(
            [Sum(AC, _func(value_func), _func(filter_func), input_subs=input_subs) for AC in Action_Class.actions])
    else:
        raise AssertionError


def Implication(l, r):
    if l == TRUE():
        return r
    if l == FALSE():
        return TRUE()
    if r == TRUE():
        return TRUE()
    if r == FALSE():
        return NOT(l)
    return OR(NOT(l), r)


class Operator():
    def __init__(self):
        self.subs = {}
        self.proof_lit = None
        self.proof_derived = False
        self.text_ref = None
        self.op = None

    def clear(self):
        self.subs = {}
        self.proof_lit = None
        self.proof_derived = False

    def encode(self, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):
        return

    def invert(self):
        return self

    def sub(self, source, target):
        if self.subs is None:
            self.subs = {target: source}
        else:
            self.subs.update({target: source})

    def to_DNF(self):
        pass

    def to_CNF(self):
        pass

    def slicing(self, actions, reverse=False):
        pass

    def __ge__(self, other):
        assert False

    def __gt__(self, other):
        assert False

    def __le__(self, other):
        assert False

    def __lt__(self, other):
        assert False

    def __add__(self, other):
        assert False

    def __sub__(self, other):
        assert False

    def to_string(self):
        return ""


class Arth_Operator(Operator):
    def __init__(self):
        super().__init__()

    def __ge__(self, other):
        return artop(self, other, _GE)

    def __gt__(self, other):
        return artop(self, other, _GT)

    def __le__(self, other):
        return artop(self, other, _LE)

    def __lt__(self, other):
        return artop(self, other, _LT)

    def __eq__(self, other):
        return artop(self, other, _EQ)

    def __add__(self, other):
        return artop(self, other, _Plus)

    def __sub__(self, other):
        return artop(self, other, _Minus)

    def to_string(self):
        # unimplemented
        assert False


def NOT(arg, polarity=True):
    if arg is None or arg == []:
        return TRUE()
    else:
        if isinstance(arg, Bool_Terminal):
            return invert(arg)
        elif isinstance(arg, Operator):
            return C_NOT(arg, polarity)
        else:
            return Not(arg)


class C_NOT(Operator):
    def __init__(self, arg, polarity=True):
        super().__init__()
        self.arg = arg
        self.polarity = polarity
        self.op = None

    def clear(self):
        super(C_NOT, self).clear()
        self.op = None
        clear(self.arg)

    def encode(self, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):

        if self.polarity:
            result = encode(invert(self.arg), assumption=assumption, include_new_act=include_new_act,
                            exception=exception,
                            disable=disable, proof_writer=proof_writer)
        else:
            result = encode(self.arg, assumption=assumption, include_new_act=include_new_act, exception=exception,
                            disable=disable, proof_writer=proof_writer)

        if self.polarity and proof_writer and not self.proof_derived:
            proof_writer.add_negation(self)
            self.proof_derived = True

        return result

    # if invert the not, then you get the argument
    def invert(self):
        if self.op:
            return self.op
        else:
            if self.polarity:
                self.op = self.arg
                # self.op.op = self
            else:
                assert False
        return self.op

    def to_DNF(self):
        if self.polarity:
            return to_DNF(invert(self.arg))
        else:
            return to_DNF(self.arg)

    def to_CNF(self):
        if self.polarity:
            return to_CNF(invert(self.arg))
        else:
            return to_CNF(self.arg)

    def slicing(self, actions, reverse=False):
        if self.polarity:
            return slicing(invert(self.arg), actions, reverse=reverse)
        else:
            return slicing(self.arg, actions, reverse=reverse)

    def generalize_encode(self, context=[]):
        return encode(self)

    def to_string(self):
        if self.polarity:
            return to_string("(! {})".format(to_string(self.arg)))
        else:
            return to_string(self.arg)


def should_use_gate(args):
    for arg in args:
        if isinstance(arg, Operator):
            return True
    return False


def artop(left, right, op):
    if isinstance(left, Operator) or isinstance(right, Operator):
        if is_arth_op(op):
            return Arth_Expression(left, right, op)
        else:
            return Compare_Binary_Expression(left, right, op)
    else:
        return op(left, right)


def propagate_polarity(term, pos, neg):
    if isinstance(term, Arth_Expression):
        term.propagate_polarity(pos, neg)
    elif isinstance(term, Summation):
        term.propagate_polarity(pos, neg)
    else:
        return


def op_str(op):
    if op == _GT:
        return ">"
    elif op == _GE:
        return ">="
    elif op == _LE:
        return "<="
    elif op == _LT:
        return "<"
    elif op == _Plus:
        return "+"
    elif op == _Minus:
        return "-"
    elif op == _EQ:
        return "=="
    elif op == _NEQ:
        return "!="
    else:
        assert False


def op_str_sleec(op):
    if op == ">":
        return _GT
    elif op == ">=":
        return _GE
    elif op == "<=":
        return _LE
    elif op == "<":
        return _LT
    elif op == "+":
        return _Plus
    elif op == "-":
        return _Minus
    elif op == "*":
        return _Multi
    elif op == "=":
        return _EQ
    elif op == "<>":
        return _NEQ
    else:
        assert False


def op_str_sleec_bool(op):
    if op == "and":
        return AND
    elif op == "or":
        return OR
    elif op == "=>":
        return Implication
    else:
        assert False


class Bool_Terminal(Operator):
    def __init__(self, value):
        super().__init__()
        self.value = value
        self.op = None

    def clear(self):
        super().clear()
        self.op = None

    def encode(self, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):
        if proof_writer:
            proof_writer.add_definition(self.value, derived=False, terminal_obj=self)
        return self.value

    def invert(self):
        if self.op:
            return self.op
        else:
            res = Bool_Terminal(Not(self.value))
            self.op = res
            res.op = self
            return res

    def to_string(self):
        return to_string(self.value)


class Arth_Expression(Arth_Operator):

    def __init__(self, left, right, operator, pos=True, neg=True):
        super().__init__()
        self.left = left
        self.right = right
        self.operator = operator

        # record polarity
        self.pos = pos
        self.neg = neg

    def encode(self, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):
        left_result = encode(self.left, assumption=assumption, include_new_act=include_new_act, exception=exception,
                             disable=disable, proof_writer=proof_writer)
        right_result = encode(self.right, assumption=assumption, include_new_act=include_new_act, exception=exception,
                              disable=disable, proof_writer=proof_writer)

        return self.operator(left_result, right_result)

    def to_string(self):
        left_str = to_string(self.left)
        right_str = to_string(self.right)
        return "( {} {} {})".format(left_str, op_str(self.operator), right_str)

    def invert(self):
        assert False

    def propagate_polarity(self, pos, neg):
        self.pos = pos
        self.neg = neg
        if self.operator == _Plus:
            propagate_polarity(self.left, pos, neg)
            propagate_polarity(self.right, pos, neg)
        elif self.operator == _Minus:
            propagate_polarity(self.left, pos, neg)
            propagate_polarity(self.right, neg, pos)
        else:
            assert False


class Compare_Binary_Expression(Operator):

    def __init__(self, left, right, operator, polarity=True):
        super().__init__()
        self.left = left
        self.right = right
        self.operator = operator
        self.polarity = polarity
        self.op = None

        if self.operator == _GE or self.operator == _GT:
            propagate_polarity(self.left, True, False)
            propagate_polarity(self.right, False, True)
        elif self.operator == _LE or self.operator == _LT:
            propagate_polarity(self.left, False, True)
            propagate_polarity(self.right, True, False)
        elif self.operator == _EQ or self.operator == _NEQ:
            propagate_polarity(self.left, True, True)
            propagate_polarity(self.right, True, True)

    def encode(self, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):
        left_result = encode(self.left, assumption=assumption, include_new_act=include_new_act, exception=exception,
                             disable=disable, proof_writer=proof_writer)
        right_result = encode(self.right, assumption=assumption, include_new_act=include_new_act, exception=exception,
                              disable=disable, proof_writer=proof_writer)
        if self.polarity:
            return self.operator(left_result, right_result)
        else:
            return Not(self.operator(left_result, right_result))

    def to_string(self):
        left_str = to_string(self.left)
        right_str = to_string(self.right)
        if self.polarity:
            return "( {} {} {})".format(left_str, op_str(self.operator), right_str)
        else:
            return "( {} {} {})".format(left_str, op_str(inverse_mapping(self.operator)), right_str)

    def invert(self):
        # now it actually matters

        if self.op is None:
            inverse_op = inverse_mapping(self.operator)
            if inverse_op is None:
                print('warning, uncaught operators')
                self.op = Compare_Binary_Expression(self.left, self.right, self.operator, polarity=not self.polarity)
                self.op.op = self
            else:
                self.op = Compare_Binary_Expression(self.left, self.right, inverse_op)
                self.op.op = self

        return self.op


def AND(*args):
    c_args = _polymorph_args_to_tuple(args)
    if c_args == [] or args is None:
        return TRUE()
    else:
        if should_use_gate(c_args):
            static_arg = frozenset(c_args)
            if static_arg in C_AND.cache:
                return C_AND.cache[static_arg]
            return C_AND(c_args)
        else:
            return And(_polymorph_args_to_tuple(args, should_tuple=True))


class C_AND(Operator):
    cache = {}

    def __init__(self, *args):
        super().__init__()
        self.arg_list = _polymorph_args_to_tuple(args)
        self.op = None
        C_AND.cache[frozenset(self.arg_list)] = self

    def clear(self):
        super(C_AND, self).clear()
        self.op = None
        for arg in self.arg_list:
            clear(arg)

    def encode(self, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):
        result_list = []
        for arg in self.arg_list:
            result_list.append(encode(arg, assumption=assumption, include_new_act=include_new_act, exception=exception,
                                      disable=disable, proof_writer=proof_writer))

        if proof_writer and not self.proof_derived:
            proof_writer.add_and(self)
            self.proof_derived = True

        return And(result_list)

    def invert(self):
        if self.op is None:
            arg_list = []
            for arg in self.arg_list:
                arg_list.append(invert(arg))
            self.op = OR(arg_list)
            self.op.op = self
        return self.op

    def to_DNF(self):
        sub_DNFS = [to_DNF(arg) for arg in self.arg_list]
        dnfs = []
        for sub_dnf in sub_DNFS:
            if dnfs == []:
                dnfs = sub_dnf
            else:
                if sub_dnf == []:
                    continue
                else:
                    temp = []
                    for dnf in dnfs:
                        for sub in sub_dnf:
                            temp.append(AND(dnf, sub))
                    dnfs = temp
        return dnfs

    def to_CNF(self):
        res = []
        for arg in self.arg_list:
            res += to_CNF(arg)
        return res

    def slicing(self, actions, reverse=False):
        sub_slices = [slicing(arg, actions, reverse=reverse) for arg in self.arg_list]
        sub_slices = [res for res in sub_slices if res is not None]
        return AND(sub_slices)

    def to_string(self):
        result_list = []
        for arg in self.arg_list:
            result_list.append(to_string(arg))
        return "({})".format(' & '.join(result_list))


def OR(*args):
    c_args = _polymorph_args_to_tuple(args)
    if c_args == [] or args is None:
        return FALSE()
    else:
        if should_use_gate(c_args):
            static_arg = frozenset(c_args)
            if static_arg in C_OR.cache:
                return C_OR.cache[static_arg]
            else:
                return C_OR(c_args)
        else:
            return Or(_polymorph_args_to_tuple(args, should_tuple=True))


def clear(arg):
    if isinstance(arg, Operator):
        arg.clear()


class C_OR(Operator):
    cache = {}

    def __init__(self, *args):
        super().__init__()
        self.arg_list = _polymorph_args_to_tuple(args)
        self.op = None
        C_OR.cache[frozenset(self.arg_list)] = self

    def clear(self):
        super(C_OR, self).clear()
        self.op = None
        for arg in self.arg_list:
            clear(arg)

    def encode(self, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):
        result_list = []
        for arg in self.arg_list:
            result_list.append(encode(arg, assumption=assumption, include_new_act=include_new_act, exception=exception,
                                      disable=disable, proof_writer=proof_writer))

        if proof_writer and not self.proof_derived:
            proof_writer.add_or(self)
            self.proof_derived = True

        if assumption:
            return _OR(result_list)
        else:
            return Or(result_list)

    def invert(self):
        if self.op is None:
            arg_list = []
            for arg in self.arg_list:
                arg_list.append(invert(arg))
            self.op = AND(arg_list)
            self.op.op = self
        return self.op

    def to_DNF(self):
        res = []
        for arg in self.arg_list:
            res += to_DNF(arg)
        return res

    def to_CNF(self):
        sub_CNFS = [to_CNF(arg) for arg in self.arg_list]
        cnfs = []
        for sub_cnf in sub_CNFS:
            if cnfs == []:
                cnfs = sub_cnf
            else:
                if sub_cnf == []:
                    continue
                else:
                    temp = []
                    for cnf in cnfs:
                        for sub in sub_cnf:
                            temp.append(OR(cnf, sub))
                    cnfs = temp
        return cnfs

    def slicing(self, actions, reverse=False):
        sub_slices = [slicing(arg, actions, reverse=reverse) for arg in self.arg_list]
        sub_slices = [res for res in sub_slices if res is not None]
        return OR(sub_slices)

    def to_string(self):
        result_list = []
        for arg in self.arg_list:
            result_list.append(to_string(arg))
        return "({})".format(' | '.join(result_list))


def _predicate(predicate, key_arg):
    pred = Predicate.Predicate_Cache.get(predicate, None)
    if pred is None:
        pred = Predicate(predicate, key_arg)
        Predicate.Predicate_Cache[predicate] = pred

    return pred


def make_bin_predicate(predicate):
    return make_predicate(predicate, 2)


def make_predicate(predicate, key_arg):
    pred = _predicate(predicate, key_arg)
    return lambda *args: pred.evaulate(*args)


def add_predicate_constraint(solver):
    for pred in Predicate.Predicate_Cache.values():
        if pred.predicate_constraints:
            res = encode(AND(pred.predicate_constraints))
            solver.add_assertion(res)
            # print("add predicate res {}".format(serialize(res)))
            pred.predicate_constraints.clear()


class Predicate(Operator):
    Predicate_Cache = {}

    def __init__(self, procedure, key_arg, size=100):
        super().__init__()
        self.procedure = procedure
        self.result_cache = dict()
        self.key_arg = key_arg
        self.predicate_constraints = []
        self.size = size

    def evaulate(self, *args):
        tuple_args = _polymorph_args_to_tuple(args)
        keys = tuple(list(tuple_args)[:self.key_arg])
        cache = self.result_cache.get(keys, None)
        if cache is None:
            cache = self.procedure(*args)
            for old_key, old_res in self.result_cache.items():
                self.predicate_constraints.append(
                    Implication(AND([EQ(keys[i], old_key[i]) for i in range(self.key_arg)]), EQ(cache, old_res)))
            self.result_cache[keys] = cache
            if len(self.result_cache) > self.size:
                self.result_cache.pop(next(iter(self.result_cache)))
                print("clean function dict")

        return cache

    def to_string(self, *args):
        res = self.evaulate(*args)
        return to_string(res)


def _func(procedure):
    func = Function.Function_cache.get(procedure, None)
    if func is None:
        func = Function(procedure)
        Function.Function_cache[procedure] = func

    return func


class Function(Operator):
    Function_cache = {}

    def __init__(self, procedure, polarity=True, arg_num=1):
        # create an concrete input based_on the type
        super().__init__()
        self.procedure = procedure
        self.polarity = polarity
        self.evaulated = []
        self.result_cache = dict()
        self.arg_num = arg_num
        self.op = None

    def clear(self):
        self.evaulated.clear()
        self.result_cache.clear()
        self.op = None

    def evaulate(self, input, assumption=False):
        # check multi-varaible input
        if self.arg_num > 1:
            assert len(input) == self.arg_num
            if isinstance(input, list):
                input = tuple(input)

        cache = self.result_cache.get(input, None)
        if cache is None:
            cache = self.procedure(input)
            self.result_cache[input] = cache

        if self.polarity:
            res = cache
        else:
            res = invert(cache)
        if assumption:
            self.evaulated.append(res)
        return res

    # check the slide effects
    def invert(self):
        if self.op is None:
            self.op = Function(self.procedure, polarity=not self.polarity, arg_num=self.arg_num)
            self.op.op = self
        return self.op

    def to_string(self, *args):
        res = self.evaulate(*args)
        return to_string(res)


temp_count = 0


def add_def(s, fml):
    global temp_count
    name = Symbol("def_{}".format(temp_count))
    temp_count += 1
    s.add_assertion(Iff(name, fml))
    return name


def relax_core(s, core, Fs):
    prefix = TRUE()
    Fs -= {f for f in set(core)}
    for i in range(len(core) - 1):
        prefix = add_def(s, And(core[i], prefix))
        Fs |= {add_def(s, Or(prefix, core[i + 1]))}


def get_assumption_core(solver):
    assumptions = solver.z3.unsat_core()
    pysmt_assumptions = [solver.converter.back(t) for t in assumptions]
    return pysmt_assumptions


minimize_memory = dict()
action_activity = dict()


def update_activity(act, round):
    old_round = minimize_memory.get(act, 0)
    old_act = action_activity.get(act, 10.0)
    decay_ratio = 0.8
    round_diff = round - old_round
    new_activity = old_act * (decay_ratio ** round_diff) + 1
    action_activity[act] = new_activity
    minimize_memory[act] = round


def maxsat(s, Fs, round=-1, namespace=None, relax_mode=False, background=None, eq_vars=None):
    cost = 0
    Fs0 = Fs.copy()
    if not background:
        background = OrderedSet()

    if not eq_vars:
        eq_vars = OrderedSet()

    while not s.solve(Fs.union(background).union(eq_vars)):
        # print("cost {}".format(cost))
        cost += 1
        # print("Solver start printing")
        # for clause in s.assertions:
        #     print(serialize(clause))
        # print("Solver end printing")
        # print("try to get assumption")
        # print(Fs.union(background).union(eq_vars))
        eq_core = [t for t in get_assumption_core(s) if t in eq_vars]
        # print(eq_core)
        if eq_core:
            for t in eq_core:
                s.add_assertion(Not(t))
                eq_vars.remove(t)
            continue

        core = [f for f in get_assumption_core(s) if f in Fs]
        # print(core)
        if round >= 0 and namespace is not None:
            for f in core:
                act = namespace.get(f, None)
                if act is not None:
                    update_activity(namespace[f], round)
                    # minimize_memory[namespace[f]] = round
        # print("relaxing core")
        if relax_mode:
            # if we are not interesting in the optimial solution, then we can get find
            # any maximal correction subset instead of the max solution
            max_clause = max(core, key=lambda c: action_activity.get(namespace[c], 10.0) if c in namespace else 0)
            Fs.remove(max_clause)
        else:
            relax_core(s, core, Fs)
        # print("next")
    model = s.get_model()
    return cost, {f for f in Fs0 if not model.get_py_value(f)}, model


def maxsat_model(s, Fs, background=None, eq_vars=None):
    cost = 0
    Fs0 = Fs.copy()

    if not background:
        background = OrderedSet()

    if not eq_vars:
        eq_vars = OrderedSet()

    while not s.solve(Fs.union(background).union(eq_vars)):

        eq_core = [t for t in get_assumption_core(s) if t in eq_vars]
        if eq_core:
            for t in eq_core:
                s.add_assertion(Not(t))
                eq_vars.remove(t)
            continue

        # print("cost {}".format(cost))
        cost += 1
        # print("try to get assumption")
        core = [f for f in get_assumption_core(s) if f in Fs]
        # print("relaxing core")
        relax_core(s, core, Fs)
        # print("next")
    model = s.get_model()
    return model, {f for f in Fs0 if not model.get_py_value(f)}


def mini_solve(solver, actions, vars, eq_vars, ignore_class=None):
    name_space = {}
    soft_constraints = OrderedSet()
    action_by_type = {}
    for act in actions:
        if (ignore_class is not None and type(act) in ignore_class) or act.disabled():
            continue

        act_type = type(act)
        previous_act = action_by_type.get(act_type, [])
        # if this action has not yet been previously constrained for minimization
        if not act.min_var:
            if act.under_encoded >= 0 and act.under_encoded <= len(previous_act):
                choice = []
                for more_act in previous_act[act.under_encoded:]:
                    choice.append(act.build_eq_constraint(more_act))
                act.min_var = FreshSymbol(template="MINFV%d")
                if act.under_var:
                    constraint = Implies(act.min_var, Or(act.under_var, Implies(act.presence, Or(choice))))
                else:
                    constraint = Implies(act.min_var, Implies(act.presence, Or(choice)))
            else:
                choice = []
                for more_act in previous_act:
                    choice.append(act.build_eq_constraint(more_act))
                act.min_var = FreshSymbol(template="MINFV%d")
                constraint = Implies(act.min_var, Or(choice))
            solver.add_assertion(constraint)
        soft_constraints.add(act.min_var)
        name_space[act.min_var] = act
        previous_act.append(act)
        action_by_type[act_type] = previous_act

    model, available = maxsat_model(solver, soft_constraints, background=vars, eq_vars=eq_vars)
    return model


def coordinate_ignored_actions(actions, model):
    result = []
    for act in actions:
        if model.get_py_value(act.presence):
            result.append(act)
    return result


shadow_dict = {}


def has_shadow(lit, solver):
    if lit in shadow_dict:
        return shadow_dict[lit]
    else:
        shadow_lit = FreshSymbol()
        solver.add_assertion(Iff(lit, shadow_lit))
        shadow_dict[lit] = shadow_lit
        return shadow_lit


def get_temp_act_constraint_minimize(solver, rules, vars, eq_vars, inductive_assumption_table=None,
                                     addition_actions=None, round=-1, disable_minimization=False, ignore_class=None,
                                     relax_mode=True, ub=False):
    should_block = True
    # short cut
    if (relax_mode and len(Exists.Temp_ACTs) == 1 or disable_minimization):
        unqiue_act = []
        for act in Exists.Temp_ACTs:
            exist_obj = Exists.Temp_ACTs.get(act)
            # print("log {}".format(act))
            unqiue_act.append((act, exist_obj))
        include_new_actions(unqiue_act, rules, should_block, inductive_assumption_table)
        return

    intermediate = OrderedSet()
    name_space = {}
    if addition_actions is None:
        addition_actions = []

    no_duplicate = len(addition_actions) > 0
    temp_actions = list(Exists.Temp_ACTs)
    soft_constraints = OrderedSet()
    ignored_actions = OrderedSet()
    action_by_type = {}
    # these are actions in the domain
    for act in addition_actions:
        if isinstance(act, _SUMObject):
            continue
        if act.disabled():
            continue

        if ignore_class is not None and type(act) in ignore_class:
            ignored_actions.add(act)
            continue

        act_type = type(act)
        previous_act = action_by_type.get(act_type, [])
        # if this action has not yet been previously constrained for minimization
        if not act.min_var:
            if act.under_encoded >= 0:
                choice = []
                assert act.under_encoded <= len(previous_act)
                for more_act in previous_act[act.under_encoded:]:
                    choice.append(act.build_eq_constraint(more_act))
                act.min_var = FreshSymbol(template="MINFV%d")
                if act.under_var:
                    constraint = Implies(act.min_var, Or(act.under_var, Implies(act.presence, Or(choice))))
                else:
                    constraint = Implies(act.min_var, Implies(act.presence, Or(choice)))
            else:
                choice = []
                for more_act in previous_act:
                    choice.append(act.build_eq_constraint(more_act))
                act.min_var = FreshSymbol(template="MINFV%d")
                constraint = Implies(act.min_var, Or(choice))
            solver.add_assertion(constraint)
        soft_constraints.add(act.min_var)
        intermediate.add(act)
        name_space[act.min_var] = act
        previous_act.append(act)
        action_by_type[act_type] = previous_act

    prev_act = dict()
    for act in temp_actions:
        if act.disabled():
            continue
        if ignore_class is not None and type(act) in ignore_class:
            ignored_actions.add(act)
            continue
        # update round info
        if not no_duplicate:
            if round >= 0:
                old_round = minimize_memory.get(act, -1)
                if old_round < 0:
                    minimize_memory[act] = round
        if act.under_var:
            # only consider temp act that has been constrained before
            # other act are introduced from trace checking, they should not be considered at all
            # if addition_actions and isinstance(act, _SUMObject):
            #     shadow_lit = has_shadow(act.under_var, solver)
            #     soft_constraints.add(shadow_lit)
            soft_constraints.add(act.under_var)
            intermediate.add(act)
            name_space[act.under_var] = act

    # filtering phase
    filtering_threshold = 5
    filtered_soft_constraints = OrderedSet()
    # print("Solver start printing")
    # for clause in solver.assertions:
    #     print(serialize(clause))
    # print("Solver end printing")
    # print("try to get assumption")
    i_core = [f for f in get_assumption_core(solver) if f in soft_constraints]
    # print("i _Core {}".format(str(i_core)))
    if len(i_core) == 1:
        act = name_space[i_core[0]]
        unqiue_act = []
        exist_obj = Exists.Temp_ACTs.get(act)
        unqiue_act.append((act, exist_obj))
        include_new_actions(unqiue_act, rules, should_block, inductive_assumption_table)
        return

    if round >= 0 and relax_mode and not no_duplicate:
        for act in intermediate:
            if minimize_memory.get(act, -1) >= round - filtering_threshold:
                filtered_soft_constraints.add(act.under_var)

        # print("diff {} {}".format(len(soft_constraints), len(filtered_soft_constraints)))
        cost, available, model = maxsat(solver, filtered_soft_constraints, round, name_space, relax_mode=relax_mode,
                                        background=vars, eq_vars=eq_vars)
        unqiue_act = []
        available_ignored_act = coordinate_ignored_actions(ignored_actions, model)
        if len(available) + len(available_ignored_act) >= 1:
            # print("filtered successful")
            for node in available:
                act = name_space[node]
                exist_obj = Exists.Temp_ACTs.get(act)
                if exist_obj is not None:
                    unqiue_act.append((act, exist_obj))

            for act in available_ignored_act:
                exist_obj = Exists.Temp_ACTs.get(act)
                if exist_obj is not None:
                    unqiue_act.append((act, exist_obj))

            # now include the temp actions into the universe, this may introduce duplicate actions
            include_new_actions(unqiue_act,
                                rules, should_block, inductive_assumption_table, ub=ub)
            return model
    # print("filtered unsuccessful")

    cost, available, model = maxsat(solver, soft_constraints, round, name_space, relax_mode=relax_mode, background=vars,
                                    eq_vars=eq_vars)
    # print("available {}".format(str(available)))
    if no_duplicate:
        new_cost, new_available, new_name_space, new_model = no_duplicate_filter(available, name_space, solver,
                                                                                 soft_constraints, vars, eq_vars, round)
        if new_name_space:
            available = new_available
            name_space = new_name_space
            model = new_model

    available_ignored_act = coordinate_ignored_actions(ignored_actions, model)
    unqiue_act = []
    if not no_duplicate:
        assert len(available) + len(available_ignored_act) >= 1

    # print("-"*10)
    for node in available:
        if node in name_space:
            act = name_space[node]
            exist_obj = Exists.Temp_ACTs.get(act)
            if exist_obj is not None:
                unqiue_act.append((act, exist_obj))
                # print(act.get_record(model, debug=False))

    for act in available_ignored_act:
        exist_obj = Exists.Temp_ACTs.get(act)
        if exist_obj is not None:
            unqiue_act.append((act, exist_obj))

    # now include the temp actions into the universe, this may introduce duplicate actions
    include_new_actions(unqiue_act,
                        rules, should_block, inductive_assumption_table, ub=ub)

    return model


def no_duplicate_filter(available, names_pace, solver, soft_constraints, vars, eq_vars, round):
    prevs_act = {}
    new_soft = OrderedSet()
    new_namespace = dict()
    solver.push()
    additional_bg = OrderedSet()
    for a in available:
        if a not in names_pace:
            continue
        act = names_pace[a]
        if Exists.Temp_ACTs.get(act):
            if isinstance(act, _SUMObject):
                additional_bg.add(act.presence)
            col = prevs_act.get(type(act), [])
            fv = FreshSymbol(template="NoDP%d")
            new_soft.add(fv)
            solver.add_assertion(Implies(fv, OR([EQ(act, pre) for pre in col])))
            col.append(act)
            prevs_act[type(act)] = col
            new_namespace[fv] = act

    cost, available, model = maxsat(solver, new_soft.union(soft_constraints), round, namespace=None, relax_mode=False,
                                    background=vars.union(additional_bg),
                                    eq_vars=eq_vars)
    # print("the cost is {}".format(len(available)))
    solver.pop()
    return cost, available, new_namespace, model


def include_new_actions(unqiue_act, rules, should_block=False, inductive_assumption_table=None, ub=False):
    for act, exist_obj in unqiue_act:
        # print(type(act))
        # print(exist_obj.to_string())
        Exists.Temp_ACTs.pop(act)
        act.make_permanent()
        new_action = act
        exist_obj.act_include = new_action
        Exists.new_included.add(new_action)
        if act in action_activity:
            action_activity.pop(act)
        # should we add inductive assumption
        if inductive_assumption_table is not None and should_block:
            # now check if the blocking clause is given
            if isinstance(exist_obj, Summation):
                continue
            blocking_clause = exist_obj.blocking_clause
            if blocking_clause is not None:
                assumption = blocking_clause(new_action)
                inductive_assumption_table[assumption] = {new_action}
                if isinstance(rules, set):
                    rules.add(assumption)
                elif isinstance(rules, list):
                    rules.append(assumption)

        if ub and len(type(new_action).collect_list) < 10:
            if isinstance(exist_obj, Summation):
                continue
            assumption = Implication(NOT(new_action.presence), NOT(exist(type(new_action), exist_obj.func.procedure)))
            if isinstance(rules, set):
                rules.add(assumption)
            elif isinstance(rules, list):
                rules.append(assumption)

        # if isinstance(act, _SUMObject):
        #     extension = extended_sum_func.evaulate(act)
        #     encode(extension)
        #     # encode(extended_sum_func)
        #     # extended_sum_func.evaulate(act)
        #     exists_extension = extension.arg_list[1]
        #     attach_obj = exists_extension.act_non_include
        #     print(type(attach_obj))
        #     Exists.Temp_ACTs.pop(attach_obj)
        #     attach_obj.make_permanent()
        #     exists_extension.act_include = attach_obj
        #     Exists.new_included.add(attach_obj)


def get_temp_act_constraints(checking=False):
    constraints = []
    type_constraints = {}
    if checking:
        compare_dict = Exists.check_ACTS
    else:
        compare_dict = Exists.Temp_ACTs

    vars = OrderedSet()
    for act in compare_dict:
        if not checking:
            var, constraint = act.under_constraint()
            vars.add(var)
            constraints.append(constraint)
        else:
            if isinstance(act, _SUMObject):
                constraints.append(Not(act.presence))
                continue
            choice_list = []
            act_type = type(act)
            for t_action in act_type.collect_list:
                choice_list.append(act.build_eq_constraint(t_action))
            choice_constraint = Implies(act.presence, Or(choice_list))
            result = Or(choice_constraint)
            constraints.append(result)
            type_constraints[act_type] = (act, result)

    if checking:
        compare_dict.clear()

    # constraints += undate_overapprox()
    return constraints, vars


def analyzing_temp_act(model):
    unqiue_act = OrderedSet()
    for act in Exists.Temp_ACTs:
        act_type = type(act)
        if model.get_py_value(act.presence):
            res = True
            for t_action in act_type.collect_list:
                if act.model_equal(model, t_action):
                    print("find non-unique")
                    res = False
                    break
            if res:
                exist_obj = Exists.Temp_ACTs.get(act)
                unqiue_act.add((act, exist_obj))
    # now include the temp actions into the universe
    for act, exist_obj in unqiue_act:
        Exists.Temp_ACTs.pop(act)
        new_action = exist_obj.input_type()
        exist_obj.act_include = new_action
        Exists.new_included.add(new_action)


class Exists(Operator):
    Temp_ACTs = dict()
    check_ACTS = dict()
    new_included = OrderedSet()
    count = 0

    def __init__(self, input_type, func, input_subs=None, reference=None):
        super().__init__()
        if not isinstance(func, Function):
            raise illFormedFormulaException("Exists: {} is not a Function".format(func))

        self.id = Exists.count
        Exists.count += 1
        self.input_type = input_type
        self.func = func
        self.act_include = None
        self.act_non_include = None
        self.op = None
        self.blocking_clause = None
        self.input_subs = input_subs
        self.print_act = self.input_type(print_only=True, input_subs=self.input_subs)
        self.print_statement = None
        self.reference = reference

    def clear(self):
        super(Exists, self).clear()
        self.act_include = None
        self.act_non_include = None
        self.op = None
        self.blocking_clause = None
        self.print_statement = None
        self.func.clear()

    def __repr__(self):
        return "Exist_{}".format(self.id)

    def __hash__(self):
        return hash(self.__repr__())

    def get_holding_obj(self, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):
        if not include_new_act:
            if self.act_include is not None:
                action = self.act_include
            else:
                if self.act_non_include is None:
                    self.act_non_include = self.input_type(temp=True, input_subs=self.input_subs)
                action = self.act_non_include
        else:
            if self.act_include is None:
                self.act_include = self.input_type(temp=False, input_subs=self.input_subs)
            action = self.act_include

        return action

    def encode(self, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):
        if not include_new_act:
            if self.act_include is not None:
                action = self.act_include
            else:
                if self.act_non_include is None:
                    self.act_non_include = self.input_type(temp=True, input_subs=self.input_subs)
                action = self.act_non_include
        else:
            if self.act_include is None:
                self.act_include = self.input_type(temp=False, input_subs=self.input_subs)
            action = self.act_include

        eval_result = self.func.evaulate(action, assumption=assumption)
        if self.reference:
            presence = Bool_Terminal(action.presence)
            text_ref[presence] = self.reference
        else:
            presence = action.presence
        application_res = AND(presence, eval_result)
        if proof_writer and not self.proof_derived:
            proof_writer.derive_exists_rule(self, action, application_res)
            self.proof_derived = True

        base_constraint = encode(application_res,
                                 assumption=assumption, include_new_act=include_new_act, exception=exception,
                                 disable=disable, proof_writer=proof_writer)

        if include_new_act:
            Exists.new_included.add(action)
        elif not include_new_act and action == self.act_non_include and action != self.act_include:
            if disable:
                constraints = []
                if isinstance(action, _SUMObject):
                    constraints.append(Not(action.presence))
                choice_list = []
                act_type = type(action)
                for t_action in act_type.collect_list:
                    choice_list.append(action.build_eq_constraint(t_action))
                choice_constraint = Implies(action.presence, Or(choice_list))
                result = Or(choice_constraint)
                constraints.append(result)
                base_constraint = And(base_constraint, And(constraints))
            else:
                # exist_obj = Exists.Temp_ACTs.get(action, None)
                # assert exist_obj is None or exist_obj == self
                Exists.Temp_ACTs[action] = self

        return base_constraint

    def invert(self):
        if self.op is None:
            self.op = Forall(self.input_type, invert(self.func), reference=self.reference)
            self.op.op = self
        return self.op

    def to_string(self):
        return "EXISTS {}: {}. ({}_presence & {})".format(self.print_act.print_name, self.input_type.action_name,
                                                          self.print_act.print_name,
                                                          self.func.to_string(self.print_act))

    def generalize_encode(self):
        action = self.input_type(temp=True)
        return

    def to_DNF(self):
        raise NotImplementedError("DNF for quantified formula is not ready")

    def get_print_statement(self):
        if not self.print_statement:
            self.print_statement = self.func.evaulate(self.print_act)
        return self.print_statement


def add_forall_defs(solver):
    for constraint in Forall.pending_defs:
        # print("add pending_ {}".format(serialize(constraint)))
        solver.add_assertion(constraint)
    Forall.pending_defs.clear()


class C_Summation(Arth_Operator):
    def __init__(self, *args):
        super().__init__()
        self.arg_list = _polymorph_args_to_tuple(args)
        self.op = None

    def encode(self, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):
        starting = Int(0)
        for arg in self.arg_list:
            starting += (encode(arg, assumption=assumption, include_new_act=include_new_act, exception=exception,
                                disable=disable, proof_writer=proof_writer))
        return starting

    def invert(self):
        print("invert is unsupported for Summation")


history = OrderedSet()
upper_bound = {}
lower_bound = {}


def model_based_gc(ACTION, model, solver, EQ_assumption, assumptions=None, strengthen=True,
                   value_bound_assumption=False):
    """
    probe and attempt to merge relational object. The oribing and merging is based on the minimal
    model of the over-approximation
    """
    if not assumptions:
        assumptions = []
    for action in ACTION:

        if action == _SUMObject:
            continue

        # filtered_objects = filter(lambda obj: model.get_py_value(obj.presence) and hasattr(obj, "time"), all_objects)
        # sorted_objects = sorted(action.snap_shot, key=lambda obj : model.get_py_value(obj.time) if hasattr(obj, "time") else 0)
        object_dict = dict()
        collection = [obj for obj in action.snap_shot if not obj.disabled() and model.get_py_value(obj.presence)]

        # try to learn the value upper and lower bound for variables presented in the trace
        # assert them as assertions (in a form of local search)
        if value_bound_assumption and hasattr(action, "attr_order"):
            for obj in collection:
                for attr in action.attr_order:
                    var = getattr(obj, attr)
                    cur_val = model.get_py_value(var)
                    var_upper_bound, upper_var_symbol = upper_bound.get(var, (None, None))
                    if not upper_var_symbol or cur_val > var_upper_bound:
                        assert (not upper_var_symbol in EQ_assumption)
                        var_upper_bound = cur_val
                        upper_var_symbol = FreshSymbol(template="upper%d")
                        EQ_assumption.add(upper_var_symbol)
                        solver.add_assertion(Implies(upper_var_symbol, var_upper_bound >= var))
                        upper_bound[var] = var_upper_bound, upper_var_symbol

                    var_lower_bound, lower_var_symbol = lower_bound.get(var, (None, None))
                    if not lower_var_symbol or cur_val < var_lower_bound:
                        assert (not lower_var_symbol in EQ_assumption)
                        var_lower_bound = cur_val
                        lower_var_symbol = FreshSymbol(template="lower%d")
                        EQ_assumption.add(lower_var_symbol)
                        solver.add_assertion(Implies(lower_var_symbol, var_lower_bound <= var))
                        lower_bound[var] = var_lower_bound, lower_var_symbol

        for obj in collection:
            key = obj.get_record(model, debug=False)
            k_list = object_dict.get(key, [])
            k_list.append(obj)
            object_dict[key] = k_list

        for k_list in object_dict.values():
            for i in range(len(k_list)):
                obj_1 = k_list[i]
                for j in range(i + 1, len(k_list)):
                    obj_2 = k_list[j]
                    if (obj_1, obj_2) in history:
                        continue
                    else:
                        history.add((obj_1, obj_2))

                    solver.push()
                    solver.add_assertion(NEQ(obj_1, obj_2))
                    if not solver.solve(assumptions):
                        mergable = True
                    else:
                        mergable = False
                    solver.pop()
                    if mergable:
                        print("merged")
                        solver.add_assertion(EQ(obj_1, obj_2))
                        break
                    else:
                        # we can make an assumption
                        var = FreshSymbol(template="EQ%d")
                        if var not in EQ_assumption:
                            solver.add_assertion(Implies(var, EQ(obj_1, obj_2)))
                            EQ_assumption.add(var)
                        else:
                            assert False

                        if obj_1.presence != obj_2.presence:
                            solver.push()
                            solver.add_assertion(Xor(obj_1.presence, obj_2.presence))
                            if not solver.solve(assumptions):
                                iff = True
                            else:
                                iff = False
                            solver.pop()
                            if iff:
                                # print("strengthened p")
                                # obj_2.presence = obj_1.presence
                                solver.add_assertion(Iff(obj_1.presence, obj_2.presence))

                        if strengthen:
                            if hasattr(type(obj_1), "attr_order"):
                                for attr in type(obj_1).attr_order:
                                    attr1 = getattr(obj_1, attr)
                                    attr2 = getattr(obj_2, attr)
                                    if attr1 != attr2:
                                        solver.push()
                                        solver.add_assertion(Not(EqualsOrIff(attr1, attr2)))
                                        if not solver.solve(assumptions):
                                            iff = True
                                        else:
                                            iff = False
                                        solver.pop()
                                        if iff:
                                            # print("strengthened {}".format(attr))
                                            # setattr(obj_2, attr, attr1)
                                            solver.add_assertion(EqualsOrIff(attr1, attr2))


def clean_up_action(s, assumptions, ACT):
    if ACT == _SUMObject:
        return
    if len(ACT.syn_collect_list) > ACT.threshold:
        ACT.threshold = int(ACT.threshold * ACT.increase_ratio)
        for act in ACT.syn_collect_list:
            test_var = assumptions.union([act.presence])
            if not s.solve(test_var):
                if act.disabled():
                    continue
                s.add_assertion(Not(act.presence))
                if act.under_var:
                    s.add_assertion(Not(act.under_var))
                act.disable()
                print("disabled {}".format(act))


def summation_clean_up(s, assumptions):
    if len(Summation.collections) > _SUMObject.threshold:
        _SUMObject.threshold = int(_SUMObject.threshold * _SUMObject.increase_ratio)
        for sum in Summation.collections:
            if sum.has_action():
                action = sum.get_action()
                if action.disabled():
                    continue
                test_var = assumptions.union([action.presence])
                if not s.solve(test_var):
                    s.add_assertion(Not(action.presence))
                    print("disabled action {}".format(action))
                    action.disable()
                    while sum.has_child():
                        new_sum, new_act = sum.act_include.child_sum
                        if not new_act.disabled():
                            s.add_assertion(Not(new_act.presence))
                            new_act.disable()
                        if not new_sum.get_action().disabled():
                            s.add_assertion(Not(new_sum.get_action().presence))
                            new_sum.get_action().disable()
                        sum = new_sum

        for sum in Summation.frontier:
            if sum.has_action:
                action = sum.get_action()
                test_var = assumptions.union([action.presence])
                if not s.solve(test_var):
                    s.add_assertion(Not(action.presence))
                    action.disable()
                    if sum.has_child():
                        sum.non_act_include.child_sum[1].disable()


class _SUMObject(Action):
    count = 0
    collect_list = []
    under_approx_counter = 0
    under_approx_vars = [Symbol("_SUMObject_under_0")]
    action_name = "_SUMObject"
    temp_collection_set = OrderedSet()
    threshold = 5
    increase_ratio = 10
    snap_shot = []

    def __init__(self, input_type, value_func, filter_func, temp=False, is_count=False, input_subs=None, pos=True,
                 neg=True,
                 print_only=False):
        self.input_type = input_type
        self.value_func = value_func
        self.filter_func = filter_func
        self.token = 'sum_presence_{}'.format(str(_SUMObject.count))
        self.presence = Symbol('sum_presence_{}'.format(str(_SUMObject.count)))
        self.value = Symbol('sum_value_{}'.format(str(_SUMObject.count)), INT)
        self.time = Symbol('sum_time_{}'.format(str(_SUMObject.count)), INT)
        self.constraint = TRUE()
        self.delayed_constraint = []
        # self.time = Int(0)
        self.child_sum = None
        self.under_encoded = False
        self.parent = None
        self.parent_info = None
        self.is_disabled = False
        self.is_count = is_count
        self.input_subs = input_subs
        self.pos = pos
        self.neg = neg
        self.encoded_actions = {}
        _SUMObject.count += 1

        if temp:
            self.under_encoded = 0
        else:
            self.under_encoded = -1

        self.min_var = None
        self.under_var = None
        if not print_only:
            if not temp:
                type(self).collect_list.append(self)
            else:
                type(self).temp_collection_set.add(self)

    def sym_subs(self, other, context):
        subs_dict = dict([(self.presence, other.presence), (self.value, other.value)])
        return substitute(context, subs_dict)

    def make_permanent(self):
        if self in type(self).temp_collection_set:
            type(self).collect_list.append(self)
            type(self).temp_collection_set.remove(self)

    def under_encode(self, assumption=False, include_new_act=False, exception=None, disable=None,
                     include_considered=False):
        consider_exception = not exception is None
        starting = Int(0)
        under_starting = Int(0)  # the under apprix
        if include_considered and self.child_sum is not None:
            child_sum, action = self.child_sum
            assert self.pos
            if (not consider_exception) or (not action in exception):
                # if there is a child, then you want to grow, therefore, under is starting
                condition = encode(AND(action.presence, self.filter_func.evaulate(action)), assumption=assumption,
                                   include_new_act=include_new_act, exception=exception,
                                   disable=disable)
                value = encode(self.value_func.evaulate(action),
                               assumption=assumption, include_new_act=include_new_act, exception=exception,
                               disable=disable)
                starting = child_sum.under_value + ITE(condition, value, Int(0))
                under_starting = starting
        else:
            considered = OrderedSet()
            for action in self.input_type.snap_shot:
                if (not consider_exception) or (not action in exception):
                    if action in self.encoded_actions:
                        cond, neg_cond, res_pos, res_neg = self.encoded_actions[action]
                        if self.pos:
                            encode(cond)
                            starting += res_pos
                        if self.neg:
                            encode(neg_cond)
                            under_starting += res_neg
                    else:
                        condition = AND(action.presence, self.filter_func.evaulate(action))
                        value = encode(self.value_func.evaulate(action),
                                       assumption=assumption, include_new_act=include_new_act, exception=exception,
                                       disable=disable)

                        # print ("value {}".format(serialize(value)))
                        deduplicate_condition = AND([NEQ(action, explored_action) for explored_action in considered])
                        cond = AND(condition, deduplicate_condition)
                        neg_cond = None
                        ite_result = None
                        under_ite_result = None
                        if self.pos:
                            # neg_cond = NOT(cond)
                            # fresh_ite_var = FreshSymbol(template="ite%d", typename=INT)
                            res_cond = encode(cond, assumption=assumption, include_new_act=include_new_act,
                                              exception=exception,
                                              disable=disable)
                            ite_result = ITE(res_cond, value, Int(0))
                            starting += ite_result

                        if self.neg:
                            neg_cond = NOT(cond)
                            under_ite_result = ITE(
                                encode(neg_cond, assumption=assumption, include_new_act=include_new_act,
                                       exception=exception,
                                       disable=disable), Int(0), value)
                            under_starting += under_ite_result

                        self.encoded_actions[action] = cond, neg_cond, ite_result, under_ite_result
                        considered.add(action)
                    # print("res cond {}".format(serialize(res_cond)))
                    # neg_res_cond = encode(neg_cond, assumption=assumption, include_new_act=include_new_act, exception=exception,
                    # #                disable=disable)
                    # ite_result = ITE(res_cond, value, Int(0))
                    # under_ite_result = ITE(
                    #     encode(NOT(cond), assumption=assumption, include_new_act=include_new_act, exception=exception,
                    #            disable=disable), Int(0), value)
                    # # print("under cond {}".format(serialize(under_ite_result)))
                    # starting += ite_result
                    # under_starting += under_ite_result
                    # considered.add(action)
        if self.pos and not self.neg:
            return starting, starting
        if self.neg and not self.pos:
            return under_starting, under_starting
        if self.pos and self.neg:
            return starting, under_starting
        else:
            assert False
        # return starting, under_starting

    def get_child_sum(self):
        return self.child_sum

    def set_child_sum(self, summation):
        assert self.child_sum is None or self.child_sum == summation
        self.child_sum = summation

    def build_eq_constraint(self, other, consider_time=True, exceptions=None):
        if exceptions is None:
            exceptions = OrderedSet()
        if not consider_time:
            exceptions.add("time")
        if type(self) != type(other):
            return FALSE()
        if self == other:
            return TRUE()
        else:
            if self.value_func != other.value_func or self.filter_func != other.filter_func:
                return FALSE()
            else:
                return And(_EQ(self.value, other.value), Iff(self.presence, other.presence))

    def same_sum(self, other):
        return type(self) == type(
            other) and self.value_func == other.value_func and self.filter_func == other.filter_func

    def conflicting_sum(self, other):
        if self == other:
            return FALSE()
        if self.same_sum(other):
            return NEQ(self.value, other.value)
        else:
            return FALSE()

    def disabled(self):
        return self.is_disabled or self.presence is FALSE()

    def disable(self):
        self.is_disabled = True
        self.presence = FALSE()

    def get_record(self, model, debug=True, mask=None):
        if debug:
            pars = "({})".format(', '.join(
                ["{}={}".format(str(getattr(self, attr)), str(model.get_py_value(getattr(self, attr)))) for attr in
                 ["value", "presence", "time"]]))
            return pars
        else:
            pars = "({} {})".format(self.input_type, ', '.join(
                ["{}={}".format(attr, str(model.get_py_value(getattr(self, attr)))) for attr in
                 ["value", "presence", "time"]]))
            return pars

    def under_constraint(self):
        assert self.under_encoded >= 0
        if not self.under_var:
            self.under_var = FreshSymbol()
            return self.under_var, Implies(self.under_var, Not(self.presence))
        else:
            return self.under_var, TRUE()
        # act_type = type(self)
        # considered_len = self.under_encoded
        # current_len = len(act_type.collect_list)
        # if not current_len:
        #     self.under_var = FreshSymbol()
        #     constraint = Implies(self.under_var, Not(self.presence))
        #     return self.under_var, constraint
        # else:
        #     if considered_len == current_len:
        #         return self.under_var, TRUE()
        #     else:
        #         new_var = FreshSymbol()
        #         choice_list = []
        #         for t_action in act_type.collect_list[self.under_encoded:]:
        #             choice_list.append(self.build_eq_constraint(t_action))
        #
        #         choice_constraint = Implies(self.presence, Or(choice_list))
        #         if self.under_encoded:
        #             constraint =  Implies(new_var, Or(self.under_var, choice_constraint))
        #         else:
        #             constraint = Implies(new_var, choice_constraint)
        #
        #         self.under_encoded = current_len
        #         self.under_var = new_var
        #         return self.under_var, constraint


class Summation(Arth_Operator):
    current_under = {}
    collections = []
    frontier = []
    under_initialized = False

    def __init__(self, input_type, value_func, filter_func, trigger_act=None, is_count=False, input_subs=None):
        super().__init__()
        assert isinstance(value_func, Function)
        assert isinstance(filter_func, Function)
        assert 1 == value_func.arg_num and 1 == filter_func.arg_num

        self.input_type = input_type
        self.value_func = value_func
        self.filter_func = filter_func
        self.act_include = None
        self.act_non_include = None
        self.under_value = Symbol("sum_under_{}".format(str(len(Summation.collections))), INT)
        self.id = len(Summation.collections)
        self.under_encoded = 0
        self.under_var = None
        self.inv_init = False
        self.parent_info = trigger_act
        self.is_count = is_count
        self.input_subs = input_subs
        Summation.collections.append(self)
        Summation.frontier.append(self)
        self.pos = True
        self.neg = True

    def __repr__(self):
        return "SUM_{}".format(self.under_value)

    def __hash__(self):
        return hash(self.__repr__())

    def propagate_polarity(self, pos, neg):
        self.pos = pos
        self.neg = neg

    def add_inv(self, solver):
        if not self.inv_init and self.has_action():
            self.inv_init = True
            solver.add_assertion(self.get_action().value >= self.under_value)
            # print("add assertion add_inv {}".format(serialize(self.get_action().value >= self.under_value)))
            if self.parent_info:
                solver.add_assertion(Implies(Not(self.parent_info.presence), Not(self.get_action().presence)))
                # print("add assertion add_inv {}".format(serialize(Implies(Not(self.parent_info.presence), Not(self.get_action().presence)))))
            # solver.add_assertion(Implies(Not(self.get_action().presence), EQ(self.get_action().value, self.under_value)))

    def encode(self, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):
        if not include_new_act:
            if self.act_include is not None:
                action = self.act_include
            else:
                if self.act_non_include is None:
                    self.act_non_include = _SUMObject(self.input_type, self.value_func, self.filter_func, temp=True,
                                                      is_count=self.is_count, input_subs=self.input_subs, pos=self.pos,
                                                      neg=self.neg)
                    self.act_non_include.parent = self
                    self.act_non_include.parent_info = self.parent_info
                action = self.act_non_include
        else:
            if self.act_include is None:
                self.act_include = _SUMObject(self.input_type, self.value_func, self.filter_func,
                                              is_count=self.is_count, input_subs=self.input_subs, pos=self.pos,
                                              neg=self.neg)
                self.act_include.parent = self
                self.act_include.parent_info = self.parent_info
            action = self.act_include

        if include_new_act:
            Exists.new_included.add(action)
        elif not include_new_act and action == self.act_non_include and action != self.act_include:
            if disable:
                Exists.check_ACTS[action] = self
            else:
                # exist_obj = Exists.Temp_ACTs.get(action, None)
                # assert exist_obj is None or exist_obj == self
                Exists.Temp_ACTs[action] = self

        if disable:
            under_value, _ = action.under_encode(assumption, include_new_act, exception, disable)
            return under_value
        else:
            under_value = self.under_value

        return ITE(action.presence, action.value, under_value)

    def has_action(self):
        return self.act_include is not None or self.act_non_include is not None

    def get_action(self):
        if self.act_include is not None:
            action = self.act_include
        elif self.act_non_include is not None:
            action = self.act_non_include
        else:
            assert False

        return action

    def update_under(self, include_considered=True):
        if include_considered:
            ground_value, under_value = self.get_under(include_considered=True)
        else:
            assert False
        return GE(self.under_value, under_value), EQ(self.under_value, ground_value)

    def get_under(self, include_considered=True):
        if include_considered:
            result = Summation.current_under.get(self.id, None)
            if result is None:
                result = self.get_action().under_encode(include_considered=include_considered)
                Summation.current_under[self.id] = result
            return result
        else:
            return self.get_action().under_encode(include_considered=include_considered)

    def invert(self):
        print("invert is unsupported for Summation")

    def get_value(self, model):
        return (model[self.under_value], model[self.act_include.value])

    def has_child(self):
        return self.act_include and self.act_include.child_sum

    def get_child(self):
        return self.act_include.child_sum[0]


def reset_underapprox(solver):
    if Summation.under_initialized:
        solver.pop()


def update_underapprox(solver):
    Summation.under_initialized = True
    Summation.current_under.clear()
    new_frontier = []
    # print("frontier:  {}".format(str(Summation.frontier)))
    for summation in Summation.frontier:
        if summation.has_action():
            summation.add_inv(solver)
            action = summation.get_action()
            under, over = summation.update_under()
            if action.child_sum:
                child_sum, child_action = action.child_sum
                solver.add_assertion(over)
                # print("update assertion  {}".format(serialize(over)))
                solver.add_assertion(under)
                # print("update assertion  {}".format(serialize(under)))
                child_sum_value = child_sum.get_action().value
                solver.add_assertion(Implies(action.presence, EQ(action.value,
                                                                 child_sum_value + summation.value_func.evaulate(
                                                                     child_action))))
                solver.add_assertion(Implies(Not(action.presence), Not(child_sum.get_action().presence)))
                solver.add_assertion(Implies(Not(child_action.presence), Not(child_sum.get_action().presence)))
                solver.add_assertion(IFF(action.presence, child_action.presence))
            if not action.child_sum:
                solver.add_assertion(under)
                # print("update assertion  {}".format(serialize(under)))
                new_frontier.append(summation)

    Summation.frontier = new_frontier


def update_overapprox():
    results = []
    vars = OrderedSet()
    for summation in Summation.frontier:
        if summation.has_action():
            _, over = summation.update_under()
            act_type = summation.input_type
            total_size = len(act_type.collect_list)
            if total_size == 0:
                if not summation.under_var:
                    summation.under_var = FreshSymbol(template="FVOVER%d")
                    results.append(Implies(summation.under_var, over))
                vars.add(summation.under_var)
            else:
                if summation.under_encoded != total_size:
                    summation.under_var = FreshSymbol(template="FVOVER%d")
                    summation.under_encoded = total_size
                    results.append(Implies(summation.under_var, over))
                vars.add(summation.under_var)

    return results, vars


class Forall(Operator):
    count = 0
    pending_defs = OrderedSet()

    def __init__(self, input_type, func, reference=None):
        super().__init__()
        if not isinstance(func, Function):
            raise illFormedFormulaException("Exists: {} is not a Function".format(func))
        self.input_type = input_type
        self.func = func
        self.op = None
        self.var = Symbol("forall_{}".format(Forall.count))
        self.considered = OrderedSet()
        Forall.count += 1
        if self.input_type != _SUMObject:
            self.print_act = self.input_type(print_only=True)
        self.print_statement = None
        self.reference = reference
        self.proof_hint = None
        self.rid = None
        self.consider_op = False

    def clear(self):
        super(Forall, self).clear()
        self.op = None
        self.print_statement = None
        self.considered = OrderedSet()
        self.func.clear()
        self.proof_hint = None
        self.rid = None
        self.consider_op = False

    def encode(self, assumption=False, include_new_act=False, exception=None, disable=None, proof_writer=None):
        constraint = []
        # base construction
        consider_exception = not exception is None

        op = self.invert()
        op_constraint = op.get_holding_obj(assumption=False, include_new_act=False, exception=None, disable=None,
                                           proof_writer=None)
        if not self.consider_op:
            Forall.pending_defs.add(Implication(self.var, Not(op_constraint.presence)))
            self.consider_op = True

        for action in self.input_type.snap_shot:
            if not action.disabled() and ((not consider_exception) or (not action in exception)):
                eval_func = self.func.evaulate(action)
                if self.reference:
                    presence = Bool_Terminal(action.presence)
                    text_ref[presence] = self.reference
                else:
                    presence = action.presence

                child_res = Implication(presence, eval_func)
                if not disable and proof_writer and action not in self.considered:
                    proof_writer.derive_forall_rule(self, action, child_res)

                base_constraint = encode(child_res,
                                         assumption=assumption, include_new_act=include_new_act, exception=exception,
                                         disable=disable, proof_writer=proof_writer)

                # dual_response = Implication(eval_func, presence)
                # dual_constraint = encode(dual_response,
                #                          assumption=assumption, include_new_act=include_new_act, exception=exception,
                #                          disable=disable, proof_writer=proof_writer)

                if not disable:
                    if action not in self.considered:
                        Forall.pending_defs.add(Implication(self.var, base_constraint))
                        self.considered.add(action)
                    else:
                        # assert (Implies(self.var, base_constraint) in Forall.pending_defs)
                        # print("weird")
                        pass
                else:
                    constraint.append(base_constraint)
        if not disable:
            return self.var
        else:
            return And(constraint)

    def invert(self):
        if self.op is None:
            self.op = Exists(self.input_type, invert(self.func), reference=self.reference)
            self.op.op = self
        assert isinstance(self.op, Exists)
        return self.op

    def to_DNF(self):
        raise NotImplementedError("DNF for quantified formula is not ready")

    def __repr__(self):
        return "Forall_{}".format(self.var)

    def __hash__(self):
        return hash(self.__repr__())

    def to_string(self):
        return "Forall {}: {}. ( (! {}_presence) | {})".format(self.print_act.print_name, self.input_type.action_name,
                                                               self.print_act.print_name,
                                                               self.func.to_string(self.print_act))

    def get_print_statement(self):
        if not self.print_statement:
            self.print_statement = self.func.evaulate(self.print_act)
        return self.print_statement


def create_control_variable(arg):
    s = controll_varaible_eq.get(arg)
    if s is None:
        s = Symbol("control_v_{}".format(len(raw_control_variable)))
        raw_control_variable.add(s)
    return s


def _OR(*args):
    arg_list = _polymorph_args_to_tuple(args)
    if len(arg_list) == 0:
        return FALSE()
    if len(arg_list) == 1:
        return arg_list[0]
    if TRUE() in arg_list:
        return TRUE()
    filtered_args = [arg for arg in arg_list if arg != FALSE()]
    control_sym = [create_control_variable(arg) for arg in filtered_args]
    build_tree(control_sym, filtered_args)
    return Or(control_sym)


def next(Action_class, idenifier_func, func, current_time=Int(0), input_subs=None):
    return (exist(Action_class, lambda act: AND(func(act),
                                                act > current_time,
                                                NOT(exist(Action_class, lambda act1:
                                                AND(act1 > current_time,
                                                    act1 < act,
                                                    idenifier_func(act1, act)
                                                    )
                                                          ))
                                                ), input_subs=input_subs))


def previous(Action_class, idenifier_func, func, current_time=Int(0), input_subs=None):
    return (exist(Action_class, lambda act: AND(func(act),
                                                act < current_time,
                                                NOT(exist(Action_class, lambda act1:
                                                AND(act1 < current_time,
                                                    act1 > act,
                                                    idenifier_func(act1, act)
                                                    )
                                                          ))
                                                ), input_subs=input_subs))


def current(Action_class, idenifier_func, func, current_time=Int(0), input_subs=None):
    return (exist(Action_class, lambda act: AND(func(act),
                                                act <= current_time,
                                                NOT(exist(Action_class, lambda act1:
                                                AND(act1 <= current_time,
                                                    act1 >= act,
                                                    idenifier_func(act1, act),
                                                    NOT(act.build_eq_constraint(act1))
                                                    )
                                                          ))
                                                ), input_subs=input_subs))


def eventually(Action_class, func, current_time=Int(0), input_subs=None):
    circuit = exist(Action_class, lambda act: AND(func(act), act >= current_time), input_subs=input_subs)
    circuit.blocking_clause = lambda act1: Implication(act1.presence,
                                                       forall(Action_class, lambda act: Implication(act1 > act,
                                                                                                    NOT(func(act)))))
    return circuit


def once(Action_class, func, current_time, input_subs=None):
    circuit = exist(Action_class, lambda act: AND(func(act), act <= current_time), input_subs)
    circuit.blocking_clause = lambda act1: Implication(act1.presence,
                                                       forall(Action_class, lambda act: Implication(act1 < act,
                                                                                                    NOT(func(act)))))
    return circuit


def until(EAction, func, Faction, func1, current_time, input_subs=None):
    circut = exist(EAction, lambda eaction: AND(func(eaction),
                                                eaction >= current_time,
                                                NOT(exist(Faction, lambda faction: AND(func1(faction),
                                                                                       faction < eaction,
                                                                                       faction >= current_time)))),
                   input_subs=input_subs)
    circut.blocking_clause = lambda act1: Implication(act1.presence,
                                                      NOT(exist(EAction, lambda eaction: AND(func(eaction),
                                                                                             eaction > act1,
                                                                                             NOT(exist(Faction, lambda
                                                                                                 faction: AND(
                                                                                                 func1(faction),
                                                                                                 faction < eaction,
                                                                                                 faction >= act1)))))))

    return circut


def since(EAction, func, Faction, func1, current_time, input_subs=None):
    circut = exist(EAction, lambda eaction: AND(func(eaction),
                                                eaction <= current_time,
                                                NOT(exist(Faction, lambda faction: AND(func1(faction),
                                                                                       faction > eaction,
                                                                                       faction <= current_time)))),
                   input_subs=input_subs)

    circut.blocking_clause = lambda act1: Implication(act1.presence,
                                                      NOT(exist(EAction, lambda eaction: AND(func(eaction),
                                                                                             eaction < act1,
                                                                                             NOT(exist(Faction, lambda
                                                                                                 faction: AND(
                                                                                                 func1(faction),
                                                                                                 faction > eaction,
                                                                                                 faction <= act1)))))))

    return circut


def ITE(cond, left, right):
    return Ite(cond, left, right)


def IFF(left, right):
    if isinstance(left, Operator) or isinstance(right, Operator):
        return AND(Implication(left, right), Implication(right, left))
    return Iff(left, right)


def EQ(left, right):
    if isinstance(left, Action) and isinstance(right, Action):
        return left.build_eq_constraint(right)
    if isinstance(left, Arth_Operator):
        return left == right
    if isinstance(right, Arth_Operator):
        return right == left
    if isinstance(left, Compare_Binary_Expression):
        return IFF(left, right)
    if isinstance(left, Operator):
        return IFF(left, right)
    return Equals(left, right)


def NEQ(left, right):
    if isinstance(left, Action) and isinstance(right, Action):
        return Not(left.build_eq_constraint(right))
    if isinstance(left, Arth_Operator):
        return left != right
    if isinstance(right, Arth_Operator):
        return right != left
    return NotEquals(left, right)


def _cast_to_pysmt_type(value):
    if type(value) == int:
        return Int(value)
    elif type(value) == type(""):
        return String(value)
    else:
        return value


def _LT(left, right):
    return LT(_cast_to_pysmt_type(left), _cast_to_pysmt_type(right))


def _GT(left, right):
    return GT(_cast_to_pysmt_type(left), _cast_to_pysmt_type(right))


def _LE(left, right):
    return LE(_cast_to_pysmt_type(left), _cast_to_pysmt_type(right))


def _GE(left, right):
    return GE(_cast_to_pysmt_type(left), _cast_to_pysmt_type(right))


def _EQ(left, right):
    return Equals(_cast_to_pysmt_type(left), _cast_to_pysmt_type(right))


def _NEQ(left, right):
    return NEQ(_cast_to_pysmt_type(left), _cast_to_pysmt_type(right))


def _Plus(left, right):
    return Plus(_cast_to_pysmt_type(left), _cast_to_pysmt_type(right))


def _Minus(left, right):
    return Minus(_cast_to_pysmt_type(left), _cast_to_pysmt_type(right))


def _Multi(left, right):
    return Times(_cast_to_pysmt_type(left), _cast_to_pysmt_type(right))


arth_op = [_Minus, _Plus]


def is_arth_op(op):
    return op in arth_op


inverse_operator_mapping = {_LT: _GE, _GE: _LT, _LE: _GT, _GT: _LE, _EQ: _NEQ, _NEQ: _EQ}


def inverse_mapping(op):
    return inverse_operator_mapping.get(op, None)


def next_sum(s, action):
    if not s.child_sum:
        if s.is_count:
            child_sum = Count(s.input_type, lambda action1: AND(s.filter_func.evaulate(action1),
                                                                NEQ(action1, action)
                                                                ), input_subs=s.input_subs)
        else:
            child_sum = Summation(s.input_type, s.value_func, _func(lambda action1: AND(s.filter_func.evaulate(action1),
                                                                                        NEQ(action1, action))),
                                  input_subs=s.input_subs)
        child_sum.parent_info = s
        s.set_child_sum((child_sum, action))
        action.parent_info = s
    else:
        child_sum, action = s.child_sum

    if s.is_count:
        value1 = Int(1)
        if s.pos and s.neg:
            connect_term = (child_sum + value1) == s.value
        elif s.pos and not s.neg:
            connect_term = (child_sum + value1) >= s.value
        else:
            assert False
        return AND(s.filter_func.evaulate(action),
                   connect_term,
                   Equals(s.time, action.time)

                   )
    else:
        value1 = s.value_func.evaulate(action)
        if s.pos and s.neg:
            connect_term = (child_sum + value1) == s.value
        elif s.pos and not s.neg:
            connect_term = (child_sum + value1) >= s.value
        else:
            assert False
        return AND(s.filter_func.evaulate(action), value1 > Int(0),
                   connect_term,
                   Equals(s.time, action.time)

                   )


def next_bcr_sum(s, action):
    if not s.child_sum:
        if s.is_count:
            child_sum = Count(s.input_type, lambda action1: AND(s.filter_func.evaulate(action1),
                                                                NEQ(action1, action)
                                                                ), input_subs=s.input_subs)
        else:
            child_sum = Summation(s.input_type, s.value_func, _func(lambda action1: AND(s.filter_func.evaulate(action1),
                                                                                        NEQ(action1, action))),
                                  input_subs=s.input_subs)
        child_sum.parent_info = s
        s.set_child_sum((child_sum, action))
        action.parent_info = s
    else:
        child_sum, action = s.child_sum

    if s.is_count:
        value1 = Int(1)
        if s.pos and s.neg:
            connect_term = (child_sum + value1) == s.value
        elif s.pos and not s.neg:
            connect_term = (child_sum + value1) >= s.value
        else:
            assert False

        return AND(s.filter_func.evaulate(action),
                   connect_term,
                   Equals(s.time, action.time),
                   forall(s.input_type, lambda other: Implication(s.filter_func.evaulate(other), other <= action))
                   )
    else:
        value1 = s.value_func.evaulate(action)
        if s.pos and s.neg:
            connect_term = (child_sum + value1) == s.value
        elif s.pos and not s.neg:
            connect_term = (child_sum + value1) >= s.value
        else:
            assert False
        return AND(s.filter_func.evaulate(action), value1 > Int(0),
                   connect_term,
                   Equals(s.time, action.time),
                   forall(s.input_type, lambda other: Implication(s.filter_func.evaulate(other),
                                                                  s.value_func.evaulate(other) <= value1))
                   )


def extended_sum_bcr(s):
    if s.pos:
        return AND(s.value > 0,
                   exist(s.input_type, lambda action: AND(next_bcr_sum(s, action)), input_subs=s.input_subs),
                   s.time >= 0)
    else:
        return TRUE()


def extended_sum(s):
    if s.pos:
        return AND(s.value > 0, exist(s.input_type, lambda action: AND(next_sum(s, action)), input_subs=s.input_subs),
                   s.time >= 0)
    else:
        return TRUE()


extended_sum_func = _func(extended_sum)
extended_sum_bcr_func = _func(extended_sum_bcr)

Summation_rule = forall(_SUMObject, extended_sum)
Summation_rule_bcr = forall(_SUMObject, extended_sum_bcr)


def get_background_actions():
    return [_SUMObject]


def get_background_rules(bcr):
    if bcr:
        return [Summation_rule_bcr]
    else:
        return [Summation_rule]


def add_background_theories(Actions, state_action, Rules, bcr=False):
    state_action.extend(get_background_actions())
    Actions.extend(get_background_actions())
    return Rules + get_background_rules(bcr)
