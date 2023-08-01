from pysmt.shortcuts import *

def forall(Action_cls, func):
    return And([Implies(action.presence, func(action)) for action in Action_cls.collect_list])

def exists(Action_cls, func):
    return Or([And(action.presence, func(action)) for action in Action_cls.collect_list])



def merge_two_dicts(x, y):
    """Given two dictionaries, merge them into a new dict as a shallow copy."""
    z = x.copy()
    z.update(y)
    return z


def consumable_resource_type(providers, users, consumers):
    if providers is None or len(providers) == 0:
        print("cannot have a resource without provider")
    if consumers is None or len(consumers) == 0:
        print("please use resource type instead")
    else:
        _, p_attrs = providers[0]
        length = len(p_attrs)
        index = 0
        condition = []
        negation = []
        u_attr= []
        p_attr = []
        c_attr = []
        while (index < length):
            u_symbol = Symbol("u_a{}".format(index), INT)
            u_attr.append(u_symbol)
            p_symbol = Symbol("p_a{}".format(index), INT)
            p_attr.append(p_symbol)
            c_symbol = Symbol("c_a{}".format(index), INT)
            c_attr.append(c_symbol)
            condition.append(Equals(u_symbol, p_symbol))
            negation.append(Equals(c_symbol, p_symbol))
            index += 1
        u_t = Symbol("u_t", INT)
        p_t = Symbol("p_t", INT)
        c_t = Symbol("c_t", INT)
        condition.append(GT(u_t, p_t ))
        negation_template = Implies(And(negation), Not(And(GT(c_t, p_t), LT(c_t, u_t))))
        template = And(condition)

        def generate_constraint():
            constraint = []

            def replacement(use_act, provide_act):
                replace_dict1 = dict((u_a_t, getattr(use_act, u_a)) for (u_a_t, u_a) in zip(u_attr, u_attrs))
                replace_dict2 = dict((p_a_t, getattr(provide_act, p_a)) for (p_a_t, p_a) in zip(p_attr, p_attrs))
                replace_dict3 = dict({u_t: getattr(use_act, "time"), p_t: getattr(provide_act, "time")})
                r = substitute(template, merge_two_dicts(merge_two_dicts(replace_dict1, replace_dict2), replace_dict3))
                return r

            def replacement_neg(use_act, provide_act, consumer_act):
                replace_dict1 = dict((u_a_t, getattr(use_act, u_a)) for (u_a_t, u_a) in zip(u_attr, u_attrs))
                replace_dict2 = dict((p_a_t, getattr(provide_act, p_a)) for (p_a_t, p_a) in zip(p_attr, p_attrs))
                replace_dict3 = dict((c_a_t, getattr(consumer_act, c_a)) for (c_a_t, c_a) in zip(c_attr, c_attrs))
                replace_dict4 = dict({u_t: getattr(use_act, "time"), p_t: getattr(provide_act, "time"), c_t: getattr(consumer_act, "time")})
                r = substitute(negation_template,
                               merge_two_dicts(merge_two_dicts(merge_two_dicts(replace_dict1, replace_dict2), replace_dict3), replace_dict4))
                return r


            for use, u_attrs in users:
                for provier, p_attrs in providers:
                    for consumer, c_attrs in consumers:
                        constraint.append(forall(use, lambda use_act:
                            exists(provier, lambda provide_act: And(replacement(use_act, provide_act),
                                                                    exists(consumer, lambda  consumer_act :
                                                                    replacement_neg(use_act, provide_act, consumer_act)))
                                   )))

            return And(constraint)
        return generate_constraint

def resource_type(providers, users):
    if providers is None or len(providers) == 0:
        print("cannot have a resource without provider")
    else:
        _, p_attrs = providers[0]
        length = len(p_attrs)
        index = 0
        condition = []
        u_attr= []
        p_attr = []
        while (index < length):
            u_symbol = Symbol("u_a{}".format(index), INT)
            u_attr.append(u_symbol)
            p_symbol = Symbol("p_a{}".format(index), INT)
            p_attr.append(p_symbol)
            condition.append(Equals(u_symbol, p_symbol))
            index += 1
        u_t = Symbol("u_t", INT)
        p_t = Symbol("p_t", INT)
        condition.append(GT(u_t, p_t ))
        template = And(condition)

        def generate_constraint():
            constraint = []

            def replacement(use_act, provide_act):
                replace_dict1 = dict((u_a_t, getattr(use_act, u_a)) for (u_a_t, u_a) in zip(u_attr, u_attrs))
                replace_dict2 = dict((p_a_t, getattr(provide_act, p_a)) for (p_a_t, p_a) in zip(p_attr, p_attrs))
                replace_dict3 = dict({u_t: getattr(use_act, "time"), p_t: getattr(provide_act, "time")})
                r = substitute(template, merge_two_dicts(merge_two_dicts(replace_dict1, replace_dict2), replace_dict3))
                return r

            for use, u_attrs in users:
                for provier, p_attrs in providers:
                    constraint.append(forall(use, lambda use_act:
                        exists(provier, lambda provide_act: replacement(use_act, provide_act))))

            return And(constraint)
        return generate_constraint