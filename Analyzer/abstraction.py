from type_constructor import *
#this is the place we can use define the abstraction

abstraction_function = dict()
abstraction_map = dict()


def ordering_constraints(vars, ordered = True):
    constraints = []
    for var1 in vars:
        for var2 in vars:
            if var1 != var2:
                if ordered:
                    constraints.append(Iff(GT(var1, var2), GT(get_varaible(var1), get_varaible(var2))))
                    constraints.append(Iff(LT(var1, var2), LT(get_varaible(var1), get_varaible(var2))))
                constraints.append(Iff(Equals(var1, var2), Equals(get_varaible(var1), get_varaible(var2))))
    return constraints


def create_abstraction(type_name, lower_bound = 0, upper_bound = 4, ordered= True, translation_map=None):
    func = lambda : _create_abstraction(type_name, lower_bound = lower_bound, upper_bound = upper_bound, ordered= ordered, translation_map=translation_map)
    abstraction_function[type_name] = func


def _create_abstraction(type_name, lower_bound = 0, upper_bound = 4, ordered= True, translation_map=None):
    constraint =  abstraction_map.get(type_name, None)
    if constraint is not None:
        return constraint
    constraints = []
    vars = get_variables_by_type(type_name)
    for var in vars:
        constraints.append(LE(get_varaible(var), Int(upper_bound)))
        constraints.append(GE(get_varaible(var), Int(lower_bound)))

    constraints += ordering_constraints(vars, ordered)

    if translation_map is not None:
        for key, value in translation_map.items():
            for var in vars:
                constraints.append(Implies(Equals(var, Int(key)), Equals(get_varaible(var), Int(value))))

    constraint = And(constraints)
    abstraction_map[type_name] = constraint
    return constraint


def realize_abstractions():
    constraints = []
    for _, func in abstraction_function.items():
        constraints.append(func())
    return And(constraints)








