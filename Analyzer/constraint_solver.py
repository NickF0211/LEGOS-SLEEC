from logic_operator import *
from domain import *
from read_trace import translation_value_map
from pysmt.shortcuts import Solver
from abstraction import realize_abstractions

walked = 0
walked_set = []
models = 0

attack_trace = []
attack_model = []

traverse_solver = Solver("z3",  unsat_cores_mode= "named")


def attack(solver):
    assumption_walk(solver, [], None, list(controll_variable))



def print_model_trace(model, translation_map, is_readable = False, is_abstract = False):
    if len(translation_map.keys()) == 0:
        return print_trace(model)
    else:
        all_res = []
        all_objects = []
        for action in ACTION:
            all_objects += action.collect_list
        filtered_objects = filter(lambda obj: model.get_py_value(obj.presence), all_objects)
        sorted_objects = sorted(filtered_objects, key=lambda obj: model.get_py_value(obj.time))
        cur_time = 0
        for obj in sorted_objects:
            action_time = model.get_py_value(obj.time)
            res = ""
            ticks = action_time // 30
            if ticks > cur_time:
                all_res.append( "Time_{}".format(ticks * 30))
                cur_time = ticks
            extended = obj in type(obj).syn_collect_list
            if extended:
                res = "+"
            res = res + obj.get_model_record(model, translation_map, is_readable = is_readable, is_abstract=is_abstract)
            all_res.append(res)
        return "\n".join(all_res)



def cardinality_constraint(lower_bound, upper_bound):
    all_objects = []
    for action in ACTION:
        all_objects += action.syn_collect_list

    card_sum = Plus([obj.card for obj in all_objects])
    card_sum_constraint = And(LE(card_sum, Int(upper_bound)), GE(card_sum, Int(lower_bound)))
    card_presence_constraint = And ([obj.cardinality_constraint for obj in all_objects])
    return And(card_presence_constraint, card_sum_constraint)


def check_unreachable(assumption):
    solved = traverse_solver.solve(assumptions= assumption + walked_set)
    if (not solved):
        #core = traverse_solver.get_unsat_core()
        #analyze_unsat_clue(traverse_solver)
        pass
    return solved


'''
expect s_core to be an CNF
returns a clause representing the learning result
'''
def analyze_unsat_clue(solver):
    core = solver.get_unsat_core()
    # time to add learning
    lesson = []
    for clue in core:
        s_core = simplify(clue)
        #print(s_core)
        atoms = s_core.args()
        for atom in atoms:
            variables = get_free_variables(atom)
            if atom.is_iff():
                continue
            valid = True
            for var in variables:
                if not var.symbol_name().startswith("control_v_"):
                    valid = False
                    break
            if not valid:
                continue
            lesson.append(atom)
    res = And(lesson)
    walked_set.append(res)
    return res

def determine_polarity(v, model):
    if model.get_py_value(v):
        return v
    else:
        return Not(v)

def assumption_formula_collect(model, cur_node, rst):
    if len(rst)==0 and cur_node is None:
        return []
    else:
        if (cur_node) is None:
            node = rst[0]
            return assumption_formula_collect(model,  node, rst[1:])
        else:
            assumptions = []
            for control_v, tree in zip(cur_node.control_vs, cur_node.trees):
                dive_in = model.get_py_value(control_v)
                if dive_in:
                    assumptions.append(controll_varaible_eq_r.get(control_v))
                    assumptions += assumption_formula_collect(model,None, list(tree) + rst )
                else:
                    # total_negation = [control_v_other for control_v_other in  cur_node.control_vs if control_v_other!= control_v ]
                    assumptions.append(Not(controll_varaible_eq_r.get(control_v)))
        return assumptions


def model_minimization(model, solver, assumptions, upper_bound, lower_bound = 0):
    #print( (lower_bound, upper_bound))
    if upper_bound - lower_bound <= 1:
        return model

    new_upper_bound = (lower_bound + upper_bound) // 2
    new_card_constraint = cardinality_constraint(lower_bound, new_upper_bound)
    solved = solver.solve(assumptions=assumptions + walked_set + [new_card_constraint])
    if (solved):
        model = solver.get_model()
        upper_bound = get_trace_size(model)
        return model_minimization(model, solver, assumptions, upper_bound, lower_bound)
    else:
        return model_minimization(model, solver, assumptions, upper_bound, new_upper_bound)

def analyze_model(solver, cur_node, rst, assumptions):
    global models
    #print("find model")
    models += 1
    remaining_conv = get_all_con_v(cur_node, rst, set())
    model = solver.get_model()
    pos_conv = [cov for cov in remaining_conv if model.get_py_value(cov)]
    constraint = And(get_symmetry(pos_conv)+ symmetry_sub(assumptions))
    #constraint = And(get_symmetry(pos_conv + assumptions))
    #print(is_valid(Implies(constraint_1, constraint)))
    upper_bound = get_trace_size(model)
    lower_bound = 0
    model = model_minimization(model, solver, assumptions, upper_bound, lower_bound)

    #print("A early model assumption_constraint {}".format(And(pos_conv+assumptions)))
    attack_model.append(model)
    attack = ""
    attack += print_model_trace(model, translation_value_map, is_readable = True)
    attack += "\n____________________________\n"
    attack+= print_model_trace(model, translation_value_map, is_readable=True, is_abstract=True)
    attack_trace.append(attack)
    #attack_trace.append(print_model_trace(model, translation_value_map, is_readable = True))
    #attack_trace.append(print_model_trace(model, translation_value_map, is_readable=True, is_abstract=True))
    active_assumptions = assumption_formula_collect(model, None, list(controll_variable))
    #clean = simplify(substitute(And(active_assumptions), controll_varaible_eq_r))
    #print("symbolic obligation:")
    #print(serialize(clean))
    walked_set.append(Not(constraint))

def get_all_con_v(cur_node, rst, coll):
    if len(rst) == 0 and cur_node is None:
        return coll
    else:
        if (cur_node) is None:
            node = rst[0]
            return get_all_con_v(node, rst[1:], coll)
        else:
            for control_v, tree in zip(cur_node.control_vs, cur_node.trees):
                if control_v not in coll:
                    coll.add(control_v)
                    get_all_con_v( None, list(tree)+rst , coll)
            return coll

def assumption_walk(solver, assumptions, cur_node, rst):
    global walked
    global models
    if len(rst)==0 and cur_node is None:
        if not check_unreachable(assumptions):
            #print("pruned {}".format(assumptions))
            return
        walked+=1
        assumption_constraint = And(assumptions)
        solved = solver.solve(assumptions = assumptions + walked_set)
        if (solved):
            solver.push()
            solver.add_assertion(realize_abstractions())
            solved = solver.solve(assumptions=assumptions + walked_set)
            if solved:
                analyze_model(solver, cur_node, rst, assumptions)
                solver.pop()
            else:
                solver.pop()
                print("abstraction too restrictive")
        else:
            #print("UNSAT")
            analyze_unsat_clue(solver)

    else:
        if (cur_node) is None:
            node = rst[0]
            return assumption_walk(solver, assumptions, node, rst[1:])
        else:
            #something wrong with this
            solved = solver.solve(assumptions=assumptions + walked_set)
            if not solved:
                analyze_unsat_clue(solver)
                #print("early unsat {}".format(assumptions))
                return
            else:
                #analyze_model(solver, cur_node, rst, assumptions)
                pass

            negated = []
            for control_v, tree in zip(cur_node.control_vs, cur_node.trees):
                #total_negation = [control_v_other for control_v_other in  cur_node.control_vs if control_v_other!= control_v ]
                assumption_walk(solver, assumptions+[And(control_v,  Not(Or(negated)))], None, list(tree)+rst)
                negated.append(control_v)

def get_trace_size(model):
    all_objects = []
    for action in ACTION:
        all_objects += action.syn_collect_list

    filtered_objects = filter(lambda obj: model.get_py_value(obj.presence), all_objects)
    return len(list(filtered_objects))

