import z3
# compute uninterpreted constants in a formula
def free_arith_vars(fml):
    '''Returns the set of all integer uninterpreted constants in a formula'''
    seen = set([])
    vars = set([])

    int_sort = z3.IntSort()
    def fv(seen, vars, f):
        if f in seen:
            return
        seen |= { f }
        if f.sort().eq(int_sort) and f.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            vars |= { f }
        for ch in f.children():
            fv(seen, vars, ch)
    fv(seen, vars, fml)
    return vars


# wrapper to solve CHC constraints and extract result
def solve_horn(chc, pp=False, q3=False, max_unfold=10, verbosity=0):
    z3.set_param(verbose=verbosity)

    s = z3.SolverFor('HORN')
    s.set('engine', 'spacer')
    s.set('spacer.order_children', 2)
    if not pp:
        s.set('xform.inline_eager', False)
        s.set('xform.inline_linear', False)
        s.set('xform.slice', False)

    if max_unfold > 0:
        s.set('spacer.max_level', max_unfold)

    if q3:
        # allow quantified variables in pobs
        s.set('spacer.ground_pobs', False)
        # enable quantified generalization
        s.set('spacer.q3.use_qgen', True)

    # add constraints to solver
    s.add(chc)
    if verbosity > 0:
        print(s.sexpr())
    # run solver
    res = s.check()
    # extract model or proof
    answer = None
    if res == z3.sat:
        answer = s.model()
    elif res == z3.unsat:
        answer = s.proof()
    return res, answer

def interpolate(A, B, verbosity=0):
    '''Computes a Craig interpolant between A and B'''
    As = free_arith_vars(A)
    Bs = free_arith_vars(B)

    shared = [s for s in As & Bs ]

    Itp = z3.Function('Itp', [s.sort() for s in shared] + [z3.BoolSort()])
    left = z3.ForAll([a for a in As], z3.Implies(A, Itp(shared)))
    right = z3.ForAll([b for b in Bs], z3.Implies(Itp(shared), z3.Not(B)))

    res, answer = solve_horn([left, right])

    if res == z3.sat:
        return answer.eval(Itp(shared))
    return None

c1_time, c1_id = z3.Ints('c1_time c1_id')
c2_time, c2_id = z3.Ints('c2_time c2_id')
c3_time, c3_id = z3.Ints('c3_time c3_id')
itp = interpolate(z3.And(c1_time < c1_id,
                         z3.Implies(c1_id > 0, z3.And(c2_time < c1_time, c2_id == c1_id -1)),
                         c1_id >= 0,
                         c1_time >= 0,
                         c2_time >= 0,
                         z3.Implies(c2_id > 0, z3.And(c3_time < c2_time, c3_id == c2_id -1)),
                         c3_time >= 0,
                         c3_id > 0
                         ),
                  z3.And(c3_id ==  0))
print(itp)