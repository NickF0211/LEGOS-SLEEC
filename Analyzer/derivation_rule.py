from pysmt.fnode import FNode
from pysmt.shortcuts import get_free_variables, get_type,serialize

from logic_operator import to_string, C_NOT, invert, C_AND, Operator, C_OR, text_ref, Bool_Terminal


def reset():
    Rule.ids = 0


def find_text_ref(expr):
    res = text_ref.get(expr, None)
    if res is None and expr.op:
        res = text_ref.get(expr.op, None)

    if res:
        return res._tx_position, res._tx_position_end
    else:
        return None


class Proof_Writer():
    def __init__(self, outfile=None):
        if outfile is None:
            self.out = None
        else:
            self.out = open(outfile, 'w')
        self.rule_id = 0
        self.input_ids = {}
        self.definition_lit_id = 0
        self.fact_ids = 0
        self.considered_facts = {}
        self.atoms = set()
        self.ro_origin = {}

    def post_process(self):
        # add   the type info for every tokens appeared in the formula
        records = []
        for atom in self.atoms:
            a_type = get_type(atom)
            records.append((str(atom), str(a_type)))
        for i in range(self.definition_lit_id):
            records.append(("c{}".format(i), "Bool"))
        self.print_to_proof("Vars || {}".format(' '.join(["{}:{}".format(a, b) for a, b in records])))

    def add_fact(self, expr, derive=True):
        fact_id = self.fact_ids
        self.fact_ids += 1
        prefix = "DeriveFact" if derive else "AddFact"
        self.print_to_proof("{} || F{} || {}".format(prefix, fact_id, expr))
        return fact_id

    def declare_atoms(self, expr):
        atoms = get_free_variables(expr)
        self.atoms.update(atoms)

    def add_definition(self, expr, derived=True, terminal_obj=None):
        if expr in self.considered_facts:
            def_id, fid = self.considered_facts[expr]
            return def_id, fid, True
        def_id = self.definition_lit_id
        self.definition_lit_id += 1
        if isinstance(expr, Operator):
            new_rule = Rule(expr, self.rule_id)
            self.rule_id += 1
            self.print_to_proof(
                "Def || {} || c{} <-> {}".format(self.add_prefix(new_rule.id), def_id, to_string(new_rule.rule)))
            hint = new_rule.id
        else:
            self.declare_atoms(expr)
            if terminal_obj is not None:
                res = find_text_ref(terminal_obj)
            else:
                res = None

            if res:
                start, end = res
                fid = self.add_fact("c{} <-> {} || {} {}".format(def_id, to_string(expr), start, end), derived)
            else:
                fid = self.add_fact("c{} <-> {}".format(def_id, to_string(expr)), derived)
            self.considered_facts[expr] = def_id, fid
            hint = fid
        return def_id, hint, not isinstance(expr, Operator)

    def add_input_rule(self, in_rule):
        rule = Rule(in_rule, self.rule_id)
        self.input_ids[rule.id] = len(self.input_ids)
        self.rule_id += 1
        self.print_to_proof("Input || {} || {}".format(self.add_prefix(rule.id), to_string(rule.rule)))
        rule_lit, hint, is_fact = self.get_def(in_rule)

        self.add_fact("c{} || {} {}".format(rule_lit, self.add_prefix(hint, is_fact), self.add_prefix(rule.id)))

    def derive_exists_rule(self, parent_rule, rel_ob, new_rule):
        parent_def_id, p_r_id, p_is_fact = self.get_def(parent_rule)
        EI_rule_id = self.rule_id
        self.ro_origin[rel_ob] = EI_rule_id
        self.rule_id += 1
        self.print_to_proof(
            "DeriveLemma || EI {}  [{}:{}<-{}] || {} || c{} -> {}".format(self.add_prefix(parent_rule.rid),
                                                                          parent_rule.print_act.print_name,
                                                                          type(rel_ob).action_name,
                                                                          rel_ob.print_name,
                                                                          self.add_prefix(EI_rule_id),
                                                                          parent_def_id, to_string(new_rule)))

        child_def, child_r, child_is_fact = self.get_def(new_rule)
        self.add_fact("c{} -> c{} || {} {}".format(parent_def_id, child_def,
                                                   self.add_prefix(child_r, child_is_fact),
                                                   self.add_prefix(EI_rule_id)))

    def derive_forall_rule(self, parent_rule, rel_ob, new_rule):
        rel_ext_id = self.ro_origin[rel_ob]
        parent_def_id, p_r_id, p_is_fact = self.get_def(parent_rule)
        UI_rule_id = self.rule_id
        self.rule_id += 1
        self.print_to_proof(
            "DeriveLemma || UI {} [{}:{}<-{}]  || {} || c{} -> {} || {}".format(self.add_prefix(parent_rule.rid),
                                                                                parent_rule.print_act.print_name,
                                                                                type(rel_ob).action_name,
                                                                                rel_ob.print_name,
                                                                                self.add_prefix(UI_rule_id),
                                                                                parent_def_id, to_string(new_rule),
                                                                                self.add_prefix(rel_ext_id)))

        child_def, child_r, child_is_fact = self.get_def(new_rule)
        self.add_fact("c{} -> c{} || {} {}".format(parent_def_id, child_def,
                                                   self.add_prefix(child_r, child_is_fact),
                                                   self.add_prefix(UI_rule_id)))

    def add_prefix(self, id, is_fact=False):
        if is_fact:
            return "F{}".format(id)
        else:
            if id in self.input_ids:
                return "R{}".format(self.input_ids[id])
            else:
                return "L{}".format(id)

    def print_to_proof(self, content):
        if self.out is None:
            print(content)
        else:
            self.out.write(content + '\n')

    def add_negation(self, rule: C_NOT):
        p_id, p_rule_id, p_is_fact = self.get_def(rule)
        negated_rule = invert(rule.arg)
        NNF_id = self.rule_id
        self.print_to_proof(
            "DeriveLemma || NNF {} || {} || c{} <-> {} ".format(self.add_prefix(rule.rid),
                                                                self.add_prefix(NNF_id), p_id,
                                                                to_string(negated_rule)))
        self.rule_id += 1
        child_def_id, r_id, cis_fact = self.get_def(negated_rule)
        self.add_fact("c{} -> c{} || {} {}".format(p_id, child_def_id,
                                                   self.add_prefix(r_id,
                                                                   cis_fact),
                                                   self.add_prefix(NNF_id)))

    def get_def(self, rule, derived=False):
        if isinstance(rule, FNode):
            return self.add_definition(rule, derived=derived)
        elif isinstance(rule, Bool_Terminal):
            return self.add_definition(rule.value, derived=derived, terminal_obj=rule)

        if rule.proof_lit is None:
            parent_lit, parent_def_rule, is_fact = self.add_definition(rule, derived=derived)
            rule.proof_lit = parent_lit
            rule.proof_hint = parent_def_rule, is_fact
        else:
            parent_lit = rule.proof_lit
            parent_def_rule, is_fact = rule.proof_hint
        return parent_lit, parent_def_rule, is_fact

    def add_and(self, rule: C_AND):
        defs = []
        child_rules = []
        if rule.proof_lit is None:
            parent_lit, parent_def_rule, p_is_fact = self.add_definition(rule)
            rule.proof_lit = parent_lit
            rule.proof_hint = parent_def_rule, p_is_fact
        else:
            parent_lit = rule.proof_lit
            parent_def_rule, p_is_fact = rule.proof_hint

        for child in rule.arg_list:
            child_proof_lit, child_rule, is_fact = self.get_def(child, derived=False)
            defs.append("c{}".format(child_proof_lit))
            child_rules.append((child_rule, is_fact))


        for i in range(len(defs)):
            child_id, is_fact = child_rules[i]
            self.add_fact("c{} -> ({}) || {} {}".format(parent_lit, defs[i], self.add_prefix(child_id, is_fact), self.add_prefix(parent_def_rule, p_is_fact)))

        # self.add_fact("c{} -> ({}) || {}".format(parent_lit, ' & '.join(defs),
        #                                          ' '.join([
        #                                                       self.add_prefix(child_id, is_fact) for (child_id, is_fact)
        #                                                       in
        #                                                       child_rules] + [
        #                                                       self.add_prefix(parent_def_rule, p_is_fact)])))

    def add_or(self, rule: C_OR):
        defs = []
        child_rules = []
        if rule.proof_lit is None:
            parent_lit, parent_def_rule, p_is_fact = self.add_definition(rule)
            rule.proof_lit = parent_lit
            rule.proof_hint = parent_def_rule, p_is_fact
        else:
            parent_lit = rule.proof_lit
            parent_def_rule, p_is_fact = rule.proof_hint

        for child in rule.arg_list:
            child_proof_lit, child_rule, is_fact = self.get_def(child, derived=False)
            defs.append("c{}".format(child_proof_lit))
            child_rules.append((child_rule, is_fact))

        self.add_fact("c{} -> ({}) || {}".format(parent_lit, ' | '.join(defs),
                                                 ' '.join([
                                                              self.add_prefix(child_id, is_fact) for (child_id, is_fact)
                                                              in
                                                              child_rules] + [
                                                              self.add_prefix(parent_def_rule, p_is_fact)])))

    def derive_unsat(self, considered_constraints = None):
        self.print_to_proof("UNSAT || F0 - F{}".format(self.fact_ids - 1))
        self.post_process()
        if considered_constraints is not None:
            self.write_type_constraints(considered_constraints)

    def write_type_constraints(self, considered_constraints):
        self.print_to_proof("AXIOM || {}".format(' & '.join([serialize(f) for f in considered_constraints])))

    def close(self):
        if self.out:
            self.out.close()


class Rule():
    ids = {}

    def __init__(self, rule, id):
        self.rule = rule
        if isinstance(rule, Operator):
            rule.rid = id
        else:
            Rule.ids[rule] = id

        self.id = id

    def get_id(self):
        return self.id

    def get_rule(self):
        return self.rule


def get_id(expr):
    if isinstance(expr, Operator):
        return expr.rid
    else:
        assert expr in Rule.ids
        return Rule.ids[expr]
