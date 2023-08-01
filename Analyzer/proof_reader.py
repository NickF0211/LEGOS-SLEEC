from pysmt.shortcuts import *
from pysmt.typing import BOOL, INT
import re

UNSAT = -1
AXIOM = []
from pysmt.parsing import parse


def get_assumption_core(solver):
    assumptions = solver.z3.unsat_core()
    pysmt_assumptions = [solver.converter.back(t) for t in assumptions]
    return pysmt_assumptions


def extend_and_insert(target, id, content):
    if len(target) == id:
        target.append(content)
    elif len(target) > id:
        assert target[id] is not None
        target[id] = content
    else:
        target.extend([None for _ in range(1 + id - len(target))])
        target[id] = content


def extract_def(content: str):
    tokens = content.split('<->', 1)
    if len(tokens) == 2:
        return tokens[0].strip(), tokens[1].strip()

    return False, False


def cmp(a: str, b: str):
    return a.replace(' ', '') == b.replace(' ', '')


def is_match(template: str, current: str):
    if cmp(template, current):
        return True
    else:
        # in case template is <-> and current is ->
        res = False
        t1 = template.split('<->', 1)
        t2 = current.split('->', 1)
        if len(t1) == len(t2) == 2:
            res = t1[0].strip() == t2[0].strip() and t1[1].strip() == t2[1].strip()

        if res:
            return res
        else:
            if t1[0] == t2[0] and '<->' in template and '->' in current and len(t1) == len(t2) == 2:
                t2_body = t2[1].strip().strip('(').strip(')').strip()
                t1_bodies = t1[1].strip().strip('(').strip(')').split('&')
                for t1_body in t1_bodies:
                    if t2_body == t1_body.strip():
                        return True
    return False


class Derivation:

    def check(self):
        pass

    def get_dep(self):
        pass

    def get_id(self):
        pass

    def project_usage(self):
        pass

    def receive_usage_update(self, content):
        pass


class Definition():
    Defs = {}

    def __init__(self, var_name, content, is_fact=False):
        self.var = var_name
        self.content = content
        self.is_fact = is_fact
        Definition.Defs[var_name] = self


class Fact(Derivation):
    Facts = []

    def __init__(self, id, content, deps, text_ref=None):
        self.id = id
        self.content = content
        self.formula = None
        self.deps = deps
        self.assumption_lit = Symbol("F{}".format(id))
        self.definition_relation = None
        extend_and_insert(Fact.Facts, self.id, self)
        self.usage = []
        self.text_ref = text_ref

    def get_id(self):
        return "F{}".format(self.id)

    def parse_content(self):
        self.formula = parse(self.content)

    def get_assumption_clause(self):
        if self.formula is not None:
            return Implies(self.assumption_lit, self.formula)
        else:
            assert False

    def check(self):
        if self.deps:
            defs = self.deps[:-1]
            base = self.deps[-1]
            base_content = get_content_by_id(base).content
            for def_id in defs:
                d = get_content_by_id(def_id)
                content = d.content
                cid, cexpr = extract_def(content)
                if not cid:
                    return False
                base_content = base_content.replace(cexpr, cid, 1)
            return is_match(base_content, self.content)
        else:
            # TODO: need to check if the def literal has appeared else where
            return True

    def get_dep(self):
        if self.deps:
            return self.deps
        else:
            return []

    def project_usage(self):
        # now the Fact as the usage
        if self.definition_relation:
            if self.deps:
                for id in self.deps:
                    d = get_content_by_id(id)
                    d.receive_usage_update(self.definition_relation)

    def __str__(self):
        if self.deps:
            header = "DeriveFact"
            return "{} || {} || {} || {}".format(header, self.get_id(), self.content, ' '.join(self.deps))
        else:
            header = "AddFact"
            if self.text_ref:
                return "{} || {} || {} || {}".format(header, self.get_id(), self.content, self.text_ref)
            else:
                return "{} || {} || {}".format(header, self.get_id(), self.content)


class InputRule(Derivation):
    Inputs = []

    def __init__(self, id, content):
        self.id = id
        self.content = content
        extend_and_insert(InputRule.Inputs, self.id, self)
        self.usage = []

    def get_id(self):
        return "R{}".format(self.id)

    def check(self):
        return True

    def get_dep(self):
        return []

    def __str__(self):
        return "Input || {} || {}".format(self.get_id(), self.content)


class Lemma(Derivation):
    Lemmas = []

    def __init__(self, id, content, hint, deps):
        self.id = id
        self.content = content
        self.hint = hint
        self.deps = deps
        self.definition_relation = None
        extend_and_insert(Lemma.Lemmas, self.id, self)
        self.usage = []

    def get_id(self):
        return "L{}".format(self.id)

    def check(self):
        if self.hint:
            return self.hint.check(self.content)
        else:
            # TODO: need to check the def var has not appeared before
            return True

    def get_dep(self):
        if self.deps:
            return self.deps
        else:
            return []

    def __str__(self):
        if self.hint:
            if self.deps:
                return "DeriveLemma || {} || {} || {} || {}".format(str(self.hint), self.get_id(), self.content,
                                                                    ' '.join(self.deps))
            else:
                return "DeriveLemma || {} || {} || {}".format(str(self.hint), self.get_id(), self.content)
        else:
            return "Def || {} || {}".format(self.get_id(), self.content)


class Hint:
    def check(self, content):
        pass

    def get_dep(self):
        return []


class EI_Hint(Hint):
    def __init__(self, base, source, target, cls):
        self.base = base
        self.source = source
        self.target = target
        self.cls = cls

    def check(self, content: str):
        # return is_match(get_content_by_id(self.base).content, content.replace(self.source, self.target))
        return True

    def get_dep(self):
        return [self.base]

    def __str__(self):
        return "EI {}  [{}:{}<-{}]".format(self.base, self.source, self.cls, self.target)


class UI_Hint(Hint):
    def __init__(self, base, source, target, cls):
        self.base = base
        self.source = source
        self.target = target
        self.cls = cls

    def check(self, content: str):
        # template = get_content_by_id(self.base)
        # template_defs = template.definition_relation
        # tcid, tcontent = template_defs.var, template_defs.content
        # template = r"\s*Forall {}: {}\.(.*)".format(self.source, self.cls)
        # res = re.match(template, tcontent)
        # if res:
        #     matched = res.group(1).replace(self.source, self.target)
        #     return is_match(content, "{} -> {}".format(tcid, matched))
        # cur_content = content.replace(self.target, self.source)
        # return is_match(get_content_by_id(self.base).content, content.replace(self.source, self.target))
        return True

    def get_dep(self):
        return [self.base]

    def __str__(self):
        return "UI {}  [{}:{}<-{}]".format(self.base, self.source, self.cls, self.target)


class NNF_Hint(Hint):
    def __init__(self, base):
        self.base = base

    def check(self, content: str):
        # for now, assume NNF conversion is always sound
        return True

    def get_dep(self):
        return [self.base]

    def __str__(self):
        return "NNF {} ".format(self.base)


def get_content_by_id(id: str):
    if id.startswith('F'):
        return Fact.Facts[int(id[1:])]
    elif id.startswith("L"):
        return Lemma.Lemmas[int(id[1:])]
    elif id.startswith('R'):
        return InputRule.Inputs[int(id[1:])]
    else:
        print("Unknown reference {}".format(id))
        assert False


def parse_hint(content: str):
    tokens = content.split()
    rule_name = tokens[0].strip()
    if rule_name == "NNF":
        assert len(tokens) >= 2
        return NNF_Hint(tokens[1])
    elif rule_name == "EI":
        assert len(tokens) >= 3
        subs = tokens[2]
        res = subs.lstrip('[').rstrip(']').split('<-')
        left, cls = res[0].split(":")
        right = res[1]
        return EI_Hint(tokens[1], left, right, cls)
    elif rule_name == "UI":
        assert len(tokens) >= 3
        subs = tokens[2]
        res = subs.lstrip('[').rstrip(']').split('<-')
        left, cls = res[0].split(":")
        right = res[1]
        return UI_Hint(tokens[1], left, right, cls)
    else:
        print("unknown hint {}".format(content))
        return None


def parse_fact_formulas():
    for fact in Fact.Facts:
        if fact is not None:
            fact.parse_content()


def parse_input_rule(content):
    tokens = content.split("||")
    assert len(tokens) == 3
    id = int(tokens[1].strip()[1:])
    content = tokens[2].strip()
    InputRule(id, content)
    return tokens[1].strip()


def parse_definition(content):
    tokens = content.split("||")
    id = int(tokens[1].strip()[1:])
    content = tokens[2].strip()
    l = Lemma(id, content, None, None)
    # now work on the content
    cid, value = content.split('<->', 1)
    l.definition_relation = Definition(cid, value, is_fact=False)
    return tokens[1].strip()


def parse_axiom(content):
    tokens = content.split('||')
    assert len(tokens) >= 2
    axiom = parse(tokens[1])
    AXIOM.append(axiom)


def parse_add_fact(content):
    tokens = content.split('||')
    assert len(tokens) >= 3
    id = int(tokens[1].strip()[1:])
    content = tokens[2].strip()
    if len(tokens) >= 4:
        start, end = tokens[3].strip().split()
        t_ref = (int(start), int(end))
    else:
        t_ref = None

    f = Fact(id, content, None, text_ref=t_ref)
    cid, value = content.split('<->', 1)
    f.definition_relation = Definition(cid, value, is_fact=False)
    return tokens[1].strip()


def parse_derive_fact(content):
    tokens = content.split('||')
    assert len(tokens) >= 3
    id = int(tokens[1].strip()[1:])
    content = tokens[2].strip()
    if len(tokens) >= 4:
        hint = tokens[3].strip().split()
    else:
        hint = []
    Fact(id, content, hint)
    return tokens[1].strip()


def parse_lemma(content):
    tokens = content.split("||")
    hint = parse_hint(tokens[1].strip())
    id = int(tokens[2].strip()[1:])
    content = tokens[3].strip()
    deps = hint.get_dep()
    if len(tokens) >= 5:
        deps += tokens[4].split()

    Lemma(id, content, hint, deps)
    return tokens[2].strip()


def parse_unsat(content):
    return UNSAT


def parse_vars(content):
    header, body = content.split('||')
    var_and_types = body.split()
    for item in var_and_types:
        name, type = item.split(':')
        if type == 'Int':
            Symbol(name, typename=INT)
        elif type == 'Bool':
            Symbol(name, typename=BOOL)
        else:
            print("var {} has unsupport type {}".format(name, type))
            assert False


def parse_line(content: str):
    content = content.strip()
    if content.startswith("Input"):
        return parse_input_rule(content)
    elif content.startswith("Def"):
        return parse_definition(content)
    elif content.startswith("AddFact"):
        return parse_add_fact(content)
    elif content.startswith("DeriveFact"):
        return parse_derive_fact(content)
    elif content.startswith("DeriveLemma"):
        return parse_lemma(content)
    elif content.startswith("UNSAT"):
        return parse_unsat(content)
    elif content.startswith("Vars"):
        return parse_vars(content)
    elif content.startswith("AXIOM"):
        return parse_axiom(content)
    elif content.startswith("c"):
        # comment line, skip it
        return 1
    else:
        print("unrecongizable proof line {}".format(content))
        assert (False)


def parse_proof(proof_name):
    AXIOM.clear()
    Lemma.Lemmas.clear()
    ordered_rules = []
    is_unsat = False
    with open(proof_name, 'r') as infile:
        line = infile.readline()
        while line:
            res = parse_line(line)
            if isinstance(res, str):
                ordered_rules.append(res)
            if res == UNSAT:
                is_unsat = True
            line = infile.readline()

    if is_unsat:
        return ordered_rules
    else:
        return False


def check_conflict():
    # by default, we first consider every single facts
    solver = Solver(name='z3')
    solver.z3.set(':core.minimize', True)
    for axiom in AXIOM:
        solver.add_assertion(axiom)
    for fact in Fact.Facts:
        if fact is not None:
            solver.add_assertion(fact.get_assumption_clause())
    facts = [f.assumption_lit for f in Fact.Facts if f is not None]
    res = solver.solve(facts)
    if res:
        m = solver.get_model()
        # print(m)
        return False
    else:
        simplified_derivations = []
        cores = [str(i) for i in get_assumption_core(solver)]
        print(cores)
        return cores


def check_proof(derivations, cores, project_usage=True):
    UNSAT_CORES = set()
    cores = set(cores)
    backward = ["UNSAT || {}".format(' '.join(cores))]
    while derivations:
        id = derivations.pop()
        if id not in cores:
            continue
        else:
            # check the derivation
            content = get_content_by_id(id)
            if isinstance(content, InputRule):
                UNSAT_CORES.add(content)
                backward.append(content)
            else:
                assert isinstance(content, Derivation)
                if content.check():
                    deps = content.get_dep()
                    cores.update(deps)
                    backward.append(content)
                else:
                    return False, id

    return UNSAT_CORES, backward


def add_vars(derivations):
    records = set()
    for d in derivations:
        if isinstance(d, Fact):
            if d.formula:
                variables = get_free_variables(d.formula)
                for atom in variables:
                    a_type = get_type(atom)
                    records.add((str(atom), str(a_type)))
    derivations.append("Vars || {}".format(' '.join(["{}:{}".format(a, b) for a, b in records])))


def check_and_minimize(input_proof, output_proof=None):
    derivations = parse_proof(input_proof)
    if derivations:
        print("detect conflict, and start backward checking")
        parse_fact_formulas()
        cores = check_conflict()
        if not cores:
            print("Failed: conflict claimed, but not detected")
            return False
        else:
            print("Conflict detected, start backward checking")
            UNSAT_core, backward_d = check_proof(derivations, cores)
            if UNSAT_core:
                simp_d = backward_d[::-1]
                add_vars(simp_d)
                if output_proof:
                    with open(output_proof, 'w') as out:
                        for i in simp_d:
                            out.write("{}\n".format(str(i)))
                else:
                    for i in simp_d:
                        print(str(i))
                return UNSAT_core, simp_d
            else:
                print("checking failed at step {}".format(backward_d))
                return False
    else:
        print("Failed: No conflict declared")
        return False


if __name__ == "__main__":
    print("checking proof")
    # input_proof = "/Users/nickfeng/SFAH19/runtime-verif/dressingRobot/proof.txt"
    input_proof = "/Users/nickfeng/SFAH19/runtime-verif/LeaderElection/proof.txt"
    output_proof = "/Users/nickfeng/SFAH19/runtime-verif/dressingRobot/proof_simplified.txt"
    check_and_minimize(input_proof)
