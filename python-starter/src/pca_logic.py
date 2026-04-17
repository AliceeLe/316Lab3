from dataclasses import dataclass
from typing import List

class Token:
    @classmethod
    def parseaction(cls, toks: list):
        new = cls(*toks)
        toks.clear()
        toks.append(new)

@dataclass
class Term(Token):
    pass

@dataclass
class Variable(Term):
    id: str

@dataclass
class Constant(Term):
    name: str


@dataclass
class Form(Token):
    pass

@dataclass
class Atom(Form):
    predicate: Constant
    terms: List[Term]

@dataclass
class Says(Form):
    agent: Term
    formula: Form

@dataclass
class Implies(Form):
    premise: Form
    conclusion: Form

@dataclass
class Forall(Form):
    variable: Variable
    formula: Form


@dataclass
class Ante(Token):
    pass

@dataclass
class Declaration(Ante):
    constant: Constant
    formula: Form


Policy = List[Ante]


@dataclass
class Proof(Token):
    pass

@dataclass
class Pvar(Proof):
    name: str

@dataclass
class App(Proof):
    m1: Proof
    m2: Proof

@dataclass
class Inst(Proof):
    m: Proof
    t: Term

@dataclass
class Wrap(Proof):
    m: Proof
    a: Term

@dataclass
class LetWrap(Proof):
    v: Pvar
    a: Term
    m: Proof
    n: Proof

@dataclass
class Let(Proof):
    v: Pvar
    m: Proof
    n: Proof

def stringify_term(t: Term) -> str:
    match t:
        case Variable(id):
            return id
        case Constant(name):
            return name
        case _:
            raise TypeError("Unknown term type")

def stringify_terms(ts: List[Term]) -> str:
    if not ts:
        return ""
    return ", ".join(stringify_term(t) for t in ts)

def stringify_form(p: Form) -> str:
    match p:
        case Atom(predicate, terms):
            return f"{stringify_term(predicate)}({stringify_terms(terms)})"
        case Says(agent, formula):
            return f"({stringify_term(agent)} says {stringify_form(formula)})"
        case Implies(premise, conclusion):
            return f"({stringify_form(premise)} -> {stringify_form(conclusion)})"
        case Forall(variable, formula):
            return f"(!{stringify_term(variable)}. {stringify_form(formula)})"
        case _:
            print(p)
            raise TypeError("Unknown form type")

def stringify_policy(policy: Policy) -> str:
    if not policy:
        return ""
    return ";\n".join(f"{decl.constant} : {stringify_form(decl.formula)}" for decl in policy) + ";"

def stringify_proof(m: Proof) -> str:
    match m:
        case Pvar(name):
            return name
        case App(m1, m2):
            return f"({stringify_proof(m1)} {stringify_proof(m2)})"
        case Inst(m, t):
            return f"({stringify_proof(m)} [{stringify_term(t)}])"
        case Wrap(m, a):
            return f"{{ {stringify_proof(m)} }}_{stringify_term(a)}"
        case LetWrap(v, a, m, n):
            return f"let {{{v}}}_{stringify_term(a)} = {stringify_proof(m)} in ({stringify_proof(n)})"
        case Let(v, m, n):
            return f"let {v} = {stringify_proof(m)} in ({stringify_proof(n)})"
        case _:
            print(m)
            raise TypeError("Unknown proof type")

def stringify_typing(proof : Proof, form : Form) -> str:
    return f"{stringify_proof(proof)}\n : \n{stringify_form(form)}"
