import pca_logic as pca
from utils import eq_form, eq_term, subst_form

class VerifyException(Exception):
    """
    Exception raised during verification errors.

    Args:
        message (str): The error message describing the issue.
    """
    def __init__(self, message: str):
        super().__init__(message)
        self.message = message


def check_policy(gamma: pca.Policy):
    """
    Checks if the given policy `gamma` is well-formed.

    A well-formed policy requires:
    (a) Each v : P in gamma has a unique v.
    (b) In each declaration, all term variables are quantified and don't shadow one another.

    Raises:
        VerifyException: If gamma is not a well-formed policy.
    """
    seen_names = set()
    for decl in gamma:
        name = decl.constant.name if isinstance(decl.constant, pca.Constant) else decl.constant
        if name in seen_names:
            raise VerifyException(f"Duplicate policy variable: {name}")
        seen_names.add(name)
        # Check that all variables in the formula are bound and no shadowing
        check_form_vars(decl.formula, bound_vars=set())


def check_form_vars(p: pca.Form, bound_vars: set):
    """Check that all variable occurrences in p are bound, with no shadowing."""
    match p:
        case pca.Atom(pred, terms):
            for t in (terms or []):
                check_term_var(t, bound_vars)
            # pred is always a Constant in atoms (by grammar)
        case pca.Says(agent, formula):
            check_term_var(agent, bound_vars)
            check_form_vars(formula, bound_vars)
        case pca.Implies(prem, conc):
            check_form_vars(prem, bound_vars)
            check_form_vars(conc, bound_vars)
        case pca.Forall(var, formula):
            if var.id in bound_vars:
                raise VerifyException(f"Variable {var.id} shadows an outer binding")
            check_form_vars(formula, bound_vars | {var.id})
        case _:
            raise VerifyException(f"Unknown form type: {p}")


def check_term_var(t: pca.Term, bound_vars: set):
    match t:
        case pca.Variable(id):
            if id not in bound_vars:
                raise VerifyException(f"Unbound variable: {id}")
        case pca.Constant(_):
            pass
        case _:
            raise VerifyException(f"Unknown term type: {t}")


def lookup_policy(gamma: pca.Policy, name: str) -> pca.Form:
    for decl in gamma:
        decl_name = decl.constant.name if isinstance(decl.constant, pca.Constant) else decl.constant
        if decl_name == name:
            return decl.formula
    return None


def synth(gamma: pca.Policy, m: pca.Proof) -> pca.Form:
    match m:
        case pca.Pvar(name):
            # id rule: look up in policy
            p = lookup_policy(gamma, name)
            if p is None:
                raise VerifyException(f"Unknown proof variable: {name}")
            return p

        case pca.App(m1, m2):
            # →E: m1 ⇒ P → Q, m2 ⇐ P, result is Q
            ty1 = synth(gamma, m1)
            match ty1:
                case pca.Implies(prem, conc):
                    check(gamma, m2, prem)
                    return conc
                case _:
                    raise VerifyException(
                        f"App: expected function type, got {pca.stringify_form(ty1)}")

        case pca.Inst(m_inner, t):
            # ∀E: m ⇒ ∀x. P(x), result is P(t)
            ty = synth(gamma, m_inner)
            match ty:
                case pca.Forall(var, formula):
                    return subst_form(var, t, formula)
                case _:
                    raise VerifyException(
                        f"Inst: expected forall type, got {pca.stringify_form(ty)}")

        case _:
            raise VerifyException(f"Cannot synthesize type for proof: {pca.stringify_proof(m)}")


def check(gamma: pca.Policy, m: pca.Proof, p: pca.Form):
    """
    Γ ⊢ m ⇐ P  (checking mode for plain formula goals)
    LetWrap (saysE) is NOT allowed here — it only applies in aff context (inside a Wrap).
    """
    match m:
        case pca.Wrap(m_inner, a):
            # saysR: goal must be A says P, enter aff context
            match p:
                case pca.Says(agent, formula):
                    if not eq_term(agent, a):
                        raise VerifyException(
                            f"Wrap: agent mismatch: {pca.stringify_term(a)} vs {pca.stringify_term(agent)}")
                    check_aff(gamma, m_inner, a, formula)
                case _:
                    raise VerifyException(
                        f"Wrap: expected 'says' goal, got {pca.stringify_form(p)}")

        case pca.Let(v, m_inner, n):
            # cut: infer type of m, extend gamma, check n
            ty = synth(gamma, m_inner)
            v_name = v.name if isinstance(v, pca.Pvar) else str(v)
            new_gamma = gamma + [pca.Declaration(constant=pca.Constant(v_name), formula=ty)]
            check(new_gamma, n, p)

        case _:
            # ⇒/⇐ rule: synthesize and compare (LetWrap raises in synth)
            ty = synth(gamma, m)
            if not eq_form(ty, p):
                raise VerifyException(
                    f"Type mismatch: synthesized {pca.stringify_form(ty)}, expected {pca.stringify_form(p)}")


def check_aff(gamma: pca.Policy, m: pca.Proof, a: pca.Term, q: pca.Form):
    match m:
        case pca.LetWrap(v, a2, m_inner, n):
            # saysE: m_inner must synthesize A says P; bind v:P and continue in aff context
            if not eq_term(a, a2):
                raise VerifyException(
                    f"LetWrap: agent mismatch: expected {pca.stringify_term(a)}, got {pca.stringify_term(a2)}")
            ty = synth(gamma, m_inner)
            match ty:
                case pca.Says(agent, formula):
                    if not eq_term(agent, a2):
                        raise VerifyException(
                            f"LetWrap: says-agent mismatch: {pca.stringify_term(a2)} vs {pca.stringify_term(agent)}")
                    v_name = v.name if isinstance(v, pca.Pvar) else str(v)
                    new_gamma = gamma + [pca.Declaration(constant=pca.Constant(v_name), formula=formula)]
                    check_aff(new_gamma, n, a, q)
                case _:
                    raise VerifyException(
                        f"LetWrap: expected 'A says P' type, got {pca.stringify_form(ty)}")

        case pca.Let(v, m_inner, n):
            # cut inside aff context
            ty = synth(gamma, m_inner)
            v_name = v.name if isinstance(v, pca.Pvar) else str(v)
            new_gamma = gamma + [pca.Declaration(constant=pca.Constant(v_name), formula=ty)]
            check_aff(new_gamma, n, a, q)

        case _:
            # aff rule: delegate to plain check
            check(gamma, m, q)


def verify(gamma: pca.Policy, m: pca.Proof, p: pca.Form):
    """
    Verifies that the judgment `gamma ⊢ m ⇐ p` holds.

    Args:
        gamma (Policy): The policy under which to verify the proof.
        m (Proof): The proof to verify.
        p (Form): The formula to verify.

    Raises:
        VerifyException: If the verification `gamma ⊢ m ⇐ p` fails.
    """
    check(gamma, m, p)
