import pca_logic as pca

# Counter to generate fresh variables
count = 0

def fresh_var(x: pca.Variable) -> pca.Variable:
    global count
    x_prime_id = f"{x.id}'{count}"
    count += 1
    return pca.Variable(x_prime_id)

def eq_term(s: pca.Term, t: pca.Term) -> bool:
    match (s, t):
        case (pca.Variable(id1), pca.Variable(id2)):
            return id1 == id2
        case (pca.Constant(name1), pca.Constant(name2)):
            return name1 == name2
        case _:
            return False

def eq_form(p: pca.Form, q: pca.Form) -> bool:
    match (p, q):
        case (pca.Atom(pred1, terms1), pca.Atom(pred2, terms2)):
            terms1 = terms1 or []
            terms2 = terms2 or []
            return (eq_term(pred1, pred2) and
                    len(terms1) == len(terms2) and
                    all(eq_term(s, t) for s, t in zip(terms1, terms2)))
        case (pca.Says(agent1, form1), pca.Says(agent2, form2)):
            return eq_term(agent1, agent2) and eq_form(form1, form2)
        case (pca.Implies(prem1, conc1), pca.Implies(prem2, conc2)):
            return eq_form(prem1, prem2) and eq_form(conc1, conc2)
        case (pca.Forall(var1, form1), pca.Forall(var2, form2)):
            if eq_term(var1, var2):
                return eq_form(form1, form2)
            else:
                fresh = fresh_var(var1)
                renamed1 = subst_form(var1, fresh, form1)
                renamed2 = subst_form(var2, fresh, form2)
                return eq_form(renamed1, renamed2)
        case _:
            return False

def subst_form(x: pca.Variable, t: pca.Term, p: pca.Form) -> pca.Form:
    match p:
        case pca.Atom(pred, terms):
            new_pred = subst_term(x, t, pred)
            new_terms = [subst_term(x, t, s) for s in (terms or [])]
            return pca.Atom(new_pred, new_terms)
        case pca.Says(agent, formula):
            return pca.Says(subst_term(x, t, agent), subst_form(x, t, formula))
        case pca.Implies(prem, conc):
            return pca.Implies(subst_form(x, t, prem), subst_form(x, t, conc))
        case pca.Forall(var, formula):
            if eq_term(var, x):
                # x is bound here, don't substitute
                return p
            else:
                # Avoid capture: if t is a variable and var == t, rename bound var
                if isinstance(t, pca.Variable) and eq_term(var, t):
                    fresh = fresh_var(var)
                    renamed = subst_form(var, fresh, formula)
                    return pca.Forall(fresh, subst_form(x, t, renamed))
                return pca.Forall(var, subst_form(x, t, formula))
        case _:
            raise TypeError(f"Unknown form type: {p}")

def subst_term(x: pca.Variable, t: pca.Term, s: pca.Term) -> pca.Term:
    match s:
        case pca.Variable(id):
            if id == x.id:
                return t
            return s
        case pca.Constant(_):
            return s
        case _:
            raise TypeError(f"Unknown term type: {s}")
