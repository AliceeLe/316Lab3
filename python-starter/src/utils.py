import pca_logic as pca

# Counter to generate fresh variables
count = 0

def fresh_var(x: pca.Variable) -> pca.Variable:
    global count
    x_prime_id = f"{x.id}'{count}"
    count += 1
    return pca.Variable(x_prime_id)

def eq_term(s: pca.Term, t: pca.Term) -> bool:
    raise NotImplementedError("unimplemented")

def eq_form(p: pca.Form, q: pca.Form) -> bool:
    raise NotImplementedError("unimplemented")

def subst_form(x: pca.Variable, t: pca.Term, p: pca.Form) -> pca.Form:
    raise NotImplementedError("unimplemented")
