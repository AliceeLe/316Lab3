from typing import Tuple
from lark import Lark, Transformer
import pca_logic as pca

formula_grammar = r"""
    // Logical Formulas
    ?form2: atom
         | quantification
         | "(" form ")"
    ?form: form2
         | says
         | implication
         | "(" form2 ")"

    implication: form "->" form             -> implies

    says: term "says" form2                  -> says

    quantification: "!" UPPER "." form      -> forall

    atom: LOWER "(" [terms] ")"             -> atom

    terms: term ("," term)*                 -> terms

    ?term: LOWER                            -> constant
         | UPPER                            -> variable

    pvar: LOWER                             -> pvar

    // Tokens
    %import common.WS
    %ignore WS

    LOWER: /[a-z][A-Za-z_0-9]*/
    UPPER: /[A-Z][A-Za-z_0-9]*/
"""

policy_grammar = r"""
    ?start: policy

    policy: (declaration ";")*              -> policy

    declaration: pvar ":" form              -> declaration

"""

typing_grammar = r"""
    ?start: typing

    // Typing: A proof followed by ":" and a formula
    typing: proof2 ":" form                  -> typing

    // Proof rules
    ?proof: pvar                             
          | "{" proof2 "}" "_" term           -> wrap
          | "let" "{" pvar "}" "_" term "=" proof2 "in" proof2 -> letwrap
          | "let" pvar "=" proof2 "in" proof2  -> let_
          | "(" proof2 ")"
    ?proof2: proof                             
          | proof2 proof                      -> app
          | proof2 "[" term "]"               -> inst

"""

class PolicyTransformer(Transformer):
    def policy(self, items):
        
        return items if items else [] # List of Declarations

    def declaration(self, items):
        return pca.Declaration(constant=items[0], formula=items[1])

    def pvar(self, items):
        return pca.Constant(name=items[0])

    def implies(self, items):
        return pca.Implies(premise=items[0], conclusion=items[1])

    def says(self, items):
        return pca.Says(agent=items[0], formula=items[1])

    def forall(self, items):
        return pca.Forall(variable=pca.Variable(items[0]), formula=items[1])

    def atom(self, items):
        predicate = items[0]
        terms = items[1] if len(items) > 1 else []
        return pca.Atom(predicate=pca.Constant(predicate), terms=terms)

    def terms(self, items):
        return items

    def variable(self, items):
        return pca.Variable(id=items[0])

    def constant(self, items):
        return pca.Constant(name=items[0])

    def LOWER(self, token):
        return str(token)

    def UPPER(self, token):
        return str(token)

class TypingTransformer(Transformer):
    def typing(self, items):
        return (items[0], items[1])  # Tuple of (Proof, Form)

    def letwrap(self, items):
        return pca.LetWrap(v=items[0], a=items[1], m=items[2], n=items[3])

    def let_(self, items):
        return pca.Let(v=items[0], m=items[1], n=items[2])

    def app(self, items):
        return pca.App(m1=items[0], m2=items[1])

    def inst(self, items):
        return pca.Inst(m=items[0], t=items[1])

    def wrap(self, items):
        return pca.Wrap(m=items[0], a=items[1])

    def pvar(self, items):
        return pca.Pvar(name=items[0])

    def implies(self, items):
        return pca.Implies(premise=items[0], conclusion=items[1])

    def says(self, items):
        return pca.Says(agent=items[0], formula=items[1])

    def forall(self, items):
        return pca.Forall(variable=items[0], formula=items[1])

    def atom(self, items):
        predicate = items[0]
        terms = items[1] if len(items) > 1 else []
        return pca.Atom(predicate=pca.Constant(predicate), terms=terms)

    def terms(self, items):
        return items

    def variable(self, items):
        return pca.Variable(id=items[0])

    def constant(self, items):
        return pca.Constant(name=items[0])

    def LOWER(self, token):
        return str(token)

    def UPPER(self, token):
        return str(token)

def parse_policy(s: str) -> pca.Policy:
    try:
        parser = Lark(policy_grammar+"\n"+formula_grammar, parser='lalr', start='start')
        tree = parser.parse(s)
        transformer = PolicyTransformer()
        ast = transformer.transform(tree)
        
        return ast if ast else []
    except Exception as e:
        print(f"Error parsing policy {s}: {e}")
        raise

def parse_typing(s: str) -> Tuple[pca.Proof, pca.Form]:
    try:
        parser = Lark(typing_grammar+"\n"+formula_grammar, parser='lalr', start='start')
        tree = parser.parse(s)
        transformer = TypingTransformer()
        ast = transformer.transform(tree)
        return ast
    except Exception as e:
        print(f"Error parsing typing {s}: {e}")
        raise
