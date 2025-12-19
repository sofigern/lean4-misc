/-

In this document, I will explore what one can call Lean4 Propositional Logic Axioms.

While I aim to provide more comprehensive explanations
related to Dependent Types theory in the future,
this content currently serves more like an informal exploration of
inhabited Propositions in Lean4, and how those are corresponding
to the Propositional Logic Axioms as one can find in
Mathematical logic books.

-/

/-
So as in classical definitions the first thing is to define well formed formulas.

================================================================================
FORMAL LOGICAL SYSTEM DEFINITION
================================================================================

A formal logical system is constructed from the following components:

1. ALPHABET (Countable Symbol Set)
   - A countable set of symbols Y = {s1, s2, s3, ...}
   - Symbols form the basic vocabulary of the system
   - Any finite sequence of symbols is called an EXPRESSION of Y

2. WELL-FORMED FORMULAS (WFS)
   - A subset of all possible expressions
   - Defined by formation rules (formal grammar)
   - Effective procedure exists to determine WFS membership
   - Example: "(p AND q) OR NOT r" is WFS in propositional logic
   - Non-example: "AND OR p q" is NOT WFS (violates grammar)

3. AXIOMS
   - A distinguished set of WFS accepted as foundational truths
   - Starting point for deriving new theorems
   - Effective decision procedure often exists for axiom membership
   - System with such procedure is called AXIOMATIC THEORY
   - Note: Different axiom sets create different logical systems

4. RULES OF INFERENCE (R1, R2, ..., Rn)
   - Finite set of inference rules among WFS
   - Each rule Ri has a unique positive integer j
   - Rule Ri: Given j premises (WFS), determines if conclusion follows
   - Effective procedure exists to check whether j premises stand in
     relation Ri to candidate conclusion B
   - If yes: B is DIRECT CONSEQUENCE of premises via Ri
   - Enables mechanical proof verification (decidability)

================================================================================
RELATIONSHIP: FORMULAS -> PROPOSITIONS
================================================================================

FORMULA (Syntactic Object):
  - Finite sequence of symbols following grammar rules
  - Purely syntactic, mechanical manipulation allowed
  - Example: (p AND q) -> r
  - Not itself a proposition, but REPRESENTS a proposition

PROPOSITION (Semantic Object):
  - Abstract concept representing truth or falsity
-/

/- Alphabet
  In Lean4 almost any litteral can be a symbol representing a proposition.
-/

def a := Prop
def γ := Prop
def h₁ := Prop

/- Well-formed formulas
  Well formed formulas for propositional logic are defined by the following rules:
  1. Any proposition is a well formed formula.
  2. If A and B are well formed formulas, then (A ⊃ B) is a well formed formula.
  3. If A and B are well formed formulas, then (A ∧ B) is a well formed formula.
  4. If A and B are well formed formulas, then (A ∨ B) is a well formed formula.
  5. If A is a well formed formula, then ¬A is a well formed formula.
-/

variable { A B C : Prop }

#check A → B
#check A ∧ B
#check A ∨ B
#check ¬A

/- Rules of inference
  Rules of inference are the rules that allow one to derive new well formed formulas from existing well formed formulas.
  Here are some of the most common rules of inference:
  1. Modus ponens: If A and A → B are well formed formulas, then B is a well formed formula.
  2. Implication introduction: If A and B are well formed formulas, then A → B is a well formed formula.
  3. Conjunction elimination: If A ∧ B are well formed formulas, then A and B are well formed formulas.
  4. Disjunction introduction: If A is a well formed formula, then A ∨ B is a well formed formula.
  5. Disjunction elimination: If A ∨ B is a well formed formula, then A is a well formed formula or B is a well formed formula.
  6. Conjunction introduction: If A and B are well formed formulas, then A ∧ B is a well formed formula.
-/

def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p

axiom modus_ponens (p q : Prop) :
  Proof (Implies p q) → Proof p →
  Proof q

axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)

/- Once it is agreed simplify this syntax to one that is used in Lean4
based on propositions-as-types paradigm most of this syntax is redundant
and reaching well formed formulas is just a matter of type checking of propositions that can be
constructed from lambda functions and predefined Rules of Inference.

In these terms we don't exactly need any axioms,
though we can show that WFS as in Kleene's Mathematical Logic are valid propositions in Lean4.
-/

/- For example these two tautologies are axioms in Kleene's Mathematical Logic system
and inhabitate Propositions in Lean4 just bcause can be constructed from lambda functions directly
-/
example : p → q → p := fun hp : p => fun hq : q => hp -- 1.a ⊢ A ⊃ (B ⊃ A)
example : (p → q) → ((p → q → r) → (p → r)) :=      -- 1.b ⊢ (A ⊃ B) ⊃ ((A ⊃ (B ⊃ Γ)) ⊃ (A ⊃ Γ))
  fun hpq : p → q => fun hpqr : p → q → r => fun hp : p => hpqr hp (hpq hp)


/- Conjunction elimination and introduction though relies on predefined Rules of Inference -/
example : p → q → p ∧ q := fun hp : p => fun hq : q => And.intro hp hq -- 3. ⊢ A ⊃ (B ⊃ A ∧ B)
example : p ∧ q → p := fun hpq : p ∧ q => And.left hpq -- 4.a ⊢ A ∧ B ⊃ A
example : p ∧ q → q := fun hpq : p ∧ q => And.right hpq -- 4.b ⊢ A ∧ B ⊃ B


/- Disjunction elimination and introduction also relies on predefined Rules of Inference -/
example : p → p ∨ q := fun hp : p => Or.inl hp -- 5.a ⊢ A ⊃ A ∨ B
example : q → p ∨ q := fun hq : q => Or.inr hq -- 5.b ⊢ B ⊃ A ∨ B
example : (p → r) → (q → r) → (p ∨ q → r) := -- 6. ⊢ (A ⊃ Γ) ⊃ (B ⊃ Γ) ⊃ (A ∨ B ⊃ Γ)
  fun hpr : p → r => fun hqr : q → r => fun hpq : p ∨ q => Or.elim hpq hpr hqr

/- Principle of non-contradiction relies on `absurd` rule -/
example : (p → q) → (p → ¬q) → ¬p := -- 7. ⊢ (A ⊃ B) ⊃ (A ⊃ ¬B) ⊃ ¬A
  fun hpq : p → q => fun hpqn : p → ¬q => fun hp : p => absurd (hpq hp) (hpqn hp)

/- Double negation elimination relies on Excluded Middle Law in Classical Logic -/
open Classical
example : ¬¬p → p := --8. ⊢ ¬¬A ⊃ A
  fun (h: ¬¬p) =>
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
