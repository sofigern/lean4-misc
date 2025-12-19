# lean4-misc
This is the repo for arbitrary lean4 experiments.

**Disclaimer**: The explanation below is based on my rather amatour understanding of the subject, and while I belive it is generally correct, it still may contain some factual mistakes or being misleading.

It's planned more like a home-learning project, though if you're reading this by any chance, don't hesitate correct me about anything.


## Where To Start

It's the best to start with looking at the [Lean4 repo](https://github.com/leanprover/lean4), and all the materials described there.

## Propositional logic
> ... the approach followed in the Calculus of Constructions, and hence in Lean as well. The fact that the rules for implication in a proof system for natural deduction correspond exactly to the rules governing abstraction and application for functions is an instance of the Curry-Howard isomorphism, sometimes known as the propositions-as-types paradigm.

To learn more about Curry-Howard isomorphism one can check these materials: 
- [Lean4 and the Curry-Howard Isomorphism (Luis Wirth)](https://www.youtube.com/watch?v=Sy_4z751YWI).

## Notes
Fundations of Lean4 Calculus of Constructions are similar to axioms desribed in [Kleene's Mathematical Logic](https://cdn.preterhuman.net/texts/math/Kleene%20%20Mathemathical%20logic%20scaned%20by%20YRB.pdf).

1.a ⊢ A ⊃ (B ⊃ A)
1.b ⊢ (A ⊃ B) ⊃ ((A ⊃ (B ⊃ Γ)) ⊃ (A ⊃ Γ))
3.  ⊢ A ⊃ B ⊃ (A ∧ B)
4.a ⊢ A ∧ B ⊃ A
4.b ⊢ A ∧ B ⊃ B
5.a ⊢ A ⊃ A ∨ B
5.b ⊢ B ⊃ A ∨ B
6.  ⊢ (A ⊃ Γ) ⊃ (B ⊃ Γ) ⊃ (A ∨ B ⊃ Γ)
7.  ⊢ (A ⊃ B) ⊃ (A ⊃ ¬B) ⊃ ¬A
8ᵒ. ⊢ ¬¬A ⊃ A

The 8ᵒ. ⊢ ¬¬A ⊃ A with all other rules is the logical equivalent to the [Excluded Middle Law](https://en.wikipedia.org/wiki/Law_of_excluded_middle) (em ⊢ A ∨ ¬A) and it separates [Intuitionistic Logic](https://en.wikipedia.org/wiki/Intuitionistic_logic) from [Classical Logic](https://en.wikipedia.org/wiki/Classical_logic).

Though by the end of the day it's the same, one still can found it's more convinient to think about formulas 1-8 as axioms instead of just valid formulas that makes sense because their truth table are returning True for all inputs, as it is described in Kleene's Mathematical Logic. 

From this point of view I'd recommend to think about Calculus of Constructions more like it's described in [Mendelson's Introductioon to Mathematical Logic](https://www.karlin.mff.cuni.cz/~krajicek/mendelson.pdf), though initially it relies on the different set of axioms.

Though, as I mentioned formerly for Propositional Logic (0 Order Languages, Sort 0 Types) it's all the same by the end of the day, and the only meaningful difference lies is in between theorems set in Classical and Intutionistic logics.

Foundations of Lean4 are neither ones described in Kleene nor in Mendelson, though they have many in familiar and I'll try to explore it a bit more in [foundations](./foundations/) materials.
