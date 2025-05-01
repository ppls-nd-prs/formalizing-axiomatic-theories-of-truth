import FormalizingAxiomaticTheoriesOfTruth.ProofTheory
import FormalizingAxiomaticTheoriesOfTruth.Syntax
import FormalizingAxiomaticTheoriesOfTruth.Conservativity
open FirstOrder
open Language

namespace LiarParadox
open Languages
open LPA
open L_T
open SyntaxTheory
open TermEncoding
open Calculus
open PA
open BoundedFormula

def syntax_and_PA : Theory ℒₜ :=
  syntax_theory ∪ peano_arithmetic

axiom diagonal_lemma {syntax_and_PA_unres_TB} (φ : BoundedFormula ℒₜ Empty 1) :
  let φ := φ.toFormula.relabel (fun x => match x with | Sum.inr i => i)
  ∃ (ψ : Formula ℒₜ ℕ), syntax_and_PA_unres_TB ⊢ (ψ ⇔ φ /[⌜ψ⌝])

-- def unrestricted_TB (φ : Formula ℒₜ ℕ) :=
--   T(⌜φ⌝) ⇔ φ

def unrestricted_TB : Theory ℒₜ :=
  { φ | ∃ ψ : Formula ℒₜ ℕ, φ = (T(⌜ψ⌝) ⇔ ψ) }

def syntax_and_PA_unres_TB : Theory ℒₜ :=
  syntax_and_PA ∪ unrestricted_TB

-- theorem liar_paradox : syntax_and_PA_unres_TB ⊢ ⊥ := by
--   let φ : BoundedFormula ℒₜ Empty 1 :=
--     ¬(T( &0 ))
--   obtain ⟨ψ, hψ⟩ := diagonal_lemma φ


def false_formula : Formula ℒₜ ℕ := ⊥
theorem liar_paradox : syntax_and_PA_unres_TB ⊢ false_formula := by
  let φ : BoundedFormula ℒₜ Empty 1 := ∼(T(&0))
  obtain ⟨ψ, hψ⟩ := diagonal_lemma φ
  apply Exists.elim
  have h1 : syntax_and_PA_unres_TB ⊢ (ψ ⟹ ∼T(⌜ψ⌝)) := by
    sorry

  have h2 : syntax_and_PA_unres_TB ⊢ (∼T(⌜ψ⌝) ⟹ ψ) := by
    sorry
end LiarParadox

namespace SandBox
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
apply Iff.intro
intro h
apply And.intro
exact And.right h
exact And.left h
intro hp
apply And.intro
exact And.right hp
exact And.left hp

example : p ∨ q ↔ q ∨ p := by
apply Iff.intro
intro h
cases h
apply Or.inr
assumption
apply Or.inl
assumption
intro hq
cases hq
apply Or.inr
assumption
apply Or.inl
assumption

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
sorry

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry
end SandBox
