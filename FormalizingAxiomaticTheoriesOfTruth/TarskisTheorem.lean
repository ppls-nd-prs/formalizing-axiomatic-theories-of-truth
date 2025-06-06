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
open Derivations
open TB

variable {L : Language}
[∀ n, DecidableEq (L.Functions n)]
[∀ n, DecidableEq (L.Relations n)]
[DecidableEq (Formula L ℕ)]

def syntax_and_PA : Theory ℒₜ :=
  syntax_theory ∪ peano_arithmetic

def unrestricted_TB : Theory ℒₜ :=
  { φ | ∃ ψ : Formula ℒₜ ℕ, φ = (T(⌜ψ⌝) ⇔ ψ) }

def syntax_and_PA_unres_TB : Theory ℒₜ :=
  syntax_and_PA ∪ unrestricted_TB

-- axiom diagonal_lemma (φ : BoundedFormula ℒₜ Empty 1) :
--     ∃ (ψ : Formula ℒₜ ℕ),
--     syntax_and_PA_unres_TB ⊢ (ψ ⇔ (φ.toFormula.relabel (fun x => match x with
--   | Sum.inr i => i
--   | Sum.inl e => nomatch e)) /[⌜ψ⌝])

axiom diagonal_lemma
  (φ : BoundedFormula ℒₜ Empty 1) :
  ∃ (ψ : Formula ℒₜ ℕ),
    syntax_and_PA_unres_TB ⊢
      (ψ ⇔ (φ /[L_T.numeral (formula_N_tonat ψ)]))

-- def bicond_elim (Th: unrestricted_TB) (A B : Formula L ℕ ) :
--   unrestricted_TB ⊢ A ⇔ B := by
--   let h: unrestricted_TB ⊢ A ⇔ b
--   h.elim Derivation unrestricted_TB ∅ (A → B) ∧ (B → A) :=
--   have lemma : Derivable unrestricted_TB φ ∧ ψ by
--     apply Nonempty
--     apply Derivation.right_conjunction
--     exact lax {φ, ψ}, {φ}
--   apply cut
--     exact h.elim
--     apply lemma A, B

lemma eqv_trans : ∀Th : Set (Formula L ℕ), ∀(A B C : L.Formula ℕ), Nonempty (Derivation Th {A ⇔ B, C ⇔ B} {A ⇔ C}) := by
  sorry

lemma inconsistency : ∀Th : Set (Formula L ℕ), ∀(A : L.Formula ℕ), Nonempty (Derivation Th {A ⇔ ∼A} {⊥}) := by
  sorry

def false_formula : Formula ℒₜ ℕ := ⊥
theorem tarskis_theorem : syntax_and_PA_unres_TB ⊢ false_formula := by
  -- Step 1: Get the liar formula using the diagonal lemma
  have liar_formula_exists :
    ∃ (ψ : Formula ℒₜ ℕ),
      syntax_and_PA_unres_TB ⊢ (ψ ⇔ ∼T(⌜ψ⌝)) := by
      -- apply Exists.elim
      -- let φ : (BoundedFormula.not BoundedFormula.rel Rel.t ![(&0)])
      -- apply diagonal_lemma φ
      -- sorry
      let φ : BoundedFormula ℒₜ Empty 1 := ∼(T(&0))
      apply diagonal_lemma φ
      -- obtain ⟨ψ,hψ⟩ := diagonal_lemma φ
      -- use ψ
      -- rw [th_to_set_form]

  -- rw [this] at hψ
  -- use ψ
  -- exact hψ
  obtain ⟨ψ, liar_formula_der⟩ := liar_formula_exists

  have liar_t_instance : syntax_and_PA_unres_TB ⊢ (T(⌜ψ⌝) ⇔ ψ) := by
    sorry
  -- Step 3: Derive T(⌜ψ⌝) ⇔ ∼T(⌜ψ⌝)
  have intermediate_lemma :
    syntax_and_PA_unres_TB ⊢ (T(⌜ψ⌝) ⇔ ∼T(⌜ψ⌝)) := by
      obtain ⟨derivation⟩ := eqv_trans syntax_and_PA_unres_TB (T(⌜ψ⌝)) (∼T(⌜ψ⌝)) ψ
      sorry
  obtain ⟨d⟩ := inconsistency (th_to_set_form syntax_and_PA_unres_TB) (T(⌜ψ⌝))
  sorry





  -- let φ : BoundedFormula ℒₜ Empty 1 := ∼(T(&0))
  -- obtain ⟨ψ, hψ⟩ := diagonal_lemma φ
  -- apply Exists.elim
  -- have h1 : syntax_and_PA_unres_TB ⊢ (ψ ⟹ ∼T(⌜ψ⌝)) := by
  --   sorry

  -- have h2 : syntax_and_PA_unres_TB ⊢ (∼T(⌜ψ⌝) ⟹ ψ) := by
  --   sorry

end LiarParadox

namespace SandBox

open Languages
  open L_T
  open Calculus
  open BoundedFormula

  def f₁ : Formula ℒₜ ℕ :=
    ∀' (&0 =' &0)
  def f₂ : Formula ℒₜ ℕ :=
    ∀' ∀' (&0 =' &1)
  def S₁ : Set (Formula ℒₜ ℕ) := {f₁, f₂}
  def S₂ : Finset (Formula ℒₜ ℕ) := ∅
  def S₃ : Finset (Formula ℒₜ ℕ) := {f₁ ∨' f₂}
  def der₁ : Derivation S₁ S₂ S₃ := by
    let S₄ : Finset (Formula ℒₜ ℕ) := {f₁, f₂}
    have step1 : f₁ ∈ S₁ ∧ f₁ ∈ S₄ := by
      simp[S₁,S₄]
    have step2 : ∃f, f ∈ S₁ ∧ f ∈ S₄ := by
      apply Exists.intro f₁ step1
    have step3 : Derivation S₁ S₂ S₄ := by
      simp[S₁,S₂,S₄]
      apply Derivation.tax step2
    have step4 : S₃ = (S₄ \ {f₁, f₂}) ∪ {f₁ ∨' f₂} := by
      simp[S₃,S₄]
    have step5 : Derivation S₁ S₂ S₃ := by
      simp[S₁,S₂,S₃]
      apply Derivation.right_disjunction f₁ f₂ S₄ step3 step4
    exact step5

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

-- -- associativity of ∧ and ∨
-- example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
-- sorry

-- example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- -- distributivity
-- example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
-- example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry
end SandBox
