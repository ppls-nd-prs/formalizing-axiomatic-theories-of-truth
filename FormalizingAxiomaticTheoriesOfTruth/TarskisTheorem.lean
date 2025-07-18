import FormalizingAxiomaticTheoriesOfTruth.ProofTheory
import FormalizingAxiomaticTheoriesOfTruth.BasicTheories
open FirstOrder
open Language

namespace DiagonalLemma
open Languages
open L_T
open Calculus
open PA
def sentence_encoding (s : ℒₜ.Sentence) : ℒₜ.Term (Empty ⊕ Fin 0) := L_T.numeral (Encodable.encodeList (BoundedFormula.listEncode s))
  scoped notation "⌜"φ"⌝" => sentence_encoding φ

axiom diagonal_lemma
  (φ : BoundedFormula ℒₜ (Fin 1) 0) :
  ∃ (ψ : Sentence ℒₜ),
    𝐓𝐁 ⊢
      (bf_empty_to_bf_N (ψ ⇔ (Induction.formula_substitution (⌜ψ⌝) φ)))

end DiagonalLemma

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

namespace LiarParadox
open Languages
open L_T
open Calculus
open PA
open BoundedFormula
open Derivations
open TB
open DiagonalLemma

-- def syntax_and_PA : Set (Formula ℒₜ ℕ) :=
--   syntax_theory ∪ 𝐏𝐀𝐓

-- def unrestricted_TB : Theory ℒₜ :=
--   { φ | ∃ ψ : Sentence ℒₜ , φ = (T(⌜ψ⌝) ⇔ ψ) }

-- def syntax_and_PA_unres_TB : ℒₜ.Theory :=
--   𝐏𝐀 ∪ unrestricted_TB

def false_formula : Formula ℒₜ ℕ := ⊥
theorem tarskis_theorem : 𝐓𝐁 ⊢ false_formula := by
  have liar_formula_exists :
    ∃ (ψ1 : ℒₜ.Sentence),
      𝐓𝐁 ⊢ (ψ1 ⇔ ∼T(⌜ψ1⌝)) := by
  -- --     -- apply Exists.elim
  -- --     -- let φ : (BoundedFormula.not BoundedFormula.rel Rel.t ![(&0)])
  -- --     -- apply diagonal_lemma φ
  -- --     -- sorry
      let φ : BoundedFormula ℒₜ (Fin 1) 0 := ∼T(#0)
      have step1: ∀ψ : ℒₜ.Sentence, φ/[⌜ψ⌝] = ∼T(⌜ψ⌝) := by

      apply diagonal_lemma φ

      sorry
  obtain ⟨ψ⟩ := liar_formula_exists
  -- have liar_formula_exists :
  --   ∃ (ψ : Formula ℒₜ ℕ),
  --     syntax_and_PA_unres_TB ⊢ (ψ ⇔ (∼T(var (Sum.inl 0)))////[⌜ψ⌝]) := by
  --   apply diagonal_lemma ∼T(var (Sum.inl 0))

  have liar_t_instance : syntax_and_PA_unres_TB ⊢ (T(⌜ψ⌝) ⇔ ψ) := by
    simp
    exact
  have intermediate_lemma : syntax_and_PA_unres_TB ⊢ (T(⌜ψ⌝) ⇔ ∼T(⌜ψ⌝)) := by
      -- obtain ⟨derivation⟩ := eqv_trans syntax_and_PA_unres_TB (T(⌜ψ⌝)) (∼T(⌜ψ⌝)) ψ
      simp
      exact
  sorry
  sorry
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
  open LPA
  open Calculus
  open BoundedFormula

  lemma test {t t' : ℒ.Term (ℕ ⊕ Fin 0)} : ((var (Sum.inl 0) =' t)////[t']) = (t' =' t):= by
    #check ((var (Sum.inl 0) =' t)////[t'])
    #check t' =' t

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
