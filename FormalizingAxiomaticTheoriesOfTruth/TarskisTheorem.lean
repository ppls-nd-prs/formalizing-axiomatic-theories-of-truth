import FormalizingAxiomaticTheoriesOfTruth.ProofTheory
import FormalizingAxiomaticTheoriesOfTruth.ArithTheories
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

def syntax_and_PA : Set (Formula ℒₜ ℕ) :=
  syntax_theory ∪ 𝐏𝐀𝐓

def unrestricted_TB : Theory ℒₜ :=
  { φ | ∃ ψ : Formula ℒₜ ℕ, φ = (T(⌜ψ⌝) ⇔ ψ) }

def syntax_and_PA_unres_TB : Set (Formula ℒₜ ℕ) :=
  syntax_and_PA ∪ unrestricted_TB

-- axiom diagonal_lemma (φ : BoundedFormula ℒₜ Empty 1) :
--     ∃ (ψ : Formula ℒₜ ℕ),
--     syntax_and_PA_unres_TB ⊢ (ψ ⇔ (φ.toFormula.relabel (fun x => match x with
--   | Sum.inr i => i
--   | Sum.inl e => nomatch e)) /[⌜ψ⌝])

axiom diagonal_lemma
  (φ : BoundedFormula ℒₜ ℕ 0) :
  ∃ (ψ : Formula ℒₜ ℕ),
    syntax_and_PA_unres_TB ⊢
      (ψ ⇔ (φ////[⌜ψ⌝]))

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
  let eqv_trans_derivation
    (Th : Set (Formula L ℕ)) (A B C : Formula L ℕ) (h₁ : C = A ∨ C = ∼((A ⟹ B) ⟹ ∼(B ⟹ A)) ∨ C = ∼((C ⟹ B) ⟹ ∼(B ⟹ C))) (h₂ : A = C ∨ A = ∼((A ⟹ B) ⟹ ∼(B ⟹ A)) ∨ A = ∼((C ⟹ B) ⟹ ∼(B ⟹ C))) :
    Derivation Th {A ⇔ B, C ⇔ B} {A ⇔ C} := by
    dsimp [FirstOrder.Language.BoundedFormula.iff]
    dsimp [instMin]
    apply Derivation.right_conjunction (A ⟹ C) (C ⟹ A) {A ⟹ C} {C ⟹ A} ∅
    apply Derivation.right_implication A C {A, (A ⟹ B) ⊓ (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {C} ∅
    apply Derivation.lax
    simp
    dsimp [instMin]
    exact h₁
    dsimp [instMin]
    rw [Finset.insert_eq]
    rw [Finset.empty_union]
    rw [Finset.empty_union]
    rw [Finset.empty_union]
    apply Derivation.right_implication C A {C, (A ⟹ B) ⊓ (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {A} ∅
    apply Derivation.lax
    simp
    dsimp [instMin]
    exact h₂
    dsimp[instMin]
    rw [Finset.insert_eq]
    rw [Finset.empty_union]
    rw [Finset.empty_union]
    rw [Finset.empty_union]
    rw [Finset.empty_union]
    dsimp [land]
  intro Th A B C
  apply eqv_trans_derivation at Th
  apply Th at A
  apply A at B
  apply B at C
  apply Nonempty.intro
  sorry

lemma inconsistency : ∀Th : Set (Formula L ℕ), ∀(A : L.Formula ℕ), Nonempty (Derivation Th {A ⇔ ∼A} {⊥}) := by
  let inconsistency_derivation
    (Th : Set (Formula L ℕ)) (A : Formula L ℕ) (h₁ : ⊥ ∉ {A}) (h₂ : ∼A ∉ {A}) (h₃ : ⊥ ≠ A) (h₄ : A ⟹ ∼A ∈ {A ⟹ ∼A, ∼A ⟹ A}) (h₅ : ∼A ⟹ A ∈ {A ⟹ ∼A, ∼A ⟹ A}) (h₆ : A ⟹ ∼A ≠ ∼A ⟹ A):
    Derivation Th {A ⇔ ∼A} {⊥} := by
    dsimp [FirstOrder.Language.BoundedFormula.iff]
    apply Derivation.left_conjunction (A ⟹ ∼A) (∼A ⟹ A) {(A ⟹ ∼A), (∼A ⟹ A)}
    apply Derivation.left_implication A ∼A {(∼A ⟹ A)} {⊥, A} {∼A, (∼A ⟹ A)}
    apply Derivation.left_implication ∼A A ∅ {⊥, A, ∼A} {A}
    apply Derivation.right_negation A {A} {⊥, A}
    apply Derivation.lax
    simp
    rw [Finset.sdiff_self]
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    rw [Finset.union_assoc]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    rw [Finset.union_assoc]
    apply Derivation.lax
    simp
    rw [Finset.union_empty]
    rw [Finset.empty_union]
    rw [Finset.insert_eq]
    apply Derivation.left_implication ∼A A {∼A} {⊥, ∼A} {A, ∼A}
    apply Derivation.right_negation A {∼A, A} {⊥}
    apply Derivation.left_negation A {A} {⊥, A}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    rw [Finset.insert_sdiff_cancel]
    exact h₁
    rw [Finset.insert_sdiff_cancel]
    exact h₂
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    apply Derivation.left_negation A {A} {⊥, A}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.insert_sdiff_cancel]
    rw [Finset.not_mem_singleton]
    exact h₃
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    exact h₄
    exact h₅
    rw [Finset.insert_eq]
    rw [Finset.union_sdiff_cancel_left]
    rw [Finset.sdiff_self]
    rw [Finset.empty_union]
    dsimp [land, instMin]
    rw [Finset.disjoint_singleton]
    exact h₆
  intro Th A
  apply inconsistency_derivation at Th
  apply Th at A
  apply Nonempty.intro
  sorry

def false_formula : Formula ℒₜ ℕ := ⊥
theorem tarskis_theorem : syntax_and_PA_unres_TB ⊢ false_formula := by
  -- Step 1: Get the liar formula using the diagonal lemma
  have liar_formula_exists :
    ∃ (ψ : Formula ℒₜ ℕ),
      syntax_and_PA_unres_TB ⊢ (ψ ⇔ ∼T(⌜ψ⌝)) := by
  -- --     -- apply Exists.elim
  -- --     -- let φ : (BoundedFormula.not BoundedFormula.rel Rel.t ![(&0)])
  -- --     -- apply diagonal_lemma φ
  -- --     -- sorry
      let φ : BoundedFormula ℒₜ ℕ 0 := ∼T(var (Sum.inl 0))
      -- have step1 : {t : ℒₜ.Term (ℕ ⊕ Fin 0)} → φ////[t] = ∼T(t)
      --   | .var v => match v with
      --   | _ => sorry

      -- have step2 {ψ : Formula ℒₜ ℕ} : (φ////[⌜ψ⌝]) = ∼T(⌜ψ⌝) := by
      --   simp[φ, my_subst]
      --   sorry

      -- apply diagonal_lemma φ
  --     -- use ψ
  --     -- rw [th_to_set_form]
  -- -- rw [this] at hψ
  -- -- use ψ
  -- -- exact hψ
      sorry
  obtain ⟨ψ⟩ := liar_formula_exists
  -- have liar_formula_exists :
  --   ∃ (ψ : Formula ℒₜ ℕ),
  --     syntax_and_PA_unres_TB ⊢ (ψ ⇔ (∼T(var (Sum.inl 0)))////[⌜ψ⌝]) := by
  --   apply diagonal_lemma ∼T(var (Sum.inl 0))

  have liar_t_instance : syntax_and_PA_unres_TB ⊢ (T(⌜ψ⌝) ⇔ ψ) := by
    simp
    apply
  -- Step 3: Derive T(⌜ψ⌝) ⇔ ∼T(⌜ψ⌝)
  have intermediate_lemma : syntax_and_PA_unres_TB ⊢ (T(⌜ψ⌝) ⇔ ∼T(⌜ψ⌝)) := by
      obtain ⟨derivation⟩ := eqv_trans syntax_and_PA_unres_TB (T(⌜ψ⌝)) (∼T(⌜ψ⌝)) ψ
      sorry
  sorry
  sorry


  lemma test {t t' : ℒ.Term (ℕ ⊕ Fin 0)} : ((var (Sum.inl 0) =' t)////[t']) = (t' =' t):= by
    #check ((var (Sum.inl 0) =' t)////[t'])
    #check t' =' t



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
