import FormalizingAxiomaticTheoriesOfTruth.ProofTheory
import FormalizingAxiomaticTheoriesOfTruth.BasicTheories
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

def syntax_and_PA_unres_TB : ℒₜ.Theory :=
  𝐏𝐀 ∪ unrestricted_TB

-- axiom diagonal_lemma (φ : BoundedFormula ℒₜ Empty 1) :
--     ∃ (ψ : Formula ℒₜ ℕ),
--     syntax_and_PA_unres_TB ⊢ (ψ ⇔ (φ.toFormula.relabel (fun x => match x with
--   | Sum.inr i => i
--   | Sum.inl e => nomatch e)) /[⌜ψ⌝])
end LiarParadox

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

open LiarParadox
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

lemma eqv_trans : ∀Th : L.Theory, ∀(A B C : L.Formula ℕ), Nonempty (Derivation Th {A ⇔ B, C ⇔ B} {A ⇔ C}) := by
  let eqv_trans_derivation
    (Th : L.Theory) (A B C : Formula L ℕ) :
    Derivation Th {A ⇔ B, C ⇔ B} {A ⇔ C} := by
    dsimp [FirstOrder.Language.BoundedFormula.iff]
    dsimp [instMin]
    apply Derivation.right_conjunction (A ⟹ C) (C ⟹ A) {A ⟹ C} {C ⟹ A} ∅
    apply Derivation.right_implication A C {A, (A ⟹ B) ⊓ (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {C} ∅
    apply Derivation.left_conjunction (A ⟹ B) (B ⟹ A) {A, (A ⟹ B), (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {A, (C ⟹ B) ⊓ (B ⟹ C)}
    apply Derivation.left_conjunction (C ⟹ B) (B ⟹ C) {A, (A ⟹ B), (B ⟹ A), (C ⟹ B), (B ⟹ C)} {A, A ⟹ B, B ⟹ A}
    apply Calculus.cut B {A, (A ⟹ B)} ∅ {(B ⟹ A), (C ⟹ B), (B ⟹ C)} {C}
    apply mp_derivation
    rw [← Finset.insert_eq]
    apply Derivation.left_implication B C {B, (B ⟹ A), (C ⟹ B)} {C, B} {C, B, (B ⟹ A), (C ⟹ B)}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [Finset.empty_union]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    dsimp [instMin]
    dsimp [land]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [Finset.union_right_comm]
    dsimp [instMin]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [Finset.union_right_comm]
    dsimp [instMin]
    dsimp [land]
    rw [← Finset.union_assoc]
    rw [← Finset.insert_eq]
    dsimp [instMin]
    rw [Finset.empty_union]
    rw [Finset.empty_union]
    rw [Finset.empty_union]
    apply Derivation.right_implication C A {C, (A ⟹ B) ⊓ (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {A} ∅
    apply Derivation.left_conjunction (A ⟹ B) (B ⟹ A) {C, (A ⟹ B), (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {C, (C ⟹ B) ⊓ (B ⟹ C)}
    apply Derivation.left_conjunction (C ⟹ B) (B ⟹ C) {C, (C ⟹ B), (A ⟹ B), (B ⟹ A),  (B ⟹ C)} {C, A ⟹ B, B ⟹ A}
    apply Calculus.cut B {C, (C ⟹ B)} ∅ {(A ⟹ B), (B ⟹ A), (B ⟹ C)} {A}
    apply mp_derivation
    rw [← Finset.insert_eq]
    apply Derivation.left_implication B A {B, (A ⟹ B), (B ⟹ C)} {A, B} {A, B, (A ⟹ B), (B ⟹ C)}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.union_right_comm]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [Finset.empty_union]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [Finset.union_right_comm]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.union_right_comm]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    dsimp [instMin]
    dsimp [land]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.union_comm]
    rw [Finset.union_left_comm]
    rw [Finset.union_comm]
    rw [Finset.union_left_comm]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.union_right_comm]
    rw [Finset.union_assoc]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [Finset.union_right_comm]
    dsimp [instMin]
    dsimp [land]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    dsimp [instMin]
    simp
    simp
    simp
    simp
    dsimp [land]
  intro Th A B C
  apply eqv_trans_derivation at Th
  apply Th at A
  apply A at B
  apply B at C
  apply Nonempty.intro C

lemma inconsistency : ∀Th : L.Theory, ∀(A : L.Formula ℕ), Nonempty (Derivation Th {A ⇔ ∼A} {⊥}) := by
  let inconsistency_derivation
    (Th : L.Theory) (A : Formula L ℕ) :
    Derivation Th {A ⇔ ∼A} {⊥} := by
    dsimp [FirstOrder.Language.BoundedFormula.iff]
    apply Derivation.left_conjunction (A ⟹ ∼A) (∼A ⟹ A) {(A ⟹ ∼A), (∼A ⟹ A)} {}
    apply Derivation.left_implication ∼A A {(A ⟹ ∼A)} {⊥, ∼A} {A, (A ⟹ ∼A)}
    apply Calculus.right_negation A {(A ⟹ ∼A), A} {⊥}
    apply Derivation.left_implication A ∼A {A} {A, ⊥} {∼A, A}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    apply Calculus.left_negation A {A} {A, ⊥}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    apply Derivation.left_implication A ∼A {A} {A, ⊥} {∼A, A}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    apply Calculus.left_negation A {A} {A, ⊥}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    simp
    simp
    dsimp [instMin]
    dsimp [land]
  intro Th A
  apply inconsistency_derivation at Th
  apply Th at A
  apply Nonempty.intro A

-- lemma inconsistency : ∀Th : Set (Formula L ℕ), ∀(A : L.Formula ℕ), Nonempty (Derivation Th {A ⇔ ∼A} {⊥}) := by
--   let inconsistency_derivation
--     (Th : Set (Formula L ℕ)) (A : Formula L ℕ) (h₂ : ∼A ≠ A) (h₃ : ⊥ ≠ A) (h₆ : A ⟹ ∼A ≠ ∼A ⟹ A):
--     Derivation Th {A ⇔ ∼A} {⊥} := by
--     dsimp [FirstOrder.Language.BoundedFormula.iff]
--     apply Derivation.left_conjunction (A ⟹ ∼A) (∼A ⟹ A) {(A ⟹ ∼A), (∼A ⟹ A)}
--     apply Derivation.left_implication A ∼A {(∼A ⟹ A)} {⊥, A} {∼A, (∼A ⟹ A)}
--     apply Derivation.left_implication ∼A A ∅ {⊥, A, ∼A} {A}
--     apply Derivation.right_negation A {A} {⊥, A}
--     apply Derivation.lax
--     simp
--     rw [Finset.sdiff_self]
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.union_assoc]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.union_assoc]
--     apply Derivation.lax
--     simp
--     rw [Finset.union_empty]
--     rw [Finset.empty_union]
--     rw [Finset.insert_eq]
--     apply Derivation.left_implication ∼A A {∼A} {⊥, ∼A} {A, ∼A}
--     apply Derivation.right_negation A {∼A, A} {⊥}
--     apply Derivation.left_negation A {A} {⊥, A}
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.insert_sdiff_cancel]
--     rw [Finset.not_mem_singleton]
--     sorry
--     rw [Finset.insert_sdiff_cancel]
--     rw [Finset.not_mem_singleton]
--     have h : ∼A ≠ A := by
--       sorry
--     exact h
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     apply Derivation.left_negation A {A} {⊥, A}
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     rw [Finset.insert_sdiff_cancel]
--     rw [Finset.not_mem_singleton]
--     sorry
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.mem_insert]
--     simp
--     rw [Finset.mem_insert]
--     simp
--     rw [Finset.insert_eq]
--     rw [Finset.union_sdiff_cancel_left]
--     rw [Finset.sdiff_self]
--     rw [Finset.empty_union]
--     dsimp [land, instMin]
--     rw [Finset.disjoint_singleton]
--     sorry
--   intro Th A
--   apply inconsistency_derivation at Th
--   apply Th at A
--   apply Nonempty.intro
--   sorry


def false_formula : Formula ℒₜ ℕ := ⊥
theorem tarskis_theorem : syntax_and_PA_unres_TB ⊢ false_formula := by
  have liar_formula_exists :
    ∃ (ψ1 : ℒₜ.Sentence),
      𝐓𝐁 ⊢ (ψ1 ⇔ ∼T(⌜ψ1⌝)) := by
  -- --     -- apply Exists.elim
  -- --     -- let φ : (BoundedFormula.not BoundedFormula.rel Rel.t ![(&0)])
  -- --     -- apply diagonal_lemma φ
  -- --     -- sorry
      let φ : BoundedFormula ℒₜ (Fin 1) 0 := ∼T(#0)

      have step1: ∀ψ : ℒₜ.Sentence, φ/[⌜ψ⌝] = ∼T(⌜ψ⌝)  := by

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
