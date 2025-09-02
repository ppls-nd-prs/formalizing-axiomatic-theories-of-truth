import FormalizingAxiomaticTheoriesOfTruth.BasicTheories
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Semantics

open FirstOrder
open Language
open BoundedFormula
open Languages
open LPA
open Induction

namespace Conservativity
  open Languages LPA L_T FirstOrder.Language.BoundedFormula

  @[simp]
  def subs_t {α : Type} : {n : ℕ} →  ({m : Nat} → {β : Type} → ℒ.Term (β ⊕ Fin m) → ℒ.BoundedFormula β m) → ℒₜ.BoundedFormula α n → ℒ.BoundedFormula α n
  | _, _, .falsum  => .falsum
  | _, _, .equal t₁ t₂ => .equal (t₁) (t₂)
  | _, φ, .rel R ts =>
      match R with
      | .t_symbol => (φ (ts 0))
      | .var_symbol =>
             .rel .var_symbol (fun i => ts i)
      | .const_symbol =>
             .rel .const_symbol (fun i => ts i)
      | .term_symbol =>
             .rel .term_symbol (fun i => ts i)
      | .clterm_symbol =>
             .rel .clterm_symbol (fun i => ts i)
      | .forml_symbol =>
             .rel .forml_symbol (fun i => ts i)
      | .sentencel_symbol =>
             .rel .sentencel_symbol (fun i => ts i)
      | .formlt_symbol =>
             .rel .formlt_symbol (fun i => ts i)
      | .sentencelt_symbol =>
             .rel .sentencelt_symbol (fun i => ts i)
  | _, φ, .imp ψ π => .imp (subs_t φ ψ) (subs_t φ π)
  | _, φ, .all ψ => .all (subs_t φ ψ)

  notation φ"/ₜ["ψ"]" => subs_t ψ φ

  def empty : Set (ℒₜ.Formula ℕ) := ∅
  lemma empty_replacement : ∀φ : ({n : Nat} → {α : Type} → ℒ.Term (α ⊕ Fin n) → ℒ.BoundedFormula α n), (empty.image (subs_t φ)) = ∅ := by
    intro φ
    simp[empty]

  def Conservative {n : Nat} {α : Type} (Th₁ : ℒₜ.Theory) (Th₂ : ℒₜ.Theory) : Prop :=
    ∀φ : ℒ.BoundedFormula α n, (Th₁ ⊨ᵇ (ϕ.onBoundedFormula φ)) → (Th₂ ⊨ᵇ (ϕ.onBoundedFormula φ))

  open Theory
  variable [Encodable ℒ.Sentence]

  variable {M : Type} [ℒₜ.Structure M]
  lemma lem2 : M ⊨ 𝐓𝐁 ↔ M ⊨ 𝐏𝐀 := by
    apply Iff.intro
    -- mp
    intro h
    simp at h
    simp
    intro a h₂
    apply h
    cases h₂ with
    | inl h₂ =>
      apply Or.intro_left
      apply Or.intro_left
      exact h₂
    | inr h₂ =>
      apply Or.intro_left
      apply Or.intro_right
      simp
      simp at h₂
      simp[h₂.choose_spec]
    simp
    --mpr
    intro h₁ φ h₂
    cases h₂ with
    | inl h₂ =>
      cases h₂ with
      | inl h₂ =>
        have step1 : φ ∈ 𝐏𝐀 := by
          apply Or.intro_left
          exact h₂
        apply h₁ at step1
        exact step1
      | inr h₂ =>
        simp at h₂

        sorry
    | inr h₂ => sorry

  theorem conservativity_of_tb {n : Nat} {α : Type}: @Conservative n α 𝐓𝐁 𝐏𝐀 := by
    intro φ h
    simp only [ModelsBoundedFormula]
    simp only [ModelsBoundedFormula] at h
    intro M
    induction φ with
    | falsum =>


      sorry
    | _ => sorry



end Conservativity
