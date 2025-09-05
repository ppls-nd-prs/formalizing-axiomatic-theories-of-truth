import FormalizingAxiomaticTheoriesOfTruth.BasicTheories
import FormalizingAxiomaticTheoriesOfTruth.ProofTheory
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

  def Conservative {α : Type} (Th₁ : ℒₜ.Theory) (Th₂ : ℒₜ.Theory) : Prop :=
    ∀φ : ℒ.Formula α, (Th₁ ⊨ᵇ (ϕ.onFormula φ)) → (Th₂ ⊨ᵇ (ϕ.onFormula φ))

  open Theory ProofSystem
  variable {α : Type} {s : @ProofSystem α ℒₜ}{φ : ℒ.Formula α}{ψ} {h : ϕ.onFormula φ = ψ}[Encodable ℒ.Sentence]
  lemma to_pa {sound : s.Sound}{complete : s.Complete} : (𝐓𝐁 ⊢(s) ψ) → (𝐏𝐀 ⊢(s) ψ) := by
    intro h₁
    unfold Provable at h₁
    apply Classical.ofNonempty at h₁
    induction h₁ with
    | ax φ h =>
      cases h with
      | inl h =>
        apply Nonempty.intro
        apply Proof.ax
        apply Or.intro_left
        exact h
      | inr h =>
        cases h with
        | inl h =>
          cases h with
          | inl h =>
            apply Nonempty.intro
            apply Proof.ax
            apply Or.intro_right
            apply Or.intro_left
            exact h
          | inr h =>

            sorry
        | inr h =>

          sorry
    | un _ h₁ h₂ p_ih =>
      unfold Provable at p_ih
      apply Classical.ofNonempty at p_ih
      unfold Provable
      apply Nonempty.intro
      apply Proof.un p_ih h₁ h₂
    | bi _ _ h₁ h₂ p_ih₁ p_ih₂ =>
      unfold Provable
      apply Nonempty.intro
      unfold Provable at p_ih₁
      apply Classical.ofNonempty at p_ih₁
      unfold Provable at p_ih₂
      apply Classical.ofNonempty at p_ih₂
      apply Proof.bi p_ih₁ p_ih₂ h₁ h₂

  open Classical
  open ProofSystem
  theorem conservativity_of_tb {α} {s : @ProofSystem α ℒₜ}{sound : s.Sound}{complete : s.Complete}{n : Nat}: @Conservative α 𝐓𝐁 𝐏𝐀 := by
    simp[Conservative]
    intro φ h
    apply complete at h
    apply @to_pa _ _ _ _ sound complete at h
    apply sound at h
    exact h

end Conservativity
