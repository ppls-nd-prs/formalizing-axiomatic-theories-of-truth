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
  def subs_t {α : Type} : {n : ℕ} →  ({m : Nat} → {β : Type} → (t : ℒ.Term (β ⊕ Fin m)) → ℒₜ.BoundedFormula β m) → ℒₜ.BoundedFormula α n → ℒₜ.BoundedFormula α n
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

  variable {α : Type}{n : Nat}{L : Language}
  @[simp]
  def bdEqual_iff {t₁ t₂ : L.Term (α ⊕ Fin n)} : t₁ =' t₂ = .equal t₁ t₂ := Eq.refl (t₁ =' t₂)

  def Conservative {α : Type} (Th₁ : ℒₜ.Theory) (Th₂ : ℒ.Theory) : Prop :=
    ∀φ : ℒ.Formula α, (Th₁ ⊨ᵇ (ϕ.onFormula φ)) → (Th₂ ⊨ᵇ φ)

    unfold Provable at h₁
    apply Classical.ofNonempty at h₁
    induction h₁ with
    | ax q w =>
      cases w with
      | inl w =>
        apply Nonempty.intro
        apply Proof.ax
        apply Or.intro_left
        exact w
      | inr w =>
        cases w with
        | inl w =>
          cases w with
          | inl w =>
            apply Nonempty.intro
            apply Proof.ax
            apply Or.intro_right
            apply Or.intro_left
            exact w
          | inr w =>
            sorry
        | inr w =>

          sorry
    | un q w e p_ih =>
      apply Nonempty.intro at q

      sorry
    | bi q w e r => sorry

  open Classical
  open ProofSystem
  theorem conservativity_of_tb {α} {s : @ProofSystem α ℒₜ}{sound : s.Sound}{complete : s.Complete}{n : Nat}: @Conservative α 𝐓𝐁 𝐏𝐀 := by
    simp[Conservative]
    intro φ h
    apply (complete φ 𝐓𝐁) at h
    unfold ProofSystem.Provable at h
    apply @Classical.ofNonempty at h
    apply sound φ 𝐏𝐀
    unfold ProofSystem.Provable
    apply Nonempty.intro
    exact to_pa h

    -- #check sound φ 𝐓𝐁
    -- apply sound φ 𝐓𝐁 at h
    -- simp only [ModelsBoundedFormula]
    -- simp only [ModelsBoundedFormula] at h
    -- intro M
    -- induction φ with
    -- | falsum =>


    --   sorry
    -- | _ => sorry



end Conservativity
