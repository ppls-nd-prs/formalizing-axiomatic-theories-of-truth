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

  open PA Languages
  def pax_unchanged {α : Type} : ∀φ, φ ∈ peano_axioms → ∀{τ}, (@Sentence.to_alpha α _ _ φ)/ₜ[τ] = (Sentence.to_alpha φ) := by
    intro φ h₁ τ
    cases h₁
    trivial
    trivial
    trivial
    trivial
    trivial
    trivial

  variable {α : Type}{n : Nat}{Th : ℒₜ.Theory}{s : @ProofSystem α ℒₜ}

  def Conservative {α : Type} (Th₁ : ℒₜ.Theory) (Th₂ : ℒₜ.Theory) : Prop :=
    ∀φ : ℒ.Formula α, (Th₁ ⊨ᵇ (ϕ.onFormula φ)) → (Th₂ ⊨ᵇ (ϕ.onFormula φ))

  open Theory ProofSystem
  variable {α : Type} {s : @ProofSystem α ℒₜ}[Encodable ℒ.Sentence]
  lemma to_pa {sound : s.Sound}{complete : s.Complete} : ∀ψ : ℒₜ.Formula α, (p : 𝐓𝐁 ⊢(s) ψ) → ∃τ, (𝐏𝐀 ⊢(s) ψ/ₜ[τ]) := by
    intro ψ h₁
    unfold Provable at h₁
    apply Classical.ofNonempty at h₁
    induction h₁ with
    | ax φ h => cases h with
      | inl h =>
        cases h with
        | inl h =>
          apply Exists.intro ⊤
          apply Nonempty.intro
          rw[(pax_unchanged φ h)]
          apply Proof.ax
          apply Or.intro_left
          exact h
        | inr h =>
          apply Exists.intro ⊤
          apply Nonempty.intro
          match φ with
          | .falsum =>
            simp[ind] at h
          | .equal t₁ t₂ =>
            simp[ind] at h
          | .rel r ts =>
            simp[ind] at h
          | .imp f₁ f₂ =>
            simp[ind] at h

            sorry
          | _ => sorry

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
    apply to_pa at h
    apply sound at h
    exact h

end Conservativity
