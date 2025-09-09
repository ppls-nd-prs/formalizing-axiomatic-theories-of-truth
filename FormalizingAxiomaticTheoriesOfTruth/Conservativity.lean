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
  variable {α : Type}{n : Nat}
  @[simp]
  def subs_t : {n : ℕ} →  ({m : Nat} → {β : Type} → ℒ.Term (β ⊕ Fin m) → ℒ.BoundedFormula β m) → ℒₜ.BoundedFormula α n → ℒ.BoundedFormula α n
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

  open BoundedFormula Classical
  variable {L : Language}{m : Nat}
  instance : Coe (ℒ.Sentence) (ℒ.BoundedFormula (Fin 1) n) where
  coe := relabel (fun _ => (.inl 0))

  variable {Th : ℒₜ.Theory}{s : @ProofSystem α ℒₜ}[Encodable ℒ.Sentence]
  noncomputable def get_disq_φs {φ : ℒₜ.Formula α} : Proof Th s φ → List (ℒ.BoundedFormula (Fin 1) n)
  | .ax φ h => if h : ∃ψ, φ = (TB.tarski_biconditional ψ) then {Coe.coe h.choose} else {}
  | .un p _ h₁ => get_disq_φs p
  | .bi p₁ p₂ _ h₁ => get_disq_φs p₁ ∪ get_disq_φs p₂

  def list_to_bf : List (ℒ.Formula (Fin 1)) → ℒ.Formula (Fin 1)
  | .nil => ⊥
  | .cons a lst => a ⊔ list_to_bf lst

  noncomputable def tau {φ : ℒₜ.Formula α} : Proof Th s φ → ℒ.Formula (Fin 1) :=
    fun p => list_to_bf (get_disq_φs p)

  variable {L : Language}
  @[simp]
  def bdEqual_iff {t₁ t₂ : L.Term (α ⊕ Fin n)} : t₁ =' t₂ = .equal t₁ t₂ := Eq.refl (t₁ =' t₂)

  def Conservative {α : Type} (Th₁ : ℒₜ.Theory) (Th₂ : ℒ.Theory) : Prop :=
    ∀φ : ℒ.Formula α, (Th₁ ⊨ᵇ (ϕ.onFormula φ)) → (Th₂ ⊨ᵇ φ)

end Conservativity
