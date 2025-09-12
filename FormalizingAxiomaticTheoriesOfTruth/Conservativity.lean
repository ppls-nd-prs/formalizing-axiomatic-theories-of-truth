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
  noncomputable def get_disq_φs {φ : ℒₜ.Formula α} : (p : @Proof α ℒₜ Th s φ) → List (ℒₜ.Formula (Fin 1))
  | .ax φ h => if h : ∃ψ, φ = (TB.tarski_biconditional ψ).to_alpha then [h.choose] else []
  | .un p _ h₁ => get_disq_φs p
  | .bi p₁ p₂ _ h₁ => (get_disq_φs p₁) ∪ (get_disq_φs p₂)

  def make_vec : (l : List (α)) → (Fin l.length → α)
  | .nil => ![]
  | .cons a l => Fin.append (make_vec l) ![a]

  #check ![1,2,4]
  #eval Fin.append ![1,2,3] ![1,2,3]
  -- instance : ∀Th : ℒₜ.Theory, ∀s : @ProofSystem α ℒₜ, ∀φ, ∀p : Proof Th s φ, Finite (Fin p.nr_axioms) := by
  --   intro Th s φ p
  --   apply @Finite.intro _ p.nr_axioms
  --   rfl
  -- variable [∀Th: L.Theory, ∀s : @ProofSystem α L, ∀φ, ∀p : Proof Th s φ, Finite (Fin p.nr_axioms)]
  open Proof
  noncomputable def tau {φ : ℒₜ.Formula α} : Proof Th s φ → ℒₜ.Formula (Fin 1) :=
    fun p => Formula.iSup (make_vec (get_disq_φs p))
end Conservativity
  variable {L : Language}{n : Nat}{α : Type}

  namespace Conservativity
  open L_T ProofSystem
  variable {L : Language}{Th : ℒₜ.Theory}{α : Type}[Inhabited α]{n : Nat}[Encodable ℒ.Sentence][Encodable (ℒₜ.Formula (Fin 1))]{s : @ProofSystem α ℒₜ}
  lemma all_disq_phis_tau_makes_true {complete : s.Complete}{sound : s.Sound} : (ψ : ℒₜ.Formula α) → ∀p : Proof Th s ψ, ∀φ ∈ get_disq_φs p, (@Theory.ModelsBoundedFormula _ {} (Fin 1) _ ((tau p).subst ![⌜φ⌝])) ↔ {} ⊨ᵇ φ := by
    intro ψ p φ h₁
    apply Iff.intro
    -- mp
    intro h₂
    unfold ProofSystem.Complete at complete
    unfold Theory.ModelsBoundedFormula at h₂
    simp[tau,make_vec,get_disq_φs] at h₂
    unfold Theory.ModelsBoundedFormula
    intro M v xs
    apply h₂ M at v
    cases φ with
    | all φ =>
      simp
      intro a

      sorry
    | _ => sorry

    --mpr
    cases φ with
    | all φ =>
      intro h₁
      unfold Theory.ModelsBoundedFormula at h₁
      unfold Theory.ModelsBoundedFormula
      intro M v xs
      apply h₁ M v at xs
      unfold tau
      simp

      sorry
    | _ => sorry

  variable {L : Language}
  @[simp]
  def bdEqual_iff {t₁ t₂ : L.Term (α ⊕ Fin n)} : t₁ =' t₂ = .equal t₁ t₂ := Eq.refl (t₁ =' t₂)

  def Conservative {α : Type} (Th₁ : ℒₜ.Theory) (Th₂ : ℒ.Theory) : Prop :=
    ∀φ : ℒ.Formula α, (Th₁ ⊨ᵇ (ϕ.onFormula φ)) → (Th₂ ⊨ᵇ φ)

end Conservativity
