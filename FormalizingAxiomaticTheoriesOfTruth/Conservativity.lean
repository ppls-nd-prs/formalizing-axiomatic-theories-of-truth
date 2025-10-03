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
  @[simp]
  noncomputable def get_disq_φs {φ : ℒₜ.Formula α} : (p : @Proof α ℒₜ Th s φ) → List (ℒ.Sentence)
  | .ax φ h => if h : ∃ψ, φ = (TB.tarski_biconditional ψ).to_alpha then [h.choose] else []
  | .un p _ h₁ => get_disq_φs p
  | .bi p₁ p₂ _ h₁ => (get_disq_φs p₁) ∪ (get_disq_φs p₂)

  variable [Encodable (ℒₜ.Formula (Fin 1))]
  @[simp]
  def make_tau_equivs (s : ℒ.Sentence) : ℒ.Formula (Fin 1) := #0 =' ⌜s⌝ ⊓ s

  open Proof
  noncomputable def tau {φ : ℒₜ.Formula α} : Proof Th s φ → ℒ.Formula (Fin 1) :=
    fun p => Formula.iSup ((get_disq_φs p).map make_tau_equivs).get

end Conservativity

  variable {M : Type w} [ℒ.Structure M]
  lemma num_all_v : ∀{n}, ∀{α : Type}, ∀{β : Type}, ∀v : α → ↑M, ∀z : β → ↑M, @Term.realize ℒ _ _ _ v (numeral n) = @Term.realize ℒ _ _ _ z (numeral n) := by
    intro n α β v z
    induction n with
    | zero =>
      simp[Matrix.empty_eq]
    | succ n ih =>
      unfold numeral
      simp
      rw[ih]

  namespace Conservativity
  open L_T ProofSystem
  variable {L : Language}{Th : ℒₜ.Theory}{α : Type}[Inhabited α]{n : Nat}[Encodable ℒ.Sentence][Encodable (ℒ.Formula (Fin 1))][Encodable (ℒₜ.Formula (Fin 1))][BEq (ℒₜ.BoundedFormula (Fin 1) 0)]{s : @ProofSystem α ℒₜ}

  lemma all_disq_phis_tau_makes_true {complete : s.Complete}{sound : s.Sound} : (ψ : ℒₜ.Formula α) → ∀p : Proof Th s ψ, ∀φ ∈ get_disq_φs p, (@Theory.ModelsBoundedFormula _ {} (Empty) _ ((tau p).subst ![⌜φ⌝])) ↔ {} ⊨ᵇ φ := by
    intro ψ p φ h₁
    apply Iff.intro
    -- mp
    unfold Theory.ModelsBoundedFormula
    intro h₂
    intro M v xs


    sorry
    --mpr
    intro h₂
    intro M v xs
    apply realize_subst.mpr; apply realize_iSup.mpr
    have ext : ∃ n, (get_disq_φs p).get n = φ := by
      apply List.mem_iff_get.mp h₁
    let n : Fin (get_disq_φs p).length := ext.choose
    let m : Fin ((get_disq_φs p).map make_tau_equivs).length := by
      rw[List.length_map]
      exact n
    apply Exists.intro m

    rw[List.get_eq_getElem]
    rw[List.getElem_map]

    have m_val_eq_n_val : @Fin.val (List.map make_tau_equivs (get_disq_φs p)).length m = @Fin.val (get_disq_φs p).length n := by
      simp[m,Fin.cast_eq_cast']
    simp only [m_val_eq_n_val]
    have is_phi : (get_disq_φs p)[(Fin.val n)] = φ := by
      apply ext.choose_spec
    rw[is_phi]
    apply BoundedFormula.realize_inf.mpr
    apply And.intro
    -- left
    #check (BoundedFormula.realize_bdEqual _ _).mpr
    apply (BoundedFormula.realize_bdEqual _ _).mpr
    simp
    rw[num_all_v ((Sum.elim (fun a ↦ Term.realize v ⌜φ⌝) xs)) v]
    --right
    simp
    exact h₂ _ (Sum.elim (fun a ↦ Term.realize v ⌜φ⌝) xs ∘ fun x ↦ Sum.inl 0) _

  variable {L : Language}
  @[simp]
  def bdEqual_iff {t₁ t₂ : L.Term (α ⊕ Fin n)} : t₁ =' t₂ = .equal t₁ t₂ := Eq.refl (t₁ =' t₂)

  def Conservative {α : Type} (Th₁ : ℒₜ.Theory) (Th₂ : ℒ.Theory) : Prop :=
    ∀φ : ℒ.Formula α, (Th₁ ⊨ᵇ (ϕ.onFormula φ)) → (Th₂ ⊨ᵇ φ)

end Conservativity
