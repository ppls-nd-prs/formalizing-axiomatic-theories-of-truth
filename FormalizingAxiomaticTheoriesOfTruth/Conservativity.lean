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
      -- | .var_symbol =>
      --        .rel .var_symbol (fun i => ts i)
      -- | .const_symbol =>
      --        .rel .const_symbol (fun i => ts i)
      -- | .term_symbol =>
      --        .rel .term_symbol (fun i => ts i)
      -- | .clterm_symbol =>
      --        .rel .clterm_symbol (fun i => ts i)
      -- | .forml_symbol =>
      --        .rel .forml_symbol (fun i => ts i)
      -- | .sentencel_symbol =>
      --        .rel .sentencel_symbol (fun i => ts i)
      -- | .formlt_symbol =>
      --        .rel .formlt_symbol (fun i => ts i)
      -- | .sentencelt_symbol =>
      --        .rel .sentencelt_symbol (fun i => ts i)
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
  | .ax φ h₁ => if th : ∃ψ, φ = (TB.tarski_biconditional ψ).to_alpha
    then
    [th.choose]
    else
    []
  | .un p _ h₁ => get_disq_φs p
  | .bi p₁ p₂ _ h₁ => (get_disq_φs p₁) ∪ (get_disq_φs p₂)

  variable [Encodable (ℒₜ.Formula (Fin 1))]
  @[simp]
  def make_tau_equivs (s : ℒ.Sentence) : ℒ.Formula (Fin 1) := #0 =' ⌜s⌝ ⊓ s

  open Proof
  @[simp]
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
  variable {L : Language}{Th : ℒₜ.Theory}{α : Type}{n : Nat}[Encodable ℒ.Sentence]{s : @ProofSystem α ℒₜ}

  variable {M β γ δ: Type}{n : Nat}[ℒ.Structure M]{t : β → ↑M}{v : (β ⊕ δ) → ↑M}[Encodable (ℒ.BoundedFormula γ n)]

  lemma lem1 : ∀{φ: ℒ.Sentence}, Term.realize v (⌜φ⌝ : ℒ.Term _) = Term.realize (default : (Empty ⊕ Fin 0) → ↑M) (⌜φ⌝ : ℒ.Term _) := by
    intro φ
    induction (Encodable.encode φ) with
    | zero =>
      simp[Matrix.empty_eq]
    | succ n ih =>
      simp[ih]

  lemma lem2 {v : γ → ↑M} : ∀{φ: ℒ.Sentence}, Term.realize v (⌜φ⌝ : ℒ.Term _) = Term.realize (default : (Empty ⊕ Fin 0) → ↑M) (⌜φ⌝ : ℒ.Term _) := by
    intro φ
    induction (Encodable.encode φ) with
    | zero =>
      simp[Matrix.empty_eq]
    | succ n ih =>
      simp[ih]

  lemma tau_equivalence : (ψ : ℒₜ.Formula α) → ∀p : Proof Th s ψ, ∀φ ∈ get_disq_φs p, 𝐏𝐀 ⊨ᵇ ((tau p).subst ![⌜φ⌝] ⇔ φ) := by
    intro ψ p φ h₁
    apply Theory.models_sentence_iff.mpr
    intro M
    apply realize_iff.mpr
    apply Iff.intro
    -- mp
    intro h₂
    have realizable : ↑M ⊨ subst (tau p) ![⌜φ⌝] := by
      exact h₂
    unfold Sentence.Realize Formula.Realize at realizable
    apply realize_subst.mp at realizable
    apply realize_iSup.mp at realizable
    have ext₁ : ∃n, (get_disq_φs p).get n = φ := by
      apply List.mem_iff_get.mp
      exact h₁
    let realization : Realize ((List.map make_tau_equivs (get_disq_φs p)).get realizable.choose) (fun a ↦ @Term.realize ℒ M _ _ (@default (Empty → ↑M) _) (![⌜φ⌝] a)) default := by
      exact realizable.choose_spec

    rw[List.get_eq_getElem] at realization
    rw[List.getElem_map] at realization

    if h₄ : (get_disq_φs p)[Fin.val realizable.choose] = φ then
      rw[h₄] at realization
      simp at realization
      apply And.right at realization
      rw[Unique.default_eq]
      rw[Unique.default_eq]
      exact realization

    else
      simp only [make_tau_equivs,realize_inf] at realization
      apply And.left at realization

      simp at realization

      -- iets met injectief (bewezen in syntax voor ℒ)
      -- de sleutel is dat de realization moet kloppen in elke M,
      -- dus ook in die waar het de interpretatie van getallen krijgt
      -- we moeten bewijzen dat Nat een ∅.ModelType is

      simp[Matrix.empty_eq,Matrix.vec_single_eq_const] at realization

      have step1 : ↑M ⊨ (∼(⌜(get_disq_φs p)[↑realizable.choose]⌝ =' ⌜φ⌝) : ℒ.Sentence) := by
        apply PA.all_fs
        exact h₄

      apply realize_not.mp at step1
      simp[realize_bdEqual _ _] at step1
      -- we hebben hier peano_arithmetic regels nodig
      rw[lem1] at realization
      simp[lem2] at realization
      rw[lem1] at step1
      simp[lem2] at step1
      symm at realization
      apply step1 at realization
      contradiction

    --mpr
    intro h₂
    apply realize_subst.mpr; apply realize_iSup.mpr
    have ext : ∃ n, (get_disq_φs p).get n = φ := by
      apply List.mem_iff_get.mp h₁

    let n : Fin (get_disq_φs p).length := ext.choose
    let m : Fin ((get_disq_φs p).map make_tau_equivs).length := by
      rw[List.length_map]
      exact n

    apply Exists.intro m; rw[List.get_eq_getElem]; rw[List.getElem_map]

    have m_val_eq_n_val : @Fin.val (List.map make_tau_equivs (get_disq_φs p)).length m = @Fin.val (get_disq_φs p).length n := by
      simp[m,Fin.cast_eq_cast']
    simp only [m_val_eq_n_val]
    have is_phi : (get_disq_φs p)[(Fin.val n)] = φ := by
      apply ext.choose_spec
    rw[is_phi]; apply BoundedFormula.realize_inf.mpr; apply And.intro

    -- left
    apply (realize_bdEqual _ _).mpr; simp
    rw[num_all_v ((Sum.elim (fun a ↦ Term.realize _ ⌜φ⌝) _)) _]
    --right
    simp
    rw[Unique.default_eq ((Sum.elim (fun a ↦ Term.realize default (⌜φ⌝: ℒ.Term Empty)) (default: Fin 0 → ↑M) ∘ fun x ↦ Sum.inl 0))] at h₂
    exact h₂

  variable {L : Language}
  @[simp]
  def bdEqual_iff {t₁ t₂ : L.Term (α ⊕ Fin n)} : t₁ =' t₂ = .equal t₁ t₂ := Eq.refl (t₁ =' t₂)

  def Conservative {α : Type} (Th₁ : ℒₜ.Theory) (Th₂ : ℒ.Theory) : Prop :=
    ∀φ : ℒ.Formula α, (Th₁ ⊨ᵇ (ϕ.onFormula φ)) → (Th₂ ⊨ᵇ φ)

end Conservativity
