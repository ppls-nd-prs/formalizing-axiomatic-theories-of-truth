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
  variable {L : Language}{Th : ℒₜ.Theory}{α : Type}[Inhabited α]{n : Nat}[Encodable ℒ.Sentence][Encodable (ℒ.Formula (Fin 1))][Encodable (ℒₜ.Formula (Fin 1))][BEq (ℒₜ.BoundedFormula (Fin 1) 0)]{s : @ProofSystem α ℒₜ}

  lemma all_disq_phis_tau_makes_true_mpr {complete : s.Complete}{sound : s.Sound} : (ψ : ℒₜ.Formula α) → ∀p : Proof Th s ψ, ∀φ ∈ get_disq_φs p, {} ⊨ᵇ φ → (@Theory.ModelsBoundedFormula _ {} (Empty) _ ((tau p).subst ![⌜φ⌝])) := by
    intro ψ p φ h₁
    intro h₂ M v xs
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
    apply (BoundedFormula.realize_bdEqual _ _).mpr; simp
    rw[num_all_v ((Sum.elim (fun a ↦ Term.realize v ⌜φ⌝) xs)) v]
    --right
    simp; exact h₂ _ (Sum.elim (fun a ↦ Term.realize v ⌜φ⌝) xs ∘ fun x ↦ Sum.inl 0) _

  def funInterpret : ℒ.Functions n → (Fin n → Nat) → Nat
  | .zero_symbol, _ => 0
  | .succ_symbol, ts => (ts 0).succ
  | .add_symbol, ts => (ts 0) + (ts 1)
  | .mult_symbol, ts => (ts 0) * (ts 1)

  def RelInterpret : ℒ.Relations n → (Fin n → Nat) → Prop := by
  intro a
  cases a

  instance interpret : ℒ.Structure Nat where
  funMap := funInterpret
  RelMap := RelInterpret

  def nat_modeltype : (∅: ℒ.Theory).ModelType where
  Carrier := Nat

  def term_encoding_inj {φ ψ : ℒ.Sentence} : ⌜φ⌝ = (⌜ψ⌝ : ℒ.Term Empty) → φ = ψ := by
    intro h
    apply Encodable.encode_injective
    apply num_inj
    exact h

  lemma all_disq_phis_tau_makes_true {complete : s.Complete}{sound : s.Sound} : (ψ : ℒₜ.Formula α) → ∀p : Proof Th s ψ, ∀φ ∈ get_disq_φs p, (@Theory.ModelsBoundedFormula _ {} (Empty) _ ((tau p).subst ![⌜φ⌝])) ↔ {} ⊨ᵇ φ := by
    intro ψ p φ h₁
    apply Iff.intro
    -- mp
    intro h₂
    apply Theory.models_sentence_iff.mp at h₂
    apply Theory.models_sentence_iff.mpr
    intro M
    have realizable : ↑M ⊨ subst (tau p) ![⌜φ⌝] := by
      exact h₂ M
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
      unfold Sentence.Realize Formula.Realize
      rw[Unique.default_eq]
      rw[Unique.default_eq]
      exact realization

      else
      simp at realization
      apply And.left at realization
      -- iets met injectief (bewezen in syntax voor ℒ)
      -- de sleutel is dat de realization moet kloppen in elke M,
      -- dus ook in die waar het de interpretatie van getallen krijgt
      -- we moeten bewijzen dat Nat een ∅.ModelType is

      have not_eq : ¬⌜(get_disq_φs p)[↑realizable.choose]⌝ = (⌜φ⌝ : ℒ.Term Empty) := by
        intro h
        apply term_encoding_inj at h
        contradiction

      -- we hebben hier peano_arithmetic regels nodig








      sorry

    -- rw[h₄] at realization
    -- simp at realization
    -- apply And.right at realization

    -- sorry
    -- else
    -- sorry







    -- have realizable : (subst (tau p) ![⌜φ⌝]).Realize v xs := by
    --   exact h₂ M v xs

    -- -- simp only [realize_subst] at realizable
    -- -- unfold tau at realizable
    -- -- unfold make_tau_equivs at realizable
    -- induction p with
    -- | ax ψ h₃ =>
    --   if h₄ : ψ = (TB.tarski_biconditional φ).to_alpha then
    --   have exs : ∃ψ_1, ψ = (TB.tarski_biconditional ψ_1).to_alpha := by
    --     apply Exists.intro φ
    --     exact h₄
    --   have exs_true : ∃ψ_1, ψ = (TB.tarski_biconditional ψ_1).to_alpha = True := by
    --     simp[exs]
    --   simp at realizable


    --   sorry
    --   else
    --   sorry
    -- | un p r h₃ ih => sorry
    -- | bi p₁ p₂ h₃ h₄ ih₁ ih₂ => sorry





    --mpr
    intro h₂ M v xs
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
    apply (BoundedFormula.realize_bdEqual _ _).mpr; simp
    rw[num_all_v ((Sum.elim (fun a ↦ Term.realize v ⌜φ⌝) xs)) v]
    --right
    simp; exact h₂ _ (Sum.elim (fun a ↦ Term.realize v ⌜φ⌝) xs ∘ fun x ↦ Sum.inl 0) _

  lemma tau_equiv_provable_pa {complete : s.Complete}{sound : s.Sound} : (ψ : ℒₜ.Formula α) → ∀p : Proof Th s ψ, ∀φ ∈ get_disq_φs p, 𝐏𝐀 ⊨ᵇ ((tau p).subst ![⌜φ⌝]) ⟹ φ := by
    intro ψ p φ h₁
    apply Theory.models_sentence_iff.mpr
    intro M
    apply realize_imp.mpr
    intro tau_realizable
    apply realize_subst.mp at tau_realizable
    apply realize_iSup.mp at tau_realizable
    let b : Fin (List.map make_tau_equivs (get_disq_φs p)).length :=
      tau_realizable.choose
    have tau_realization : Realize ((List.map make_tau_equivs (get_disq_φs p)).get b) (fun a ↦ @Term.realize ℒ M _ _ (@default (Empty → ↑M) _) (![⌜φ⌝] a)) default := by
      exact Exists.choose_spec tau_realizable

    rw[List.get_eq_getElem] at tau_realization
    rw[List.getElem_map] at tau_realization

    by_cases h₄ : (get_disq_φs p)[Fin.val b] = φ
    -- pos
    rw[h₄] at tau_realization
    simp at tau_realization
    rw[Unique.default_eq]; rw[Unique.default_eq]
    exact tau_realization.right
    -- neg
    simp at tau_realization
    apply And.left at tau_realization
    have not_eq : ¬⌜(get_disq_φs p)[↑b]⌝ = (⌜φ⌝ : ℒ.Term Empty) := by
      intro h
      apply term_encoding_inj at h
      contradiction
    have first_ax : 𝐏𝐀 ⊨ᵇ ((∀' ∼(null =' S(&0))) : ℒ.Sentence) := by
      apply Theory.models_sentence_of_mem
      unfold PA.pa
      apply Or.intro_left
      apply PA.peano_axioms.first
    #check first_ax M default default
    /- Het moet nog worden bewezen dat het te bewijzen is in 𝐏𝐀 dat voor twee termen t₁ en t₂ die enkel uit zero_symbol en succ_symbol bestaan en niet gelijk zijn aan elkaar
    hun interpretaties ook niet gelijk zijn aan elkaar.
    Dit lijkt vanzelfsprekend maar is dat niet, want er zijn ook
    termen die geïnterpreteerd mogen worden als hetzelfde ookal
    zijn de termen anders, bijvoorbeeld 3 * 3 en 9 + 0. 𝐏𝐀 dwingt
    echter af dat alle interpretaties van numeralen die ongelijk zijn
    ook ongelijk zijn.
    -/

    sorry

  variable {L : Language}
  @[simp]
  def bdEqual_iff {t₁ t₂ : L.Term (α ⊕ Fin n)} : t₁ =' t₂ = .equal t₁ t₂ := Eq.refl (t₁ =' t₂)

  def Conservative {α : Type} (Th₁ : ℒₜ.Theory) (Th₂ : ℒ.Theory) : Prop :=
    ∀φ : ℒ.Formula α, (Th₁ ⊨ᵇ (ϕ.onFormula φ)) → (Th₂ ⊨ᵇ φ)

end Conservativity
