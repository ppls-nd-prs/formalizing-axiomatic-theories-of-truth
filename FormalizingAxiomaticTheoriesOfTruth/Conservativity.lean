import FormalizingAxiomaticTheoriesOfTruth.ProofTheory
import FormalizingAxiomaticTheoriesOfTruth.BasicTheories

open FirstOrder
open Language
open BoundedFormula
open Languages
open LPA
open PA.Induction

namespace Conservativity
  open Languages LPA L_T Calculus FirstOrder.Language.BoundedFormula TermEncoding

    def to_l_func ⦃arity : ℕ⦄ : (ℒₜ.Functions arity) → (ℒ.Functions arity)
    | .null => .null
    | .succ => .succ
    | .add => .add
    | .mult => .mult
    | .neg => .neg
    | .conj => .conj
    | .disj => .disj
    | .cond => .cond
    | .forall => .forall
    | .exists => .exists
    | .denote => .denote
    | .subs => .subs

    def to_l_term {α : Type} : (ℒₜ.Term α) → (ℒ.Term α)
    | .var f => .var f
    | .func f ts => .func (to_l_func f) (fun i => to_l_term (ts i))

  abbrev ℒ.Fml := ℒ.Formula ℕ
  abbrev ℒₜ.Fml := ℒₜ.Formula ℕ

  @[simp]
  def subs_fml_for_t_in_fml : {n : ℕ} →  ℒ.BoundedFormula ℕ n → ℒₜ.BoundedFormula ℕ n → ℒ.BoundedFormula ℕ n
  | _, _, .falsum  => .falsum
  |  _, _, .equal t₁ t₂ => .equal (to_l_term t₁) (to_l_term t₂)
  |  _, φ, .rel R ts =>
      match R with
      | .t => (φ/[(to_l_term (ts 0))])
      | .var =>
             .rel LPA.Rel.var (fun i => to_l_term (ts i))
      | .const =>
             .rel LPA.Rel.const (fun i => to_l_term (ts i))
      | .term =>
             .rel LPA.Rel.term (fun i => to_l_term (ts i))
      | .clterm =>
             .rel LPA.Rel.clterm (fun i => to_l_term (ts i))
      | .forml =>
             .rel LPA.Rel.forml (fun i => to_l_term (ts i))
      | .sentencel =>
             .rel LPA.Rel.sentencel (fun i => to_l_term (ts i))
      | .formlt =>
             .rel LPA.Rel.formlt (fun i => to_l_term (ts i))
      | .sentencelt =>
             .rel LPA.Rel.sentencelt (fun i => to_l_term (ts i))
  | _, φ, .imp ψ π => .imp (subs_fml_for_t_in_fml φ ψ) (subs_fml_for_t_in_fml φ π)
  | _, φ, .all ψ => .all (subs_fml_for_t_in_fml (φ↓) ψ)

  @[simp]
  def subs_fml_for_t_in_fml_0 : ℒ.Fml → ℒₜ.Fml → ℒ.Fml :=
  @subs_fml_for_t_in_fml 0

  @[simp]
  def subs_fml_for_t_in_fml_finset {n : ℕ} (s : Finset (ℒₜ.BoundedFormula ℕ n)) (φ: ℒ.BoundedFormula ℕ n) : Finset (ℒ.BoundedFormula ℕ n) := s.image (subs_fml_for_t_in_fml φ)

  open PA.Induction

  def add_one_bv : {n : ℕ} → ℒ.BoundedFormula (Fin 1) n → ℒ.BoundedFormula (Fin 1) (n + 1)
  | _, .falsum => .falsum
  | _, .equal t p => .equal (Substitution.up_bv t) (Substitution.up_bv p)
  | _, .rel R ts => .rel R (fun i => Substitution.up_bv (ts i))
  | _, .imp φ ψ => .imp (add_one_bv φ) (add_one_bv ψ)
  | _, .all φ => .all (add_one_bv φ)

  @[simp]
  def subs_fml_for_t_in_sent : {n : ℕ} →  ℒ.BoundedFormula (Fin 1) n → ℒₜ.BoundedFormula Empty n → ℒ.BoundedFormula Empty n
  | _, _, .falsum  => .falsum
  |  _, _, .equal tₐ₁ tₐ₂ => .equal (to_l_term tₐ₁) (to_l_term tₐ₂)
  |  _, φ, .rel R ts =>
      match R with
      | .t => (φ/[(to_l_term (ts 0))])
      | .var =>
             .rel LPA.Rel.var (fun i => to_l_term (ts i))
      | .const =>
             .rel LPA.Rel.const (fun i => to_l_term (ts i))
      | .term =>
             .rel LPA.Rel.term (fun i => to_l_term (ts i))
      | .clterm =>
             .rel LPA.Rel.clterm (fun i => to_l_term (ts i))
      | .forml =>
             .rel LPA.Rel.forml (fun i => to_l_term (ts i))
      | .sentencel =>
             .rel LPA.Rel.sentencel (fun i => to_l_term (ts i))
      | .formlt =>
             .rel LPA.Rel.formlt (fun i => to_l_term (ts i))
      | .sentencelt =>
             .rel LPA.Rel.sentencelt (fun i => to_l_term (ts i))
  | _, φ, .imp ψ π => .imp (subs_fml_for_t_in_sent φ ψ) (subs_fml_for_t_in_sent φ π)
  | _, φ, .all ψ => .all (subs_fml_for_t_in_sent (add_one_bv φ) ψ)

#check subs_fml_for_t_in_sent

  @[simp]
  def subs_r_for_fml_in_set (s : ℒₜ.Theory) (φ : ℒ.Formula (Fin 1)) : ℒ.Theory := s.image (subs_fml_for_t_in_sent φ)


  notation φ"/ₜ["ψ"]" => subs_fml_for_t_in_fml ψ φ
  notation φ"/tsent["ψ"]" => subs_fml_for_t_in_sent ψ φ
  notation Γ"/ₜₛ["φ"]" => subs_r_for_fml_in_set Γ φ
  notation Γ"/ₜ["φ"]" => subs_fml_for_t_in_fml_finset Γ φ

  lemma empty_replacement : ∀φ : ℒ.Fml, ∅/ₜ[φ] = ∅ := by
    intro φ
    simp

  lemma in_replacement_finset : ∀s : Finset ℒₜ.Fml, ∀φ : ℒₜ.Fml, ∀ψ : ℒ.Fml, (φ ∈ s) → ((φ/ₜ[ψ]) ∈ (s/ₜ[ψ])) := by
    intro s φ ψ h
    simp
    apply Exists.intro φ (And.intro h (by rfl))

  lemma in_replacement_set : ∀s : ℒₜ.Theory, ∀φ : ℒₜ.Sentence, ∀ψ : ℒ.Formula (Fin 1), (φ ∈ s) → ((φ/tsent[ψ]) ∈ (s/ₜₛ[ψ])) := by
    intro s φ ψ h
    simp
    apply Exists.intro φ (And.intro h (by rfl))

  def term_translation : (t₁ : ℒ.Term (α ⊕ Fin n)) → to_l_term (to_lt_term t₁) = t₁
    | .var v => match v with
      | .inl m => by simp[to_l_term,to_lt_term]
      | .inr m => by simp[to_l_term,to_lt_term]
    | .func f ts => by
      simp[to_lt_term,to_l_term]
      apply And.intro
      match f with
      | .null => trivial
      | .succ => trivial
      | .add => trivial
      | .mult => trivial
      | .neg => trivial
      | .conj => trivial
      | .disj => trivial
      | .cond => trivial
      | .forall => trivial
      | .exists => trivial
      | .denote => trivial
      | .subs => trivial
      simp[term_translation]

  def homomorph_replacement : {n : ℕ} → (φ : ℒ.BoundedFormula ℕ n) → (ψ : ℒ.BoundedFormula ℕ n) → (to_lt_bf φ)/ₜ[ψ] = φ
    | _, .falsum, _ => by
      simp[to_lt_bf]
    | _, .equal t₁ t₂, _ => by
      simp[to_lt_bf]
      apply And.intro
      apply term_translation
      apply term_translation
    | _, @BoundedFormula.rel ℒ ℕ n l R ts, _ => by
      match l, R with
      | 1, .sentencelt => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .formlt => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .sentencel => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .forml => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .clterm => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .term => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .const => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .var => simp[to_lt_bf,to_lt_rel,term_translation]
    | _, .imp φ₁ ψ₁, ψ => by
      simp[to_lt_bf]
      apply And.intro
      apply homomorph_replacement φ₁ ψ
      apply homomorph_replacement ψ₁ ψ
    | _, .all φ₁, ψ => by
      simp[to_lt_bf]
      apply homomorph_replacement φ₁

  def homomorph_replacement_sent : {n : ℕ} → (φ : ℒ.BoundedFormula Empty n) → (ψ : ℒ.BoundedFormula (Fin 1) n) → (to_lt_bf φ)/tsent[ψ] = φ
    | _, .falsum, _ => by
      simp[to_lt_bf]
    | _, .equal t₁ t₂, _ => by
      simp[to_lt_bf]
      apply And.intro
      apply term_translation
      apply term_translation
    | _, @BoundedFormula.rel ℒ Empty n l R ts, _ => by
      match l, R with
      | 1, .sentencelt => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .formlt => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .sentencel => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .forml => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .clterm => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .term => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .const => simp[to_lt_bf,to_lt_rel,term_translation]
      | 1, .var => simp[to_lt_bf,to_lt_rel,term_translation]
    | _, .imp φ₁ ψ₁, ψ => by
      simp[to_lt_bf]
      apply And.intro
      apply homomorph_replacement_sent φ₁ ψ
      apply homomorph_replacement_sent ψ₁ ψ
    | _, .all φ₁, ψ => by
      simp[to_lt_bf]
      apply homomorph_replacement_sent φ₁

  def general_t_replacement_form {φ : ℒ.Sentence}{ψ : ℒ.Formula (Fin 1)}: T(TB.sentence_encoding φ)/tsent[ψ] = ψ/[to_l_term (TB.sentence_encoding φ)] := by trivial

  def no_t_to_l_sent {n : ℕ} (φ : ℒₜ.BoundedFormula Empty n) (h : ¬ contains_T φ) : ℒ.BoundedFormula Empty n :=
  match n, φ with
  | _, .falsum => .falsum
  | _, .equal t1 t2 => .equal (to_l_term t1) (to_l_term t2)
  | _, .rel R ts =>
    match R with
    | .t => by
      simp at h
    | .var =>
      .rel LPA.Rel.var (fun i => (to_l_term (ts 0)))
    | .const => .rel LPA.Rel.const (fun i => (to_l_term (ts 0)))
    | .term => .rel .term (fun i => (to_l_term (ts 0)))
    | .clterm => .rel .clterm (fun i => (to_l_term (ts 0)))
    | .forml => .rel .forml (fun i => (to_l_term (ts 0)))
    | .sentencel => .rel .sentencel (fun i => (to_l_term (ts 0)))
    | .formlt => .rel .formlt (fun i => (to_l_term (ts 0)))
    | .sentencelt => .rel .sentencelt (fun i => (to_l_term (ts 0)))
  | _, .imp ψ1 ψ2 => .imp (no_t_to_l_sent ψ1 (by simp at h; exact h.left)) (no_t_to_l_sent ψ2 (by simp at h; exact h.right))
  | _, .all ψ => .all (no_t_to_l_sent ψ (by assumption))

open Classical
  noncomputable def build_relevant_phis_list {Γ Δ : Finset ℒₜ.Fml} : Derivation 𝐓𝐁 Γ Δ → List ℒ.Sentence
    | Derivation.tax φ _ _  =>
      match φ with
      | (((((.rel L_T.Rel.t ts₁ ⟹ f₁)⟹⊥)⟹((f₂ ⟹ .rel L_T.Rel.t ts₂)⟹⊥))⟹⊥)⟹⊥) => 
        if h : ¬contains_T f₁ ∧ f₁ = f₂ ∧ (ts₁ 0) = L_T.numeral (sent_tonat f₁) ∧ (ts₂ 0) = L_T.numeral (sent_tonat f₂) then [(no_t_to_l_sent f₁ h.left)] else []
      | _ => []
    | .lax _ => []
    | .left_conjunction _ _ _ _ d₁ _ _ => build_relevant_phis_list d₁
    | .left_disjunction _ _ _ _ _ d₁ _ d₂ _ _ => (build_relevant_phis_list d₁) ∪ (build_relevant_phis_list d₂)
    | .left_implication _ _ _ _ _ d₁ _ d₂ _ _ => (build_relevant_phis_list d₁) ∪ (build_relevant_phis_list d₂)
    | .left_bot _ => []
    | .right_conjunction _ _ _ _ _ d₁ _ d₂ _ _ => (build_relevant_phis_list d₁) ∪ (build_relevant_phis_list d₂)
    | .right_disjunction _ _ _ _ d₁ _ _ => build_relevant_phis_list d₁
    | .right_implication _ _ _ _ _ d₁ _ _ _ => build_relevant_phis_list d₁
    | .left_forall _ _ _ _ _ _ d₁ _ _  => build_relevant_phis_list d₁
    | .left_exists _ _ _ _ d₁ _ => build_relevant_phis_list d₁
    | .right_forall _ _ _ _ d₁ _ => build_relevant_phis_list d₁
    | .right_exists _ _ _ _ _ _ d₁ _ _ => build_relevant_phis_list d₁

 noncomputable def build_relevant_phis {Γ Δ : Finset ℒₜ.Fml} : Derivation 𝐓𝐁 Γ Δ → List ℒ.Sentence := fun d => (build_relevant_phis_list d).dedup

  open LPA
  open L_T
  open TermEncoding
  open PAT
  open SyntaxTheory
  open TB
  def restricted_tarski_biconditionals {Γ Δ} (d : Derivation 𝐓𝐁 Γ Δ) : ℒₜ.Theory := 𝐏𝐀𝐓 ∪ {φ | ∃ψ : ℒ.Sentence, φ = T(⌜ψ⌝) ⇔ ψ ∧ ψ ∈ (build_relevant_phis d)}

  notation "𝐓𝐁("d")" => restricted_tarski_biconditionals d

end Conservativity

namespace FirstOrder.Language.Sentence
variable {L : Language}
def to_fml : L.Sentence → L.Formula ℕ := @Calculus.bf_empty_to_bf_N _ 0
end FirstOrder.Language.Sentence

namespace Conservativity
  open FirstOrder.Language
  open BoundedFormula
  open TermEncoding
  open Calculus
  
  notation "ℒ.enc" f => LPA.numeral (sent_tonat f)
  variable {L : Language}

  def up_fv {n : ℕ} : L.Term (Empty ⊕ Fin n) → L.Term ((Fin 1) ⊕ Fin n)
  | .var v => match v with
    | .inl l => by cases l
    | .inr l => (Term.var (.inr l))
  | .func f ts => .func f (fun i => up_fv (ts i))

  def to_fin_1 : {n : ℕ} → L.BoundedFormula Empty n → L.BoundedFormula (Fin 1) n
  | _, .falsum => .falsum
  | _, .equal t p => .equal (up_fv t) (up_fv p)
  | _, .rel R ts => .rel R (fun i => up_fv (ts i))
  | _, .imp φ ψ => .imp (to_fin_1 φ) (to_fin_1 ψ)
  | _, .all φ => .all (to_fin_1 φ)

  def build_tau : List ℒ.Sentence → ℒ.Formula (Fin 1)
    | .nil => ⊥
    | .cons a lst => (((#0) =' (ℒ.enc a)) ∧' (to_fin_1 a)) ∨' (build_tau lst)
  variable {L : Language}[∀i, DecidableEq (L.Functions i)][∀i, DecidableEq (L.Relations i)]
  def iff_from_sides {Th Γ Δ} (A B : L.Formula ℕ) (S₁ S₂ S₃ : Finset (L.Formula ℕ)) : Derivation Th Δ S₁ → S₁ = S₃ ∪ {A ⟹ B} → Derivation Th Δ S₂ → S₂ = S₃ ∪ {B ⟹ A} → Γ = (S₃ ∪ {A ⇔ B}) → Derivation Th Δ Γ := sorry

  def iff_to_left_to_right {Th Γ Δ} (A B : (L.Formula ℕ)) (S₁ S₂: Finset (L.Formula ℕ)) : Derivation Th Δ S₁ → S₁ = S₂ ∪ {A ⇔ B} → Γ = S₂ ∪ {A ⟹ B} → Derivation Th Δ Γ := sorry

  def iff_to_right_to_left {Th Γ Δ} (A B : (L.Formula ℕ)) (S₁ S₂ : Finset (L.Formula ℕ)) : Derivation Th Δ S₁ → S₁ = S₂ ∪ {A ⇔ B} → Γ = S₂ ∪ {B ⟹ A} → Derivation Th Δ Γ := sorry

  def split_if {Th Γ Δ} (A B : (L.Formula ℕ)) (S₁ S₂ S₃) : Derivation Th S₁ S₂ → S₂ = S₃ ∪ {A ⟹ B} → Δ = S₁ ∪ {A} → Γ = S₃ ∪ {B} → Derivation Th Δ Γ := sorry

  def subst_disj_distr {A B: (L.Formula (Fin 1))} : (A ∨' B)/[t] = (A/[t] ∨' B/[t]) := by trivial

  def subst_conj_distr {A B: (L.Formula (Fin 1))} : (A ∧' B)/[t] = (A/[t] ∧' B/[t]) := by trivial

  def subst_if_distr {A B: (L.Formula (Fin 1))} : (A ⟹ B)/[t] = (A/[t] ⟹ B/[t]) := by trivial

  def to_N_disj_distr {A B : (L.Sentence)} : bf_empty_to_bf_N (A ∨' B) = (bf_empty_to_bf_N A) ∨' (bf_empty_to_bf_N B) := by trivial

  def to_N_conj_distr {A B : (L.Sentence)} : bf_empty_to_bf_N (A ∧' B) = (bf_empty_to_bf_N A) ∧' (bf_empty_to_bf_N B) := by trivial

  def to_N_iff_distr {A B : (L.Sentence)} : bf_empty_to_bf_N (A ⇔ B) = (bf_empty_to_bf_N A) ⇔ (bf_empty_to_bf_N B) := by trivial

  def to_N_if_distr {A B : (L.Sentence)} : bf_empty_to_bf_N (A ⟹ B) = (bf_empty_to_bf_N A) ⟹ (bf_empty_to_bf_N B) := by trivial


  lemma numeral_no_subst : ∀n, ∀t : ℒ.Term (Empty ⊕ Fin m), term_substitution t (LPA.numeral n) = LPA.numeral n
| .zero, t => by
  simp[LPA.numeral,LPA.null,term_substitution,Matrix.empty_eq]
| .succ n, t => by
  simp[LPA.numeral,term_substitution]
  have step1 : term_substitution t (LPA.numeral n) = LPA.numeral n := by
    apply numeral_no_subst
  simp[step1]
  apply funext
  intro x
  cases x with
  | mk val isLt =>
    cases val with
    | zero =>
      simp
    | succ n =>
      simp


    variable {L : Language} [∀n, DecidableEq (L.Functions n)][∀n, DecidableEq (L.Relations n)][∀i, Encodable (L.Functions i)][∀i, Encodable (L.Relations i)]
    axiom right_weakening {Th Δ Γ} (A : (L.Formula ℕ)) (S) : Derivation Th Γ S → Δ = S ∪ {A} → Derivation Th Γ Δ

  def forall_sent_term_trans_subst_self {n : ℕ} : (t₁ : L.Term (Empty ⊕ Fin n)) → (t₂ : L.Term (Empty ⊕ Fin n)) → (term_substitution t₂ (up_fv t₁)) = t₁
    | .var (.inl m), _ =>
      by cases m
    | .var (.inr m), _ => by
      simp[term_substitution,up_fv]
    | .func f ts, _ => by
      simp[term_substitution,up_fv,forall_sent_term_trans_subst_self]

  def forall_sent_trans_subst_self : {n : ℕ} → (φ : L.BoundedFormula Empty n) → (t : L.Term (Empty ⊕ Fin n)) → (to_fin_1 φ)/[t] = φ
  | _, .falsum, _ => by
    simp[to_fin_1]
  | _, .equal t₁ t₂, t => by
      simp[formula_substitution,to_fin_1,term_substitution,sent_term_to_formula_term]
      simp[formula_substitution,bf_empty_to_bf_N,term_substitution,sent_term_to_formula_term,forall_sent_term_trans_subst_self]
  | _, .rel R ts, t => by
    simp[formula_substitution,to_fin_1,term_substitution,sent_term_to_formula_term,forall_sent_term_trans_subst_self]
  | _, .imp φ ψ, t => by
    simp[formula_substitution,to_fin_1,term_substitution,sent_term_to_formula_term,forall_sent_term_trans_subst_self]
    apply And.intro
    apply forall_sent_trans_subst_self φ
    apply forall_sent_trans_subst_self ψ
  | _, .all φ, t => by
    simp[formula_substitution,to_fin_1,term_substitution,sent_term_to_formula_term,forall_sent_term_trans_subst_self]
    apply forall_sent_trans_subst_self φ

  open PA.Induction

#check @LPA.numeral

  def numeral_to_sent_is_numeral : {k : ℕ} →  (sent_term_to_formula_term (@LPA.numeral (Empty ⊕ Fin 0) k)) = (LPA.numeral k)
    | .zero => by
      simp[sent_term_to_formula_term,LPA.numeral,null,Matrix.empty_eq]
    | .succ n => by
      simp[sent_term_to_formula_term,LPA.numeral,numeral_to_sent_is_numeral,Matrix.vec_single_eq_const]

  def switch (A B : ℒ.Formula ℕ) : {A, B} = ({B, A} : Finset (ℒ.Formula ℕ)) := by
    rw[Finset.insert_eq]
    rw[Finset.insert_eq]
    rw[Finset.union_comm]

  def tonat_inj (φ ψ : L.Formula ℕ) : φ ≠ ψ → (formula_tonat φ) ≠ (formula_tonat ψ) := by
  sorry

  def sent_tonat_inj {φ ψ : L.Sentence} : φ ≠ ψ → (sent_tonat φ) ≠ (sent_tonat ψ) := by  
  sorry

  noncomputable def extend_iff_right {A B a: L.Formula ℕ} : Derivation Th Γ (Δ ∪ {A ⇔ B}) → Derivation Th Γ (Δ ∪ {B ⟹ (A ∨' a)}) := by
    intro d
    apply Derivation.right_implication B (A ∨' a) ({B} ∪ Γ) (Δ ∪ {A ∨' a}) Δ _ rfl rfl rfl
    apply Derivation.right_disjunction A a (Δ ∪ {A, a}) Δ _ rfl rfl
    apply right_weakening a (Δ ∪ {A}) _ (by simp[Finset.insert_eq])
    apply (fun d₁ => iff_to_right_to_left A B (Δ ∪ {A ⇔ B}) Δ d₁ (by rfl) (by rfl)) at d
    apply (fun d₁ => split_if B A Γ (Δ ∪ {B ⟹ A}) Δ d₁ (by rfl) (by rfl) (by rfl)) at d
    rw[Finset.union_comm] at d
    exact d
end Conservativity

namespace FirstOrder.Language.Term
  variable {L : Language}
  def fin_one_to_bv : L.Term ((Fin 1) ⊕ Fin n) → L.Term (Empty ⊕ Fin (n + 1))
    | .var v => match v with
      | .inl m => .var (.inr ⟨n,(by simp)⟩)
      | .inr m => match m with
        | .mk k isLt => .var (.inr ⟨k,(Nat.lt_trans isLt (Nat.lt_succ_self n))⟩)
    | .func f ts => .func f (fun i => fin_one_to_bv (ts i))

  def fin_one_to_N : L.Term ((Fin 1) ⊕ Fin n) → L.Term (ℕ ⊕ Fin n)
    | .var v => match v with
      | .inl m => .var (.inl m)
      | .inr m => .var (.inr m)
    | .func f ts => .func f fun i => fin_one_to_N (ts i)
end FirstOrder.Language.Term

namespace FirstOrder.Language.BoundedFormula
open Term
variable{L : Language}
  def fin_one_to_bv : {n : ℕ} → L.BoundedFormula (Fin 1) n → L.BoundedFormula Empty (n + 1)
    | _, .falsum => .falsum
    | _, .equal t₁ t₂ => .equal (Term.fin_one_to_bv t₁) (Term.fin_one_to_bv t₂)
    | _, .rel R ts => .rel R (fun i => Term.fin_one_to_bv (ts i))
    | _, .imp φ ψ => .imp (fin_one_to_bv φ) (fin_one_to_bv ψ)
    | _, .all φ => .all (fin_one_to_bv φ)

  def fin_one_to_N : {n : ℕ} → L.BoundedFormula (Fin 1) n → L.BoundedFormula ℕ n
    | _, .falsum => .falsum
    | _, .equal t₁ t₂ => .equal (Term.fin_one_to_N t₁) (Term.fin_one_to_N t₂)
    | _, .rel R ts => .rel R (fun i => Term.fin_one_to_N (ts i))
    | _, .imp φ ψ => .imp (fin_one_to_N φ) (fin_one_to_N ψ)
    | _, .all φ => .all (fin_one_to_N φ)

open Calculus
variable {n : ℕ} [∀i, DecidableEq (L.Functions i)] [∀i, DecidableEq (L.Relations i)]
  def right_instantiation {t : L.Term (Empty ⊕ Fin 0)} {A : L.BoundedFormula (Fin 1) 0} {h : B = fin_one_to_bv A} : Derivation Th Δ (S ∪ {bf_empty_to_bf_N (∀'B)}) → Derivation Th Δ (S ∪ {bf_empty_to_bf_N (A/[t])}) := by sorry

end FirstOrder.Language.BoundedFormula

namespace Conservativity
open Calculus
  def derivable_num_not_eq {S : Finset (ℒ.Formula ℕ)}: {n m : ℕ} → (h₁ : n ≠ m) → Derivation 𝐏𝐀 Δ (S ∪ {∼( bf_empty_to_bf_N (BoundedFormula.equal (numeral n) (numeral m)))})
    | .zero, .zero, h₁ => by
      trivial
    | .zero, .succ k, h₁ => by
      simp[numeral]
      have h₂ : Derivation 𝐏𝐀 Δ (S ∪ {bf_empty_to_bf_N (∀' ∼(null =' S(&0)))}) := by
        apply Derivation.tax (∀' ∼(null =' S(&0)))
        simp[PA.peano_arithmetic]
        apply Or.intro_left
        apply PA.peano_axioms.first
        simp
        trivial

      have step3 : Derivation 𝐏𝐀 Δ (S ∪ {bf_empty_to_bf_N (∼(null =' S(numeral k)))}) := by
        apply @right_instantiation _ _ _ (∼(null =' S((var ∘ Sum.inr) 0))) _ _ _ (numeral k) (∼(null =' S(#0))) (by simp[Term.bdEqual,LPA.null,BoundedFormula.not,Term.fin_one_to_bv,Matrix.empty_eq,fin_one_to_bv,Matrix.vec_single_eq_const]; rfl) at h₂
        simp[Term.bdEqual,Matrix.empty_eq] at h₂
        simp[Term.bdEqual,Matrix.empty_eq,BoundedFormula.not,BoundedFormula.falsum,Matrix.vec_single_eq_const]
        exact h₂

      exact step3
    | _, _, _ => sorry

  def pa_proves_left_to_right_when_phi_not_in_l {φ : ℒ.Sentence} : (l : List ℒ.Sentence) → φ ∉ l → Derivation 𝐏𝐀 Δ (Γ ∪ {bf_empty_to_bf_N ((build_tau l)/[ℒ.enc φ] ⟹ φ)})
    | .nil, h₁ => by
      simp[build_tau,bf_empty_to_bf_N]
      apply Calculus.right_implication_intro
      apply Calculus.left_bot_intro
    | .cons a lst, h₁ => by
      simp[build_tau,subst_disj_distr,subst_conj_distr,to_N_disj_distr,to_N_conj_distr,Term.bdEqual,numeral_no_subst,forall_sent_trans_subst_self,to_N_iff_distr]
      apply Calculus.right_implication_intro
      apply Calculus.left_disjunction_intro
      -- d₁
      have step1: φ ≠ a := by
        simp at h₁
        exact h₁.left
      apply Calculus.left_conjunction_intro
      rw[Finset.insert_eq]
      rw[←Finset.union_assoc]
      apply Calculus.left_weakening_intro
      apply Calculus.left_double_negation_elimination
      apply Calculus.left_negation_intro
      apply derivable_num_not_eq
      apply sent_tonat_inj
      exact step1
      -- d₂
      simp at h₁
      apply Calculus.right_implication_elim
      apply pa_proves_left_to_right_when_phi_not_in_l lst h₁.right

  def if_pos {lst : List (ℒ.Sentence)} {a φ : ℒ.Sentence}{S : Finset (ℒ.Formula ℕ)} (h₁ : φ = a) (h₂ : Δ = S ∪ {bf_empty_to_bf_N (build_tau (a :: lst)/[ℒ.enc φ] ⇔ φ)}) (h₄ : ¬ a ∈ lst) : Derivation 𝐏𝐀 Γ Δ := by 
    simp[h₂,h₁,build_tau,subst_disj_distr,subst_conj_distr,to_N_disj_distr,to_N_conj_distr,Term.bdEqual,numeral_no_subst,forall_sent_trans_subst_self,to_N_iff_distr]
    apply Calculus.iff_intro
    --left to right
    apply Calculus.right_implication_intro
    apply Calculus.left_disjunction_intro
    -- d₁
    apply Calculus.left_conjunction_intro
    rw[Finset.insert_eq,Finset.union_comm {bf_empty_to_bf_N ..},←Finset.union_assoc]
    apply Calculus.left_weakening_intro
    apply Derivation.lax (Exists.intro a (And.intro (by simp) (by simp)))
    -- d₂
    apply Calculus.right_implication_elim
    apply pa_proves_left_to_right_when_phi_not_in_l lst h₄
    -- right to left
    apply Calculus.right_implication_intro
    apply Calculus.right_disjunction_intro
    rw[Finset.insert_eq,←Finset.union_assoc]
    apply Calculus.right_weakening_intro
    apply Calculus.right_conjunction_intro
    -- d₁
    simp[bf_empty_to_bf_N]
    apply Calculus.iax (sent_term_to_formula_term (ℒ.enc a)) _
    simp[Term.bdEqual]
    -- d₂
    apply Derivation.lax (Exists.intro (bf_empty_to_bf_N a) (And.intro (by simp) (by simp)))
    
  noncomputable def pa_proves_all_tau_disq {φ : ℒ.Sentence} {S : Finset (ℒ.Formula ℕ)} : (l : List ℒ.Sentence) → {h : l.Nodup} → φ ∈ l → Γ = S ∪ {bf_empty_to_bf_N ((build_tau l)/[ℒ.enc φ] ⇔ φ)} → Derivation 𝐏𝐀 Δ Γ
    | .nil, h, h₁, _ => by
      simp at h₁
    | .cons a lst, h, h₁, h₂ => by
      by_cases h₃ : φ = a
      -- case pos
      have step1 : a ∉ lst := by
        apply List.Nodup.notMem h
      apply if_pos h₃ h₂ step1

      -- case neg
      simp[h₃] at h₁
      have ih : Derivation 𝐏𝐀 Δ (S ∪ {bf_empty_to_bf_N ((build_tau lst)/[ℒ.enc φ] ⇔ φ)}) := by
        apply pa_proves_all_tau_disq lst h₁ rfl
        apply List.Nodup.of_cons h

      simp[build_tau,subst_disj_distr,subst_conj_distr,to_N_disj_distr,to_N_conj_distr,Term.bdEqual,numeral_no_subst,forall_sent_trans_subst_self,to_N_iff_distr] at h₂

      simp only [h₂]

      apply Calculus.iff_intro
      -- left to right
      apply Calculus.right_implication_intro
      apply Calculus.left_disjunction_intro
      -- d₁
      apply Calculus.left_conjunction_intro
      rw[Finset.insert_eq,←Finset.union_assoc]
      apply Calculus.left_weakening_intro
      apply Calculus.left_double_negation_elimination
      apply Calculus.left_negation_intro
      apply derivable_num_not_eq
      apply sent_tonat_inj h₃
      -- d₂
      apply Calculus.iff_to_left_to_right at ih
      exact Calculus.right_implication_elim ih
      -- right to left
      simp[build_tau,subst_disj_distr,subst_conj_distr,to_N_disj_distr,to_N_conj_distr,Term.bdEqual,numeral_no_subst,forall_sent_trans_subst_self,to_N_iff_distr] at ih
          
      have step1 : Derivation 𝐏𝐀 Δ (S ∪ {(bf_empty_to_bf_N φ) ⟹ (bf_empty_to_bf_N (build_tau lst/[ℒ.enc φ])) ∨' (bf_empty_to_bf_N (BoundedFormula.equal (ℒ.enc φ) (ℒ.enc a))) ∧' (bf_empty_to_bf_N a)}) := by
        exact extend_iff_right ih

      apply Calculus.right_implication_intro
      apply Calculus.or_comm
      apply Calculus.right_implication_elim at step1
      exact step1


  open SyntaxAxioms
  open BoundedFormula
  open PAT
  open L_T

  def distr_t_sub_over_union {A B : Finset (ℒₜ.Fml)} {φ : ℒ.Fml} : (A ∪ B)/ₜ[φ] = (A/ₜ[φ]) ∪ (B/ₜ[φ]) := by
    simp[Finset.image_union]
  def distr_t_sub_over_union_set {A B : ℒₜ.Theory} {φ : ℒ.Formula (Fin 1)} : (A ∪ B)/ₜₛ[φ] = (A/ₜₛ[φ]) ∪ (B/ₜₛ[φ]) := by
    simp[Set.image_union]
  def in_finset {A : ℒₜ.Fml} {φ : ℒ.Fml} : {A}/ₜ[φ] = {A/ₜ[φ]} := by
     trivial
  def distr_t_sub_over_conjunction {A B : ℒₜ.Fml} {φ : ℒ.Fml} : (A ∧' B)/ₜ[φ] = (A/ₜ[φ]) ∧' (B/ₜ[φ]) := by
    trivial
  def distr_tsent_sub_over_iff {A B : ℒₜ.Sentence} {φ : ℒ.Formula (Fin 1)} : (A ⇔ B)/tsent[φ] = (A/tsent[φ] ⇔ B/tsent[φ]) := by trivial

/-
match ((T(to_lt_term ⌜falsum⌝) ⟹ falsum) ⟹ (falsum ⟹ T(to_lt_term ⌜falsum⌝)) ⟹ ⊥) ⟹ ⊥, ⋯, ⋯ with
| ((rel Rel.t ts₁ ⟹ f₁) ⟹ (f₂ ⟹ rel Rel.t ts₂) ⟹ falsum) ⟹ falsum, h₁, h₂ =>
 if h : ¬contains_T f₁ ∧ f₁ = f₂ ∧ ts₁ = ![to_lt_term ⌜f₁⌝] ∧ ts₁ = ts₂ then [no_t_to_l_sent f₁ ⋯] else []
-/

  noncomputable def to_restricted : (d : Derivation 𝐓𝐁 Γ Δ) → Derivation 𝐓𝐁(d) Γ Δ
    | .tax A h₁ h₂ => by
      simp only [restricted_tarski_biconditionals,build_relevant_phis]
      simp only [TB.tarski_biconditionals] at h₁
      by_cases h₃ : A ∈ 𝐏𝐀𝐓
      -- pos
      apply Derivation.tax A
      simp [Set.union_def]
      apply Or.intro_left _ h₃
      exact h₂
      -- neg
      simp [h₃] at h₁
      apply Exists.choose_spec at h₁
--      simp [h₁] give maxRecursionDepth error
      sorry
    | .left_conjunction A B S₁ S₂ d₁ h₁ h₂ => by
      apply to_restricted at d₁
      simp only [h₂,restricted_tarski_biconditionals]
      simp only [h₁,restricted_tarski_biconditionals] at d₁
--      exact Calculus.left_conjunction_intro d₁
      sorry
    | _ => sorry

  noncomputable def pa_plus_der_general {Δ₁ Γ₁ : Finset ℒₜ.Fml} {φ : ℒ.Fml} : (d₁ : Derivation 𝐓𝐁 Δ₁ Γ₁) → (Derivation ((𝐓𝐁(d₁))/ₜₛ[build_tau (build_relevant_phis d₁)]) (Δ₁/ₜ[BoundedFormula.fin_one_to_N (build_tau (build_relevant_phis d₁))]) (Γ₁/ₜ[BoundedFormula.fin_one_to_N (build_tau (build_relevant_phis d₁))]))
  | Derivation.tax φ h₁ h₂ => by
    sorry
    -- use that applying the substitution to (i) 𝐓𝐁 yields 𝐏𝐀 ∪ {x | ∃ ψ_1 ∈ build_relevant_phis (Derivation.tax h₁ h₂), build_tau (build_relevant_phis (Derivation.tax h₁ h₂))/[⌜ψ_1⌝] ⇔ ψ_1 = x}) and (ii) Finset.image ϕ.onFormula Γ for an arbitrary Γ yields Γ.
  | .left_conjunction A B S₁ S₂ d₂ h₁ h₂ => by
    simp only [h₂]
    rw[distr_t_sub_over_union, in_finset, distr_t_sub_over_conjunction]
    apply Calculus.left_conjunction_intro
    rw[Finset.insert_eq]
    rw[←in_finset,←in_finset,←distr_t_sub_over_union,←distr_t_sub_over_union,←Finset.insert_eq,←h₁]
    simp only [build_tau, build_relevant_phis]
    sorry
--    apply pa_plus_der_general d₂ : cannot verify cuz doesnt know TB(d₁) = TB(d₂)
  | _ => sorry

  def numeral_language_independent {α : Type} :{k : ℕ} → (to_l_term (@L_T.numeral α k)) = (LPA.numeral k)
    | .zero => by
      simp[L_T.numeral,L_T.null,to_l_term,to_l_func,Matrix.empty_eq]
    | .succ n => by
      simp[L_T.numeral,L_T.null,to_l_term,to_l_func,Matrix.empty_eq]
      rw[numeral_language_independent]
      simp only [Matrix.vec_single_eq_const]

open TermEncoding
  def encoding_typing {φ} : to_l_term (TB.sentence_encoding φ) = ℒ.enc φ := by 
    simp[to_l_term,TB.sentence_encoding,LPA.numeral,sent_tonat]
    rw[numeral_language_independent]


  lemma tb_replacement {φ : ℒ.Fml} {d : Derivation 𝐓𝐁 {} {to_lt_bf φ}} : 𝐓𝐁(d)/ₜₛ[build_tau (build_relevant_phis d)] = (𝐏𝐀 ∪ {(((build_tau (build_relevant_phis d))/[ℒ.enc ψ]) ⇔ ψ) | ψ ∈ (build_relevant_phis d)}) := by
    apply Set.eq_of_subset_of_subset
    -- tb sub pa+
    rw[Set.subset_def]
    intro x
    intro h
    sorry
    sorry
/-
    simp only [TB.tarski_biconditionals] at h
    rw[distr_t_sub_over_union_set] at h
    simp only [Set.mem_union] at h
    simp only [pat] at h
    rw[distr_t_sub_over_union_set,distr_t_sub_over_union_set] at h
    simp only [Set.mem_union] at h
    cases h with
    | inl p => sorry
    | inr p =>
      simp
      apply Or.intro_right
      simp at p
      apply Exists.choose_spec at p
      rw[←p.right]
      have step2 := by apply Exists.choose_spec p.left
      rw[step2]
      apply Exists.intro p.left.choose
      rw[distr_tsent_sub_over_iff]
      simp only [homomorph_replacement_sent]
      rw[general_t_replacement_form]
      rw[encoding_typing]
      apply And.intro
      -- left
      simp only [build_relevant_phis,build_relevant_phis_list]
      sorry
      -- right
      rfl
    -- pa+ sub tb
    sorry
-/

  noncomputable def pa_plus_der {φ : ℒ.Fml} : (d₁ : Derivation 𝐓𝐁 {} {to_lt_bf φ}) →  Derivation (𝐏𝐀 ∪ {(((build_tau (build_relevant_phis d₁))/[ℒ.enc ψ]) ⇔ ψ) | ψ ∈ (build_relevant_phis d₁)}) {} {φ} := by
  intro d₂
  apply pa_plus_der_general at d₂
  rw[in_finset] at d₂
  simp only [empty_replacement, homomorph_replacement] at d₂
  rw[tb_replacement] at d₂
  exact d₂
  exact φ

  noncomputable def pa_plus_to_pa {φ : ℒ.Fml} {d : Derivation 𝐓𝐁 {} {to_lt_bf φ}} {Γ Δ : Finset ℒ.Fml} : (Derivation (𝐏𝐀 ∪ {(((build_tau (build_relevant_phis d))/[ℒ.enc ψ]) ⇔ ψ) | ψ ∈ (build_relevant_phis d)}) Γ Δ) → (Derivation 𝐏𝐀 Γ Δ)
    | Derivation.tax φ h₁ h₂ => by
      by_cases h₃ : φ ∈ 𝐏𝐀
      -- pos
      apply Derivation.tax φ h₃ h₂
      -- neg
      simp[h₃] at h₁
      apply Exists.choose_spec at h₁
      apply pa_proves_all_tau_disq (build_relevant_phis d) (h₁.left)
      rw[←h₁.right] at h₂
      exact h₂
      simp only [build_relevant_phis]
      apply List.nodup_dedup
    | .lax h => .lax h
    | .left_bot h => .left_bot h
    | .left_conjunction A B S₁ S₂ d₁ h₂ h₃ => by
      rw[h₃]
      apply Calculus.left_conjunction_intro
      rw[h₂] at d₁
      apply pa_plus_to_pa d₁
      --Calculus.left_conjunction_intro (pa_plus_to_pa d₁)
    | .left_disjunction A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ => .left_disjunction A B S₁ S₂ S₃ (pa_plus_to_pa d₁) h₁ (pa_plus_to_pa d₂) h₂ h₃
    | .left_implication A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ => .left_implication A B S₁ S₂ S₃ (pa_plus_to_pa d₁) h₁ (pa_plus_to_pa d₂) h₂ h₃
    | .right_conjunction A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ => .right_conjunction A B S₁ S₂ S₃ (pa_plus_to_pa d₁) h₁ (pa_plus_to_pa d₂) h₂ h₃
    | .right_disjunction A B S₁ S₂ d₁ h₁ h₂ => by
      rw[h₂]
      apply Calculus.right_disjunction_intro
      rw[h₁] at d₁
      apply pa_plus_to_pa d₁
    | .right_implication A B S₁ S₂ S₃ d₁ h₁ h₂ h₃ => .right_implication A B S₁ S₂ S₃ (pa_plus_to_pa d₁) h₁ h₂ h₃
    | .left_forall A B h₁ t S₁ S₂ d₁ h₂ h₃ => .left_forall A B h₁ t S₁ S₂ (pa_plus_to_pa d₁) h₂ h₃
    | .left_exists A B S₁ h₁ d₁ h₂ => .left_exists A B S₁ h₁ (pa_plus_to_pa d₁) h₂
    | .right_forall A B S h₁ d₁ h₂ => .right_forall A B S h₁ (pa_plus_to_pa d₁) h₂
    | .right_exists A B t S₁ S₂ h₁ d₁ h₂ h₃ => .right_exists A B t S₁ S₂ h₁ (pa_plus_to_pa d₁) h₂ h₃

  noncomputable def translation (φ : ℒ.Fml) (d : Derivation 𝐓𝐁 {} {to_lt_bf φ}) : (Derivation 𝐏𝐀 {} {φ}) := pa_plus_to_pa (pa_plus_der d)

  theorem conservativity_of_tb : ∀φ : ℒ.Fml, (𝐓𝐁 ⊢ φ) → (𝐏𝐀 ⊢ φ) := by
    intro φ
    simp only [formula_provable,sequent_provable,emptyFormList]
    intro h
    apply Nonempty.intro (translation φ (Classical.choice h))

end Conservativity
