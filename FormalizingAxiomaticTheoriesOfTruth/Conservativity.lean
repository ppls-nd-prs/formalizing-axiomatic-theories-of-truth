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
  def subs_fml_for_t_in_fml_finset (s : Finset ℒₜ.Fml) (φ: ℒ.Fml)  : Finset (ℒ.Fml) := s.image (subs_fml_for_t_in_fml_0 φ)
  
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


  notation φ"/ₜ["ψ"]" => subs_fml_for_t_in_fml_0 ψ φ
  notation φ"/tsent["ψ"]" => subs_fml_for_t_in_sent ψ φ
  notation Γ"/ₜₛ["φ"]" => subs_r_for_fml_in_set Γ φ
  notation Γ"/ₜ["φ"]" => subs_fml_for_t_in_fml_finset Γ φ

  lemma empty_replacement : ∀φ, ∅/ₜ[φ] = ∅ := by 
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

  lemma homomorph_replacement : ∀φ, ∀ψ, {ϕ.onFormula φ}/ₜ[ψ] = {φ} := by
    intro φ ψ
    simp[LHom.onFormula]
    cases φ with
    | falsum => 
      rfl
    | equal t₁ t₂ =>   
      cases t₁ with
      | var n₁ => 
        cases t₂ with
        | var n₂ =>
          rfl
        | func f ts => 
          cases f with
          | succ =>
            simp
            sorry
            -- problems with term equality in recursion case
            /-match (ts i) with
            | .var v => sorry
            | .func f₂ ts₂ => sorry-/
          | _ => sorry
      | func f ts => 
        cases t₂ with
        | var n₂ => 
          simp[LHom.onFormula]  
          sorry
        | func f₂ ts₂ =>
          simp[LHom.onFormula]
          sorry
        
    | _ => sorry

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

  noncomputable def build_relevant_phis {Γ Δ : Finset ℒₜ.Fml} : Derivation 𝐓𝐁 Γ Δ → List ℒ.Sentence
    | @Derivation.tax _ _ _ _ _ _ _ h =>
      match h.choose with
      | (((.rel L_T.Rel.t ts₁ ⟹ f₁) ⟹ ((f₂ ⟹ .rel L_T.Rel.t ts₂) ⟹ ⊥)) ⟹ ⊥) => 
        if h : ¬contains_T f₁ ∧ f₁ = f₂ ∧ (ts₁ 0) = L_T.numeral (sent_tonat f₁) ∧ (ts₂ 0) = L_T.numeral (sent_tonat f₂) then [(no_t_to_l_sent f₁ h.left)] else []
      | _ => []
    | .lax _ => []
    | .left_conjunction _ _ _ _ d₁ _ _ => build_relevant_phis d₁
    | .left_disjunction _ _ _ _ _ d₁ _ d₂ _ _ => (build_relevant_phis d₁) ∪ (build_relevant_phis d₂)
    | .left_implication _ _ _ _ _ d₁ _ d₂ _ _ => (build_relevant_phis d₁) ∪ (build_relevant_phis d₂)
    | .left_bot _ => []
    | .right_conjunction _ _ _ _ _ d₁ _ d₂ _ _ => (build_relevant_phis d₁) ∪ (build_relevant_phis d₂)
    | .right_disjunction _ _ _ _ d₁ _ _ => build_relevant_phis d₁
    | .right_implication _ _ _ _ _ d₁ _ _ _ => build_relevant_phis d₁
    | .left_forall _ _ _ _ _ _ d₁ _ _  => build_relevant_phis d₁
    | .left_exists _ _ _ _ d₁ _ => build_relevant_phis d₁
    | .right_forall _ _ _ _ d₁ _ => build_relevant_phis d₁
    | .right_exists _ _ _ _ _ _ d₁ _ _ => build_relevant_phis d₁

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

  set_option maxHeartbeats 1000000
  
  def tonat_inj (φ ψ : L.Formula ℕ) : φ ≠ ψ → (formula_tonat φ) ≠ (formula_tonat ψ) := by  
  sorry

  def neq_num_derivable {Δ Γ : Finset (ℒ.Formula ℕ)}:  (n m : ℕ) → (h : n ≠ m) → (∼(LPA.numeral n =' LPA.numeral m) ∈ Γ) → Derivation 𝐏𝐀 Δ Γ
    | .zero, .zero, h₁, h₂ => by
      simp at h₁
    | .zero, .succ m, h₁, h₂ => by
      simp[numeral] at h₂ 
      have h₃ : (∀' ∼(LPA.null =' S(&0))) ∈ 𝐏𝐀 := by
        simp[PA.peano_arithmetic]
        apply Or.intro_left
        apply PA.peano_axioms.first
      have h₅ : Derivation 𝐏𝐀 Δ (Γ ∪ {∀' ∼(LPA.null =' S(&0))}) := by
--        apply Derivation.tax ...
        sorry
      have h₄ : Derivation 𝐏𝐀 Δ (Γ ∪ {∼(null =' S(numeral m))}) := by
--        apply universal_instantiation_right
        sorry
      sorry
    | _, _, _, _ => sorry

  noncomputable def extend_iff {A B a: L.Formula ℕ} : Derivation Th Γ (Δ ∪ {A ⇔ B}) → Derivation Th Γ (Δ ∪ {B ⟹ (A ∨' a)}) := by
    intro d
    apply Derivation.right_implication B (A ∨' a) ({B} ∪ Γ) (Δ ∪ {A ∨' a}) Δ _ rfl rfl rfl
    apply Derivation.right_disjunction A a (Δ ∪ {A, a}) Δ _ rfl rfl 
    apply right_weakening a (Δ ∪ {A}) _ (by simp[Finset.insert_eq]) 
    apply (fun d₁ => iff_to_right_to_left A B (Δ ∪ {A ⇔ B}) Δ d₁ (by rfl) (by rfl)) at d
    apply (fun d₁ => split_if B A Γ (Δ ∪ {B ⟹ A}) Δ d₁ (by rfl) (by rfl) (by rfl)) at d
    rw[Finset.union_comm] at d 
    exact d  

  def right_instantiation {t : L.Term _} {A : L.BoundedFormula ℕ 0} {h : B = A↓} : Derivation Th Δ (S ∪ {(∀'B)}) → Derivation Th Δ (S ∪ {A/[t]}) := by sorry

  def derivable_num_not_eq {S : Finset (ℒ.Formula ℕ)}: (n m : ℕ) → (h₁ : n ≠ m) → Derivation 𝐏𝐀 Δ (S ∪ {∼(numeral n =' numeral m)})
    | .zero, .zero, h₁ => by
      trivial
    | .zero, .succ k, h₁ => by
      simp[numeral]
      have h₂ : Derivation 𝐏𝐀 Δ (S ∪ {∀' ∼(null =' S(&0))}) := by
        apply Derivation.tax
        apply Exists.intro (∀' ∼(null =' S(&0)))
        apply And.intro
        simp[PA.peano_arithmetic]
        apply Or.intro_left
        apply PA.peano_axioms.first
        simp
        apply Or.intro_right
        simp[bf_empty_to_bf_N,Term.bdEqual,sent_term_to_formula_term,null,not,Matrix.empty_eq,BoundedFormula.not]
        apply And.intro
        simp[Matrix.vec_single_eq_const]
        trivial
--      apply right_instantiation h₂ 
      sorry
    | _, _, _ => sorry

  def if_first {a φ : ℒ.Sentence}{S : Finset (ℒ.Formula ℕ)} (h₁ : φ = a) (h₂ : Δ = S ∪ {bf_empty_to_bf_N (build_tau (a :: lst)/[ℒ.enc φ] ⇔ φ)}) : Derivation 𝐏𝐀 Γ Δ := by sorry 

  noncomputable def pa_proves_all_tau_disq {φ : ℒ.Sentence} {S : Finset (ℒ.Formula ℕ)} : (l : List ℒ.Sentence) → φ ∈ l → Γ = S ∪ {bf_empty_to_bf_N ((build_tau l)/[ℒ.enc φ] ⇔ φ)} → Derivation 𝐏𝐀 Δ Γ
    | .nil, h₁, _ => by
      simp at h₁
    | .cons a lst, h₁, h₂ => by
      by_cases h₃ : φ = a
      apply if_first h₃ h₂
      
      simp[h₃] at h₁
      have ih : Derivation 𝐏𝐀 Δ (S ∪ {bf_empty_to_bf_N ((build_tau lst)/[ℒ.enc φ] ⇔ φ)}) := by
        apply pa_proves_all_tau_disq lst h₁ rfl
      
      simp[build_tau,subst_disj_distr,subst_conj_distr,to_N_disj_distr,to_N_conj_distr,Term.bdEqual,numeral_no_subst,forall_sent_trans_subst_self,to_N_iff_distr] at ih
      
      simp[build_tau,subst_disj_distr,subst_conj_distr,to_N_disj_distr,to_N_conj_distr,Term.bdEqual,numeral_no_subst,forall_sent_trans_subst_self,to_N_iff_distr] at h₂
      
      
      have step1 : Derivation 𝐏𝐀 Δ (S ∪ {(bf_empty_to_bf_N φ) ⟹ (bf_empty_to_bf_N (build_tau lst/[ℒ.enc φ])) ∨' (bf_empty_to_bf_N (equal (ℒ.enc φ) (ℒ.enc a)) ∧' (bf_empty_to_bf_N a))}) := by
        exact extend_iff ih
    
      
      
      sorry


  open SyntaxAxioms
  open BoundedFormula
  open PAT 

  noncomputable def pa_plus_der_general {Δ₁ Γ₁ : Finset ℒₜ.Fml} {φ : ℒ.Fml} (d₁ : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}): Derivation 𝐓𝐁 Δ₁ Γ₁ → (Derivation (𝐓𝐁/ₜₛ[build_tau_sent (build_relevant_phis d₁)]) (Δ₁/ₜ[build_tau (build_relevant_phis d₁)]) (Γ₁/ₜ[build_tau (build_relevant_phis d₁)]))
  | @Derivation.tax _ _ _ _ _ _ _ h => by
    sorry
    -- use that applying the substitution to (i) 𝐓𝐁 yields 𝐏𝐀 ∪ {x | ∃ ψ_1 ∈ build_relevant_phis (Derivation.tax h₁ h₂), build_tau (build_relevant_phis (Derivation.tax h₁ h₂))/[⌜ψ_1⌝] ⇔ ψ_1 = x}) and (ii) Finset.image ϕ.onFormula Γ for an arbitrary Γ yields Γ.    
  | .left_conjunction A B S d₂ h₁ h₂ h₃ => by
    let tau := build_tau (build_relevant_phis d₁)
    have step1 : A/ₜ[tau] ∈ S/ₜ[tau] := by
      apply  (in_replacement_finset S A (tau)) 
      exact h₁
    have step2 :  B/ₜ[tau] ∈ S/ₜ[tau] := by
      apply  (in_replacement_finset S B (tau)) 
      exact h₂
    have step3 : Δ₁/ₜ[tau] = (S/ₜ[tau] \ {A/ₜ[tau]}) \ {B/ₜ[tau]} ∪ {A/ₜ[tau]∧'B/ₜ[tau]} := sorry
    apply Derivation.left_conjunction (A/ₜ[tau]) (B/ₜ[tau]) (S/ₜ[tau]) (pa_plus_der_general d₁ d₂) step1 step2 step3     
  | _ => sorry
  
  lemma tb_replacement {φ : ℒ.Fml} {d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}} : 𝐓𝐁/ₜₛ[build_tau (build_relevant_phis d)] = (𝐏𝐀 ∪ {(((build_tau (build_relevant_phis d))/[⌜ψ⌝]) ⇔ ψ) | ψ ∈ (build_relevant_phis d)}) := 
    -- make use of : new def theories and def t-replacement
    sorry

  noncomputable def pa_plus_der {φ : ℒ.Fml} : (d₁ : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) →  Derivation (𝐏𝐀 ∪ {(((build_tau (build_relevant_phis d₁))/[⌜ψ⌝]) ⇔ ψ) | ψ ∈ (build_relevant_phis d₁)}) {} {φ} := by
  intro d₂
  apply pa_plus_der_general d₂ at d₂
  simp only [empty_replacement, homomorph_replacement, tb_replacement] at d₂ 
  exact d₂  

  noncomputable def pa_plus_to_pa {φ : ℒ.Fml} {d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}} {Γ Δ : Finset ℒ.Fml} : (Derivation (𝐏𝐀 ∪ {(((build_tau (build_relevant_phis d))/[⌜ψ⌝]) ⇔ ψ) | ψ ∈ (build_relevant_phis d)}) Γ Δ) → (Derivation 𝐏𝐀 Γ Δ)
    | @Derivation.tax _ _ _ _ _ _ _ h => by
      have hₐ : h.choose ∈ 𝐏𝐀 ∪ {x | ∃ ψ ∈ build_relevant_phis d, build_tau (build_relevant_phis d)/[⌜ψ⌝] ⇔ ψ = x} ∧ (h.choose ∈ Δ) := by
        apply Exists.choose_spec at h
        exact h
      have h₁ : h.choose ∈ 𝐏𝐀 ∪ {x | ∃ ψ ∈ build_relevant_phis d, build_tau (build_relevant_phis d)/[⌜ψ⌝] ⇔ ψ = x} := hₐ.left
      have h₂ : h.choose ∈ Δ := hₐ.right
      by_cases h₃ : h.choose ∈ 𝐏𝐀
      have h₄ : ∃f, f ∈ 𝐏𝐀 ∧ f ∈ Δ := by
        apply Exists.intro (h.choose) (And.intro h₃ h₂)
        
      apply Derivation.tax h₄
      simp[h₃] at h₁
      
      have step1 : h₁.choose ∈ build_relevant_phis d ∧ build_tau (build_relevant_phis d)/[⌜h₁.choose⌝] ⇔ h₁.choose = h.choose := by
        apply Exists.choose_spec at h₁
        exact h₁
     
      have step2 : (build_tau (build_relevant_phis d)/[⌜h₁.choose⌝] ⇔ h₁.choose) ∈ Δ := by
        simp[(And.right step1)]
        exact h₂
      
      have step3 : Derivation 𝐏𝐀 Γ Δ := by 
        apply pa_proves_all_tau_disq (build_relevant_phis d) (step1.left) step2 
        
      exact step3
    | .iax t h  => Derivation.iax t h
    | .i_one_for_two S φ t₁ t₂ h₁ h₂ d₁ h₃ h₄ => .i_one_for_two S φ t₁ t₂ h₁ h₂ (pa_plus_to_pa d₁) h₃ h₄
    | .i_two_for_one S φ t₁ t₂ h₁ h₂ d₁ h₃ h₄ => .i_two_for_one S φ t₁ t₂ h₁ h₂ (pa_plus_to_pa d₁) h₃ h₄
    | .lax h => .lax h
    | .left_bot h => .left_bot h
    | .left_conjunction A B S d₁ h₁ h₂ h₃ => .left_conjunction A B S (pa_plus_to_pa d₁) h₁ h₂ h₃
    | .left_disjunction A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ => .left_disjunction A B S₁ S₂ S₃ (pa_plus_to_pa d₁) h₁ (pa_plus_to_pa d₂) h₂ h₃
    | .left_implication A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ => .left_implication A B S₁ S₂ S₃ (pa_plus_to_pa d₁) h₁ (pa_plus_to_pa d₂) h₂ h₃
    | .left_negation A S₁ S₂ d₁ h₁ h₂ => .left_negation A S₁ S₂ (pa_plus_to_pa d₁) h₁ h₂
    | .right_conjunction A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ => .right_conjunction A B S₁ S₂ S₃ (pa_plus_to_pa d₁) h₁ (pa_plus_to_pa d₂) h₂ h₃
    | .right_disjunction A B S d₁ h₁ => .right_disjunction A B S (pa_plus_to_pa d₁) h₁
    | .right_implication A B S₁ S₂ S₃ d₁ h₁ h₂ h₃ => .right_implication A B S₁ S₂ S₃ (pa_plus_to_pa d₁) h₁ h₂ h₃
    | .right_negation A S₁ S₂ d₁ h₁ h₂ => .right_negation A S₁ S₂ (pa_plus_to_pa d₁) h₁ h₂
    | .left_forall A B h₁ t S d₁ h₂ h₃ => .left_forall A B h₁ t S (pa_plus_to_pa d₁) h₂ h₃
    | .left_exists A B S₁ h₁ d₁ h₂ => .left_exists A B S₁ h₁ (pa_plus_to_pa d₁) h₂
    | .right_forall A B S h₁ d₁ h₂ => .right_forall A B S h₁ (pa_plus_to_pa d₁) h₂
    | .right_exists A B t S h₁ d₁ h₂ => .right_exists A B t S h₁ (pa_plus_to_pa d₁) h₂
    | .cut A S₁ S₂ S₃ S₄ d₁ d₂ h₁ h₂ => .cut A S₁ S₂ S₃ S₄ (pa_plus_to_pa d₁) (pa_plus_to_pa d₂) h₁ h₂
  
  noncomputable def translation (φ : ℒ.Fml) (d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) : (Derivation 𝐏𝐀 {} {φ}) := pa_plus_to_pa (pa_plus_der d)

  theorem conservativity_of_tb : ∀φ : ℒ.Fml, (𝐓𝐁 ⊢ φ) → (𝐏𝐀 ⊢ φ) := by
    simp[formula_provable,sequent_provable]    
    intro φ
    intro h
    apply Nonempty.intro (translation φ h)

end Conservativity
