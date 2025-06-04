
import FormalizingAxiomaticTheoriesOfTruth.ProofTheory

open FirstOrder
open Language

namespace PA
  open Languages
  open LPA
  open L_T
  open BoundedFormula

  variable{L : Language}
  def replace_bv_with_non_var_term (f : BoundedFormula L ℕ 1) (t : Term L ℕ) : L.Formula ℕ :=
    subst f.toFormula (fun _ : ℕ ⊕ Fin 1 => t)
  notation A "//[" t "]" => replace_bv_with_non_var_term A t
  def replace_bv_with_bv_term  (f : BoundedFormula L ℕ 1) (t : Term L (ℕ ⊕ Fin 1)) : BoundedFormula L ℕ 1 :=
    (relabel id (subst (f.toFormula) (fun _ : (ℕ ⊕ Fin 1) => t)))
  notation A "///[" t "]" => replace_bv_with_bv_term A t

  /-- The induction function for ℒₚₐ -/
  def induction (f : BoundedFormula ℒ ℕ 1) : ℒ.Formula ℕ :=
    ∼ (f//[LPA.null] ⟹ (∼(∀'(f ⟹ f///[S(&0)])))) ⟹ ∀'f

  /-- Peano arithemtic -/
  inductive peano_arithmetic : Set (ℒ.Formula ℕ) where
    | first : peano_arithmetic (∀' ∼(LPA.null =' S(&0)))
    | second :peano_arithmetic (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
    | third : peano_arithmetic (∀' ((&0 add LPA.null) =' &0))
    | fourth : peano_arithmetic (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
    | fifth : peano_arithmetic (∀' ((&0 times LPA.null) =' LPA.null))
    | sixth : peano_arithmetic (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
    | induction (φ) : peano_arithmetic (induction φ)

  notation "𝐏𝐀" => peano_arithmetic

end PA

namespace PAT
open Languages
  open L_T
 /-- The induction function for ℒₚₐ -/
  def induction (f : BoundedFormula ℒₜ ℕ 1) : ℒₜ.Formula ℕ :=
    ∼ (f//[L_T.null] ⟹ (∼(∀'(f ⟹ f///[S(&0)])))) ⟹ ∀'f

  /-- Peano arithemtic -/
  inductive peano_arithmetic_t : Set (ℒₜ.Formula ℕ) where
    | first : peano_arithmetic_t (∀' ∼(L_T.null =' S(&0)))
    | second :peano_arithmetic_t (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
    | third : peano_arithmetic_t (∀' ((&0 add L_T.null) =' &0))
    | fourth : peano_arithmetic_t (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
    | fifth : peano_arithmetic_t (∀' ((&0 times L_T.null) =' L_T.null))
    | sixth : peano_arithmetic_t (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
    | induction (φ) : peano_arithmetic_t (induction φ)

  notation "𝐏𝐀𝐓" => peano_arithmetic_t
end PAT

namespace TB
open Languages
open L_T
open LPA
open PAT
open SyntaxTheory
open TermEncoding

inductive tarski_biconditionals : Set (ℒₜ.Formula ℕ) where
  | pat_axioms {φ} : peano_arithmetic_t φ → tarski_biconditionals φ
  | syntax_axioms {φ : ℒₜ.Formula Empty} {ψ : ℒₜ.Formula ℕ} {h : ψ = (Calculus.bf_empty_to_bf_N φ)} : syntax_theory φ → tarski_biconditionals ψ
  | disquotation {φ : Sentence ℒ} {ψ : ℒₜ.Formula ℕ} {h : ψ =  (T(⌜φ⌝) ⇔ φ)} : tarski_biconditionals ψ

notation "𝐓𝐁" => tarski_biconditionals

end TB

namespace Conservativity
  open Languages LPA L_T Calculus FirstOrder.Language.BoundedFormula TermEncoding

  abbrev ℒ.Fml := ℒ.Formula ℕ
  abbrev ℒₜ.Fml := ℒₜ.Formula ℕ

  variable {L : Language}
  def g₁ {n : ℕ} (t :  L.Term (ℕ ⊕ Fin n)) (α :  (ℕ ⊕ Fin n)) : L.Term (ℕ ⊕ Fin n) :=
  match n with   
  | 0 => 
    match α with
    | .inl v =>
      match v with
      | 0 => t
      | .succ n => Term.var (.inl n)
    | .inr v => by
      cases v with
      | mk val isLt => simp at isLt
  | .succ k => 
    match α with
    | .inl v => Term.var (.inl v)
    | .inr v => 
      ite (v = n) t (Term.var (.inr v))

  def my_subst (φ : L.BoundedFormula ℕ n) (t : L.Term (ℕ ⊕ Fin n)):= relabel id (subst φ.toFormula (g₁ t))   
  notation φ "////[" t "]" => my_subst φ t

  @[simp]
  def subs_t_for_fml : {n : ℕ} →  ℒ.BoundedFormula ℕ n → ℒₜ.BoundedFormula ℕ n → ℒ.BoundedFormula ℕ n
  | _, _, .falsum  => .falsum
  |  _, _, .equal t₁ t₂ => .equal (to_l_term t₁) (to_l_term t₂)
  |  _, φ, .rel R ts =>
      match R with
      | .t => (φ////[(to_l_term (ts 0))]) 
      -- replace .t by φ 
     -- φ/[(to_l_term (ts 0))]
     /- match m with
      | 0 => 
        -- replace lowest free variable
        sorry
      | .succ r =>
        -- replace highest bounded variable, i.e. shift all bounded variables down by n + 1, replace lowest free variable and shift everything back up by n + 1 -/ 
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
  | _, φ, .imp ψ π => .imp (subs_t_for_fml φ ψ) (subs_t_for_fml φ π)  
  | _, φ, .all ψ => .all (subs_t_for_fml (φ↓) ψ)
  
  @[simp]
  def subs_t_for_fml_0 : ℒ.Fml → ℒₜ.Fml → ℒ.Fml :=
  @subs_t_for_fml 0 
  
  lemma all_falsum_neq_eq : ∀L : Language, ∀α : Type _, BoundedFormula.equal t₁ t₂ ≠ BoundedFormula.falsum := by
    intro L α 
    simp

  lemma subs_t_for_fml_inj : Function.Injective subs_t_for_fml_0 := by
    simp[Function.Injective]
    intro a₁ a₂ h₁
    /-cases a₁
    cases a₂
    simp
    case falsum t₁ t₂ => 
      have step1 : subs_t_for_fml (.equal t₁ t₂) = .equal (to_l_term t₁) (to_l_term t₂) := by 
      sorry
      simp[all_falsum_neq_eq] at h₁-/
    sorry
    
    
    

  @[simp]
  def subs_r_for_fml_in_set (s : Set ℒₜ.Fml) (φ : ℒ.Fml) : Set (ℒ.Fml) := s.image (subs_t_for_fml_0 φ)     

  @[simp]
  def subs_r_for_fml_in_finset (s : Finset ℒₜ.Fml) (φ: ℒ.Fml)  : Finset (ℒ.Fml) := s.image (subs_t_for_fml_0 φ)

  @[simp]
    lemma reversible : ∀α : Type, ∀t : ℒ.Term α, to_l_term (ϕ.onTerm t) = t := by
  intro α t
  unfold to_l_term LHom.onTerm LHom.onFunction
  sorry
    

  notation φ"/ₜ["ψ"]" => subs_t_for_fml_0 ψ φ
  notation Γ"/ₜₛ["φ"]" => subs_r_for_fml_in_set Γ φ
  notation Γ"/ₜ["φ"]" => subs_r_for_fml_in_finset Γ φ

  lemma empty_replacement : ∀φ, ∅/ₜ[φ] = ∅ := by 
    intro φ 
    simp
  
  lemma in_replacement_finset : ∀s : Finset ℒₜ.Fml, ∀φ : ℒₜ.Fml, ∀ψ : ℒ.Fml, (φ ∈ s) → ((φ/ₜ[ψ]) ∈ (s/ₜ[ψ])) := by
    intro s φ ψ h
    simp
    apply Exists.intro φ (And.intro h (by rfl))

  lemma in_replacement_set : ∀s : Set ℒₜ.Fml, ∀φ : ℒₜ.Fml, ∀ψ : ℒ.Fml, (φ ∈ s) → ((φ/ₜ[ψ]) ∈ (s/ₜₛ[ψ])) := by
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


  def build_relevant_phis {Γ Δ : Finset ℒₜ.Fml} (d : Derivation 𝐓𝐁 Γ Δ) : Finset (ℒ.Fml) := sorry

  noncomputable def build_tau (Γ : Finset (ℒ.Fml)) : ℒ.Fml := finset_iSup Γ

open BoundedFormula
open PAT 
#check ℒₜ.Sentence 
#check SyntaxTheory.syntax_theory
  lemma tb_either {φ : ℒₜ.Fml} : (φ ∈ 𝐓𝐁) → (φ ∈ 𝐏𝐀𝐓 ∨ (∃ψ : ℒₜ.Sentence, ψ ∈  SyntaxTheory.syntax_theory ∧ (φ = Calculus.bf_empty_to_bf_N ψ)) ∨ (∃ψ : ℒ.Sentence, φ = (T(⌜ψ⌝) ⇔ ψ)))
  | .pat_axioms h => by
        
    sorry
  | .syntax_axioms h => sorry
  | .disquotation => sorry
  
  noncomputable def pa_plus_der_general {Δ₁ Γ₁ : Finset ℒₜ.Fml} : (d : Derivation 𝐓𝐁 Δ₁ Γ₁) → (Derivation (𝐓𝐁/ₜₛ[build_tau (build_relevant_phis d)]) (Δ₁/ₜ[build_tau (build_relevant_phis d)]) (Γ₁/ₜ[build_tau (build_relevant_phis d)]))
  | @Derivation.tax _ _ _ _ _ _ ψ h₁ h₂ => by
   
    #check ψ 
    by_cases h₃ : (ψ ∈ 𝐏𝐀𝐓) 
    #check 𝐏𝐀𝐓 
--    #check in_replacement 𝐏𝐀𝐓 ψ (build_tau (build_relevant_phis (Derivation.tax h₁ h₂)))
    apply (in_replacement_set 𝐏𝐀𝐓 ψ (build_tau (build_relevant_phis (Derivation.tax h₁ h₂)))) at h₃
    
    sorry
    sorry
    
    
/-    match h₁ with
    | .pat_axioms h => sorry
    | .syntax_axioms h =>  sorry
    | .disquotation => sorry
-/
    
    -- use that applying the substitution to (i) 𝐓𝐁 yields 𝐏𝐀 ∪ {x | ∃ ψ_1 ∈ build_relevant_phis (Derivation.tax h₁ h₂), build_tau (build_relevant_phis (Derivation.tax h₁ h₂))/[⌜ψ_1⌝] ⇔ ψ_1 = x}) and (ii) Finset.image ϕ.onFormula Γ for an arbitrary Γ yields Γ.    
  | .left_conjunction A B S d₁ h₁ h₂ h₃ => by

   apply Derivation.left_conjunction (A/ₜ[build_tau (build_relevant_phis d₁)]) (B/ₜ[build_tau (build_relevant_phis d₁)]) (S/ₜ[build_tau (build_relevant_phis d₁)]) (pa_plus_der_general d₁) _ _ _  
   apply (in_replacement_finset S A (build_tau (build_relevant_phis d₁)))
   exact h₁
   
   apply (in_replacement_finset S B (build_tau (build_relevant_phis d₁))) 
   exact h₂
   
   simp[h₃, Finset.image_union, Finset.image_sdiff]
   
   
   
   
   
   
   -- 
   sorry
  | _ => sorry
  
  lemma tb_replacement {φ : ℒ.Fml} {d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}} : 𝐓𝐁/ₜₛ[build_tau (build_relevant_phis d)] = (𝐏𝐀 ∪ {(((build_tau (build_relevant_phis d))/[⌜ψ⌝]) ⇔ ψ) | ψ ∈ (build_relevant_phis d)}) := sorry

  noncomputable def pa_plus_der {φ : ℒ.Fml} : (d₁ : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) →  Derivation (𝐏𝐀 ∪ {(((build_tau (build_relevant_phis d₁))/[⌜ψ⌝]) ⇔ ψ) | ψ ∈ (build_relevant_phis d₁)}) {} {φ} := by
  intro d₂
  apply @pa_plus_der_general {} {ϕ.onFormula φ} at d₂
  simp only [empty_replacement, homomorph_replacement, tb_replacement] at d₂ 
  exact d₂  
 
  def pa_proves_all_tau_disq_sents : ∀Γ : Finset (ℒ.Fml), ∀φ ∈ Γ, (Δ Γ₂ : Finset ℒ.Fml) → (((build_tau Γ)/[⌜φ⌝] ⇔ φ) ∈ Δ) → Nonempty (Derivation 𝐏𝐀 Γ₂ Δ) := by
    intro Γ φ Δ Γ₂ h₁ h₂
    induction Γ using Finset.induction_on with
    | empty => sorry
    | insert b => 
      
      sorry

  example : ∀Γ : Finset ℒ.Fml, ∀φ ∈ Γ, 𝐏𝐀 ⊢ (build_tau Γ)/[⌜φ⌝] ⇔ φ := by
    intro Γ φ h
    induction Γ using Finset.induction_on with
    | empty => sorry
    | insert b c => 
      simp
      let sing (a) : Finset ℒ.Fml := {a} 
      have step1 {a : ℒ.Fml} {s} : insert a s = (sing a) ∪ s := by
        rfl
      simp[step1,sing] at h
      cases h with
      | inl => 
        simp[build_tau,finset_iSup]

        sorry
      | inr => 
        
        sorry

  noncomputable def pa_der_general {φ : ℒ.Fml} {d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}} {Γ Δ : Finset ℒ.Fml} : (Derivation (𝐏𝐀 ∪ {(((build_tau (build_relevant_phis d))/[⌜ψ⌝]) ⇔ ψ) | ψ ∈ (build_relevant_phis d)}) Γ Δ) → (Derivation 𝐏𝐀 Γ Δ)
    | @Derivation.tax _ _ _ _ _ _ ψ h₁ h₂ => by
      by_cases h₃ : ψ ∈ 𝐏𝐀
      apply Derivation.tax h₃ h₂
      simp[h₃] at h₁
      have step1 : h₁.choose ∈ build_relevant_phis d ∧ build_tau (build_relevant_phis d)/[⌜h₁.choose⌝] ⇔ h₁.choose = ψ := by
        apply Exists.choose_spec at h₁
        exact h₁
     
      have step2 : (build_tau (build_relevant_phis d)/[⌜h₁.choose⌝] ⇔ h₁.choose) ∈ Δ := by
        simp[(And.right step1)]
        exact h₂

      #check pa_proves_all_tau_disq_sents (build_relevant_phis d) h₁.choose (And.left step1) Δ Γ step2 
      
      have step3 : Derivation 𝐏𝐀 Γ Δ := by
        apply Classical.choice (pa_proves_all_tau_disq_sents (build_relevant_phis d) h₁.choose (And.left step1) Δ Γ step2)
     
      exact step3 
    | .lax h => .lax h
    | .left_bot h => .left_bot h
    | .left_conjunction A B S d₁ h₁ h₂ h₃ => .left_conjunction A B S (pa_der_general d₁) h₁ h₂ h₃
    | .left_disjunction A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ => .left_disjunction A B S₁ S₂ S₃ (pa_der_general d₁) h₁ (pa_der_general d₂) h₂ h₃
    | .left_implication A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ => .left_implication A B S₁ S₂ S₃ (pa_der_general d₁) h₁ (pa_der_general d₂) h₂ h₃
    | .left_negation A S₁ S₂ d₁ h₁ h₂ => .left_negation A S₁ S₂ (pa_der_general d₁) h₁ h₂
    | .right_conjunction A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ => .right_conjunction A B S₁ S₂ S₃ (pa_der_general d₁) h₁ (pa_der_general d₂) h₂ h₃
    | .right_disjunction A B S d₁ h₁ => .right_disjunction A B S (pa_der_general d₁) h₁
    | .right_implication A B S₁ S₂ S₃ d₁ h₁ h₂ h₃ => .right_implication A B S₁ S₂ S₃ (pa_der_general d₁) h₁ h₂ h₃
    | .right_negation A S₁ S₂ d₁ h₁ h₂ => .right_negation A S₁ S₂ (pa_der_general d₁) h₁ h₂
    | .left_forall A B h₁ t S d₁ h₂ h₃ => .left_forall A B h₁ t S (pa_der_general d₁) h₂ h₃
    | .left_exists A B S₁ h₁ d₁ h₂ => .left_exists A B S₁ h₁ (pa_der_general d₁) h₂
    | .right_forall A B S h₁ d₁ h₂ => .right_forall A B S h₁ (pa_der_general d₁) h₂
    | .right_exists A B t S h₁ d₁ h₂ => .right_exists A B t S h₁ (pa_der_general d₁) h₂
    | .cut A S₁ S₂ S₃ S₄ d₁ d₂ h₁ h₂ => .cut A S₁ S₂ S₃ S₄ (pa_der_general d₁) (pa_der_general d₂) h₁ h₂

  noncomputable def pa_der {φ : ℒ.Fml} {d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}} : (Derivation (𝐏𝐀 ∪ {(((build_tau (build_relevant_phis d))/[⌜ψ⌝]) ⇔ ψ) | ψ ∈ (build_relevant_phis d)}) {} {φ}) → (Derivation 𝐏𝐀 {} {φ}) := pa_der_general

  noncomputable def translation (φ : ℒ.Fml) (d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) : (Derivation 𝐏𝐀 {} {φ}) := pa_der (pa_plus_der d)

  theorem conservativity_of_tb : ∀φ : ℒ.Fml, (𝐓𝐁 ⊢ φ) → (𝐏𝐀 ⊢ φ) := by
    simp
    intro φ
    intro h
    apply Nonempty.intro (translation φ h)

end Conservativity
