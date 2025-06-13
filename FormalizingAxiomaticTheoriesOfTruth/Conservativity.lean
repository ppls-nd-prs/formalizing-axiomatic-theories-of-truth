
import FormalizingAxiomaticTheoriesOfTruth.ProofTheory
import FormalizingAxiomaticTheoriesOfTruth.ArithTheories

open FirstOrder
open Language

namespace Conservativity
  open Languages LPA L_T Calculus FirstOrder.Language.BoundedFormula TermEncoding

    def to_l_func ⦃arity : ℕ⦄ : (ℒₜ.Functions arity) → (ℒ.Functions arity)
    | .zero => .zero
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
  def subs_t_for_fml : {n : ℕ} →  ℒ.BoundedFormula ℕ n → ℒₜ.BoundedFormula ℕ n → ℒ.BoundedFormula ℕ n
  | _, _, .falsum  => .falsum
  |  _, _, .equal t₁ t₂ => .equal (to_l_term t₁) (to_l_term t₂)
  |  _, φ, .rel R ts =>
      match R with
      | .t => (φ////[(to_l_term (ts 0))]) 
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
  
  @[simp]
  def subs_r_for_fml_in_set (s : Set ℒₜ.Fml) (φ : ℒ.Fml) : Set (ℒ.Fml) := s.image (subs_t_for_fml_0 φ)     

  @[simp]
  def subs_r_for_fml_in_finset (s : Finset ℒₜ.Fml) (φ: ℒ.Fml)  : Finset (ℒ.Fml) := s.image (subs_t_for_fml_0 φ)

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

  def no_t_to_l_fml {n : ℕ} (φ : ℒₜ.BoundedFormula ℕ n) (h : ¬ contains_T φ) : ℒ.BoundedFormula ℕ n :=
  match n, φ with
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (to_l_term t₁) (to_l_term t₂)
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
  | _, .imp ψ₁ ψ₂ => .imp (no_t_to_l_fml ψ₁ (by simp at h; exact h.left)) (no_t_to_l_fml ψ₂ (by simp at h; exact h.right))
  | _, .all ψ => .all (no_t_to_l_fml ψ (by assumption)) 

  noncomputable def build_relevant_phis {Γ Δ : Finset ℒₜ.Fml} : Derivation 𝐓𝐁 Γ Δ → List ℒ.Fml 
    | @Derivation.tax _ _ _ _ _ _ _ h =>
      match h.choose with
      | (((.rel L_T.Rel.t ts₁ ⟹ f₁) ⟹ ((f₂ ⟹ .rel L_T.Rel.t ts₂) ⟹ ⊥)) ⟹ ⊥) => 
        if h : ¬contains_T f₁ ∧ f₁ = f₂ ∧ (ts₁ 0) = L_T.numeral (formula_tonat f₁) ∧ (ts₂ 0) = L_T.numeral (formula_tonat f₂) then [(no_t_to_l_fml f₁ h.left)] else []
      | _ => []
    | .lax _ => []
    | .iax _ _ => []
    | .i_two_for_one _ _ _ _ _ _ d₁ _ _ => build_relevant_phis d₁
    | .i_one_for_two _ _ _ _ _ _ d₁ _ _ => build_relevant_phis d₁
    | .left_conjunction _ _ _ d₁ _ _ _ => build_relevant_phis d₁
    | .left_disjunction _ _ _ _ _ d₁ _ d₂ _ _ => (build_relevant_phis d₁) ∪ (build_relevant_phis d₂)
    | .left_implication _ _ _ _ _ d₁ _ d₂ _ _ => (build_relevant_phis d₁) ∪ (build_relevant_phis d₂)
    | .left_bot _ => []
    | .left_negation _ _ _ d₁ _ _=> build_relevant_phis d₁
    | .right_conjunction _ _ _ _ _ d₁ _ d₂ _ _ => (build_relevant_phis d₁) ∪ (build_relevant_phis d₂)
    | .right_disjunction _ _ _ d₁ _  => build_relevant_phis d₁
    | .right_implication _ _ _ _ _ d₁ _ _ _ => build_relevant_phis d₁
    | .right_negation _ _ _ d₁ _ _ => build_relevant_phis d₁
    | .left_forall _ _ _ _ _ d₁ _ _ => build_relevant_phis d₁
    | .left_exists _ _ _ _ d₁ _ => build_relevant_phis d₁
    | .right_forall _ _ _ _ d₁ _ => build_relevant_phis d₁
    | .right_exists _ _ _ _ _ d₁ _ => build_relevant_phis d₁
    | .cut _ _ _ _ _ d₁ d₂ _ _ => (build_relevant_phis d₁) ∪ (build_relevant_phis d₂)
  
  notation "ℒ.enc" φ => LPA.numeral (formula_tonat φ)
  
  def build_tau : List ℒ.Fml → ℒ.Fml
    | .nil => ⊥
    | .cons a lst => (((#0) =' (ℒ.enc a)) ∧' a) ∨' (build_tau lst)
 
  def iff_der {Th Γ Δ} (A B : ℒ.Fml) (S₁ S₂ S₃ : Finset ℒ.Fml) : Derivation Th Δ S₁ → S₁ = S₃ ∪ {A ⟹ B} → Derivation Th Δ S₂ → S₂ = S₃ ∪ {B ⟹ A} → Γ = (S₃ ∪ {A ⇔ B}) → Derivation Th Δ Γ := sorry

  def subst_disj_distr {A B: ℒ.Fml} : (A ∨' B)/[t] = (A/[t] ∨' B/[t]) := by sorry

  def subst_conj_distr {A B: ℒ.Fml} : (A ∧' B)/[t] = (A/[t] ∧' B/[t]) := by sorry
    
    variable {L : Language} [∀n, DecidableEq (L.Functions n)][∀n, DecidableEq (L.Relations n)]
    axiom right_weakening {Th Δ Γ} (A : ℒ.Fml) (S) : Derivation Th Γ S → Δ = S ∪ {A} → Derivation Th Γ Δ

    def t₁ : ℒ.Term (ℕ ⊕ Fin 0) := null
    def φ₁ := (#0 =' t₁)
    #eval φ₁ 
    #eval φ₁////[t₁] 
    #check  φ₁////[t₁] 
    #check (t₁ =' t₁) 
    #eval (t₁ =' t₁) 
    def this_subst : φ₁////[t₁] = (t₁ =' t₁) := by
      #check φ₁////[t₁]  
      #check (t₁ =' t₁) 
      simp[relabel, id]
      --rfl
      
      --unfold my_subst relabel id subst φ₁ t₁ mapTermRel g₂ Term.relabel  
--      simp
      sorry

  lemma test {t : ℒ.Term (ℕ ⊕ Fin 0)} {t' : ℒ.Term ℕ}: ((var (Sum.inl 0) =' t)////[t]) = (t =' t):= by
     unfold my_subst subst mapTermRel g₂ Term.subst relabel
     simp
     sorry

    def all_subst : {t : ℒ.Term (ℕ ⊕ Fin 0)} → ((var (Sum.inl 0) =' t)////[t]) = (t =' t)
      | .var v => by
        cases v with
        | inl n => 
          match n with
          | .zero => rfl
          | .succ Nat.zero => 
            
            sorry
          | .succ n => 
            simp[subst,Function.comp,g₂,mapTermRel,Term.subst,Sum.elim,Term.relabel,id,BoundedFormula.toFormula]
            
            sorry
        | inr n => sorry
        
      | .func f ts => sorry

  noncomputable def pa_proves_all_tau_disq : (l : List ℒ.Fml) → φ ∈ l → ((build_tau l)/[ℒ.enc φ] ⇔ φ) ∈ Γ → Derivation 𝐏𝐀 Δ Γ
    | .nil, h₁, _ => by
      simp at h₁
    | .cons a lst, h₁, h₂ => by
      simp at h₁
      
      let A₁ := (build_tau (a :: lst)/[ℒ.enc φ])
      let B₁ := φ
      let S₁ := Γ \ {build_tau (a :: lst)/[ℒ.enc φ] ⇔ φ}
      apply iff_der A₁ B₁ (S₁ ∪ {A₁ ⟹ B₁}) (S₁ ∪ {B₁ ⟹ A₁}) S₁ _ (rfl) _ rfl (by simp[A₁,B₁,S₁]; exact h₂)
      -- case left_to_right
      sorry
      -- case right_to_left
      simp[A₁,B₁]
      let A₂ := φ
      let B₂ := build_tau (a :: lst)/[ℒ.enc φ]
      let S₂₃ := S₁
      let S₂₁ := {A₂} ∪ Δ
      let S₂₂ := S₂₃ ∪ {B₂}
      apply Derivation.right_implication A₂ B₂ S₂₁ S₂₂ S₂₃ _ rfl rfl rfl
      
      simp[S₂₁,S₂₂,S₂₃,A₂,B₂,B₁,A₁,build_tau]
      by_cases h₂ : φ = a
      -- pos
      simp[h₂,subst_disj_distr]
      let A₃ := ((var (Sum.inl 0) =' ℒ.enc a)∧'a)/[ℒ.enc a]
      let B₃ := build_tau lst/[ℒ.enc a]
      let S₃ := S₁ ∪ {A₃, B₃}

      sorry
      -- case neg
      sorry

  open SyntaxAxioms
  open BoundedFormula
  open PAT 

  noncomputable def pa_plus_der_general {Δ₁ Γ₁ : Finset ℒₜ.Fml} {φ : ℒ.Fml} (d₁ : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}): Derivation 𝐓𝐁 Δ₁ Γ₁ → (Derivation (𝐓𝐁/ₜₛ[build_tau (build_relevant_phis d₁)]) (Δ₁/ₜ[build_tau (build_relevant_phis d₁)]) (Γ₁/ₜ[build_tau (build_relevant_phis d₁)]))
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

