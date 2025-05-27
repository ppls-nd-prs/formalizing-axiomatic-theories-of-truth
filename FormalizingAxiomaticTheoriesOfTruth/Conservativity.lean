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
  | syntax_axioms {φ} : syntax_theory φ → tarski_biconditionals φ
  | disquotation {φ : Sentence ℒ} : tarski_biconditionals (T(⌜φ⌝) ⇔ φ)

notation "𝐓𝐁" => tarski_biconditionals

-- lemma all_tb_either : ∀φ ∈ 𝐓𝐁, φ ∈ 𝐏𝐀𝐓 ∨ φ ∈ syntax_theory ∨ ∃ψ :

end TB

namespace Conservativity
  open Languages
  open LPA
  open L_T
  open Calculus
  open TB
  open PA

  abbrev ℒ.Fml := ℒ.Formula ℕ
  abbrev ℒₜ.Fml := ℒₜ.Formula ℕ

  def subs_r_for_fml {α n} {k : ℕ} {L₁ L₂ : Language} : ℒₜ.BoundedFormula α n → ℒₜ.Relations k → ℒ.Fml → ℒ.Fml :=
    sorry

  def subs_r_for_fml_in_set {k : ℕ} : Set (ℒₜ.Fml) → ℒₜ.Relations k → ℒ.Fml → Set (ℒ.Fml) :=
    sorry

  def subs_r_for_fml_in_finset {k : ℕ} : Finset (ℒₜ.Fml) → ℒₜ.Relations k → ℒ.Fml → Finset (ℒ.Fml) :=
    sorry

  notation φ"/["R","ψ"]" => subs_r_for_fml φ R ψ
  notation Γ"/ₛ["R","φ"]" => subs_r_for_fml_in_set Γ R φ
  notation Γ"/["R","φ"]" => subs_r_for_fml_in_finset Γ R φ

  @[simp]
  lemma subs_empty_is_empty {k : ℕ} {R : ℒₜ.Relations k} {φ : ℒ.Fml} : ∅/[R,φ] = ∅ :=   sorry
  @[simp]
  lemma subs_t_single_hom_is_l_set {φ ψ : ℒ.Fml} : {ϕ.onFormula φ}/[.t, ψ] = {φ} := sorry

  def subs_der {Th : Set (ℒₜ.Fml)} {Γ Δ : Finset (ℒₜ.Fml)} {k : ℕ} (R : ℒₜ.Relations k) (φ : ℒ.Fml) (d : Derivation Th Γ Δ) : Derivation (Th/ₛ[R,φ]) (Γ/[R,φ]) (Δ/[R,φ]) :=
    sorry

  open PAT
  open SyntaxTheory
  open TermEncoding
  inductive restricted_tb (Γ : Finset (ℒ.Fml)) : Set (ℒₜ.Formula ℕ) where
  | pat_axioms (φ) : peano_arithmetic_t φ → restricted_tb Γ φ
  | syntax_axioms {φ} : syntax_theory φ → restricted_tb Γ φ
  | disquotation {φ} {h : φ ∈ Γ} : restricted_tb Γ (T(⌜φ⌝) ⇔ φ)

  notation "𝐓𝐁 " Γ => restricted_tb Γ

  variable {φ : ℒ.Fml} {d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}}

  lemma all_finite_tb_either {Γ : Finset (ℒ.Fml)} : ∀φ ∈ (𝐓𝐁 Γ), φ ∈ peano_arithmetic_t ∨ φ ∈ (fml_set syntax_theory) ∨ (∃ψ, ψ ∈ Γ ∧ φ = T(⌜ψ⌝) ⇔ ψ) := sorry

  lemma all_finite_replaced_either {k} {R : ℒₜ.Relations k} {Γ : Finset (ℒ.Fml)} {φ : ℒ.Fml} : ∀ψ ∈ ((𝐓𝐁 Γ)/ₛ[R, φ]), ψ ∈ (peano_arithmetic_t/ₛ[R, φ]) ∨ ψ ∈ ((fml_set syntax_theory)/ₛ[R,φ]) ∨ (∃π, π ∈ Γ ∧ ψ = (@subs_r_for_fml _ _ _ ℒₜ ℒ (T(⌜π⌝) ⇔ (ϕ.onFormula π)) R φ)) := sorry

  variable {L : Language} {Th : Set (Formula L ℕ)}[∀n, DecidableEq (L.Functions n)][∀p, DecidableEq (L.Relations p)]

  variable {ψ : ℒₜ.Fml}

  -- def disquotation_to_phi : ℒₜ.Fml → ℒ.Fml
  --   | (((.rel L_T.Rel.t ts₁ ⟹ f₁) ⟹ ((f₂ ⟹ .rel L_T.Rel.t ts₂) ⟹ ⊥)) ⟹ ⊥) => if Nonempty ϕ.onFormula f = f₁ then f else ⊥
  --   | _ => ⊥

  -- def test : ℒₜ.Fml := (((.rel L_T.Rel.t ![S(zero)] ⟹ (#0 =' #0)) ⟹ ((⊤ ⟹ .rel L_T.Rel.t ![S(zero)]) ⟹ ⊥)) ⟹ ⊥)

  -- #check disquotation_to_phi test
  -- #eval @disquotation_to_phi _ test

  def disquotation_phis (s : Finset (ℒₜ.Fml)) : Finset (ℒ.Fml) := sorry

  -- def fmls : Derivation 𝐓𝐁 Δ Γ → Finset (ℒ.Fml)
  --   | .tax h => (disquotation_phis Δ) ∪ (disquotation_phis Γ)
  --   | .lax h => (disquotation_phis Δ) ∪ (disquotation_phis Γ)
  --   | .left_conjunction _ _ _ d _ _ _ => (fmls d)
  --   | .left_disjunction _ _ _ _ _ d₁ _ d₂ _ _ => (fmls d₁) ∪ (fmls d₂)
  --   | .left_implication _ _ _ _ _ d₁ _ d₂ _ _ => (fmls d₁) ∪ (fmls d₂)
  --   | .left_negation _ _ _ d₁ _ _ => (fmls d₁)
  --   | .left_bot _ => Δ ∪ Γ
  --   | .right_conjunction _ _ _ _ _ d₁ _ d₂ _ _ => (fmls d₁) ∪ (fmls d₂)
  --   | .right_disjunction _ _ _ d _ => (fmls d)
  --   | .right_implication _ _ _ _ _ d _ _ _ => (fmls d)
  --   | .right_negation _ _ _ d₁ _ _ => (fmls d₁)
  --   | .left_forall _ _ _ _ _ d _ _ => (fmls d)
  --   | .left_exists _ _ _ _ d _ => (fmls d)
  --   | .right_forall _ _ _ _ d _ => (fmls d)
  --   | .right_exists _ _ _ _ _ d _ => (fmls d)
  --   | .cut _ _ _ _ _ d₁ d₂ _ _ => (fmls d₁) ∪ (fmls d₂)

  def relevant_disquotation_phis : Derivation 𝐓𝐁 {} {ϕ.onFormula φ} → (Finset (ℒ.Fml)) := sorry

  def finite_disq_th (d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) : Set (ℒₜ.Fml) := 𝐓𝐁 (relevant_disquotation_phis d)

  lemma all_rel_finite_tb_either {d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}} : ∀ψ ∈ (finite_disq_th d), ψ ∈ peano_arithmetic_t ∨ ψ ∈ (fml_set syntax_theory) ∨ (∃π, π ∈ (relevant_disquotation_phis d) ∧ ψ = T(⌜π⌝) ⇔ π) := by
    intro ψ h₁
    apply all_finite_tb_either at ψ
    simp[finite_disq_th] at h₁
    apply ψ at h₁
    exact h₁

  def finite_tb_der (d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) : Derivation (finite_disq_th d) {} {ϕ.onFormula φ} := sorry

  noncomputable def build_tau (d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) : ℒ.Fml := BoundedFormula.finset_iSup (relevant_disquotation_phis d)

  notation "τ" => build_tau

  lemma PAT_replaced_is_PA : 𝐏𝐀𝐓/ₛ[.t, (τ d)] = 𝐏𝐀 := sorry

  open BoundedFormula
  def tau_to_phi {π : ℒ.Fml} {h₁ : π ∈ relevant_disquotation_phis d} : Derivation 𝐏𝐀 ∅ {(τ d)/[⌜π⌝] ⟹ π} := sorry

  noncomputable def phi_to_tau {π : ℒ.Fml} {h₁ : π ∈ relevant_disquotation_phis d} : Derivation 𝐏𝐀 ∅ {π ⟹ (τ d)/[⌜π⌝]} := by
    apply Derivation.right_implication π (τ d/[⌜π⌝]) {π} {(τ d)/[⌜π⌝]} {} _ (by simp) (by simp) (by simp)
    simp[build_tau]
    -- apply Derivation.right_iSup


    sorry

  noncomputable def fml_to_tau_der (π : ℒ.Fml) (h₁ : π ∈ relevant_disquotation_phis d) : Derivation 𝐏𝐀 {} {(τ d)/[⌜π⌝] ⇔ π} := by
    apply Derivation.to_iff tau_to_phi phi_to_tau
    exact h₁
    exact h₁

  lemma all_fml_tau_prov : ∀π ∈ (relevant_disquotation_phis d), 𝐏𝐀 ⊢ ((τ d)/[⌜π⌝] ⇔ π) := by
    intro π h
    simp
    apply Nonempty.intro (fml_to_tau_der π h)


  lemma replace_disq_is_tau {π : ℒ.Fml} : (@subs_r_for_fml ℕ 0 1 ℒₜ ℒ (T(⌜π⌝) ⇔ ϕ.onFormula π) Rel.t (τ d)) = ((τ d)/[⌜π⌝] ⇔ π) := sorry

  lemma all_finite_tb_provable : ∀ψ ∈ ((finite_disq_th d)/ₛ[.t, (τ d)]), 𝐏𝐀 ⊢ ψ := by
    intro ψ h₁
    apply all_finite_replaced_either ψ at h₁
    cases h₁ with
    | inl h₂ =>
      rw[PAT_replaced_is_PA] at h₂
      simp
      apply Nonempty.intro
      apply Derivation.tax
      apply Exists.intro ψ (by simp; exact h₂)
    | inr h₂ =>
      cases h₂ with
      | inl h₃ =>
        /- Problem: syntax_theory is not part of 𝐏𝐀 .-/
        sorry
      | inr h₃ =>
        /- here we should replace (T(⌜π⌝) ⇔ ϕ.onFormula π)/[Rel.t,τ d]
        with Derivation 𝐏𝐀 {} {(tau d)/[⌜π⌝] ⇔ π} using the fact that
        ∀π, Nonempty (Derivation 𝐏𝐀 {} {(tau d)/[⌜π⌝] ⇔ π})
        -/
        simp[replace_disq_is_tau] at h₃
        have step1 : h₃.choose ∈ relevant_disquotation_phis d ∧ ψ = τ d/[⌜h₃.choose⌝] ⇔ h₃.choose := h₃.choose_spec
        have step2 : h₃.choose ∈ relevant_disquotation_phis d := And.left step1
        have step3 : ψ = (τ d)/[⌜h₃.choose⌝] ⇔ h₃.choose := And.right step1
        rw[step3]
        apply all_fml_tau_prov
        exact step2

  noncomputable def finite_tb_to_pa : Derivation ((finite_disq_th d)/ₛ[.t, (build_tau d)]) {} {φ} → Derivation 𝐏𝐀 {} {φ} := by
    intro d₂
    apply Nonempty.intro at d₂
    apply Derivation.derivability_trans at d₂
    have step1 : ∀φ ∈ ((𝐓𝐁 (relevant_disquotation_phis d))/ₛ[.t, (τ d)]), 𝐏𝐀 ⊢ φ := by
      apply all_finite_tb_provable
    apply d₂ at step1
    simp at step1
    apply Classical.choice at step1
    exact step1

  noncomputable def translation {φ: ℒ.Fml} : (Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) → (Derivation 𝐏𝐀 {} {φ}) := by
    intro d
    let tau : ℒ.Fml := build_tau d
    apply finite_tb_der at d
    apply subs_der L_T.Rel.t tau at d
    simp[tau] at d
    apply finite_tb_to_pa at d
    exact d

  lemma all_phi_var_in_pa (h₁ : (ϕ.onFormula φ ∈ 𝐓𝐁)) : φ ∈ 𝐏𝐀 := sorry

  -- def translation_alternative {φ₁ : ℒ.Fml} : (Derivation 𝐓𝐁 {} {ϕ.onFormula φ₁}) → Derivation 𝐏𝐀 {} {φ₁}
  --   | @Derivation.tax ℒₜ _ _ _ _ _ φ₂ h₁ h₂ => by
  --     have step1 : φ₂ = ϕ.onFormula φ₁ := by
  --       sorry
  --     simp[step1] at h₁
  --     have step2 : φ₁ ∈ 𝐏𝐀 := by
  --       apply all_phi_var_in_pa h₁













    --   sorry
    -- | _ => sorry

  theorem conservativity_of_tb : ∀φ : ℒ.Fml, (𝐓𝐁 ⊢ φ) → (𝐏𝐀 ⊢ φ) := by
    simp
    intro φ
    intro h
    apply translation at h
    apply Nonempty.intro h


end Conservativity
