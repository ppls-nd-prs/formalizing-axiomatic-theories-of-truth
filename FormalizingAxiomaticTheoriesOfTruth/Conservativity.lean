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
  lemma subs_empty_is_empty {R : ℒₜ.Relations k} {φ : ℒ.Fml} : ∅/[R,φ] = ∅ :=   sorry
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

  lemma all_finite_tb_either {Γ : Finset (ℒ.Fml)} : ∀φ ∈ (𝐓𝐁 Γ), φ ∈ peano_arithmetic_t ∨ φ ∈ (fml_set syntax_theory) ∨ (∃ψ, ψ ∈ Γ ∧ φ = T(⌜ψ⌝) ⇔ ψ) := sorry

  lemma all_finite_replaced_either {k} {R : ℒₜ.Relations k} {Γ : Finset (ℒ.Fml)} {φ : ℒ.Fml} : ∀ψ ∈ ((𝐓𝐁 Γ)/ₛ[R, φ]), ψ ∈ (peano_arithmetic_t/ₛ[R, φ]) ∨ ψ ∈ ((fml_set syntax_theory)/ₛ[R,φ]) ∨ (∃π, π ∈ Γ ∧ ψ = (@subs_r_for_fml _ _ _ ℒₜ ℒ (T(⌜π⌝) ⇔ (ϕ.onFormula π)) R φ)) := sorry

  def relevant_disquotation_phis {φ : ℒ.Fml} (d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) : Finset (ℒ.Fml) := sorry

  def finite_disq_th {φ : ℒ.Fml} (d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) : Set (ℒₜ.Fml) := 𝐓𝐁 (relevant_disquotation_phis d)

  lemma all_rel_finite_tb_either {φ : ℒ.Fml} {d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}} : ∀ψ ∈ (finite_disq_th d), ψ ∈ peano_arithmetic_t ∨ ψ ∈ (fml_set syntax_theory) ∨ (∃π, π ∈ (relevant_disquotation_phis d) ∧ ψ = T(⌜π⌝) ⇔ π) := by
    intro ψ h₁
    apply all_finite_tb_either at ψ
    simp[finite_disq_th] at h₁
    apply ψ at h₁
    exact h₁

  def finite_tb_der {φ : ℒ.Fml} (d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) : Derivation (finite_disq_th d) {} {ϕ.onFormula φ} := sorry

  def build_tau {φ : ℒ.Fml} (d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) : ℒ.Fml := sorry
  notation "τ" => build_tau

  lemma all_finite_tb_provable {φ : ℒ.Fml} {d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}} : ∀ψ ∈ ((finite_disq_th d)/ₛ[.t, (τ d)]), 𝐏𝐀 ⊢ ψ := by
    intro ψ h₁
    apply all_finite_replaced_either ψ at h₁
    cases h₁ with
    | inl h₂ =>
      sorry
    | inr h₂ =>
      cases h₂ with
      | inl h₃ =>

        sorry
      | inr h₃ =>

        sorry

  noncomputable def finite_tb_to_pa {φ : ℒ.Fml} {d₁ : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}} : Derivation ((finite_disq_th d₁)/ₛ[.t, (build_tau d₁)]) {} {φ} → Derivation 𝐏𝐀 {} {φ} := by
    intro d
    apply Nonempty.intro at d
    apply derivability_trans at d
    have step1 : ∀φ ∈ ((𝐓𝐁 (relevant_disquotation_phis d₁))/ₛ[.t, (τ d₁)]), 𝐏𝐀 ⊢ φ := by
      apply all_finite_tb_provable
    apply d at step1
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

  theorem conservativity_of_tb : ∀φ : ℒ.Fml, (𝐓𝐁 ⊢ φ) → (𝐏𝐀 ⊢ φ) := by
    simp
    intro φ
    intro h
    apply translation at h
    apply Nonempty.intro h


end Conservativity
