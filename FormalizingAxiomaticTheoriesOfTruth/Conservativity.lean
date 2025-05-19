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

  def subs_r_for_fml {k : ℕ} {L₁ L₂ : Language} : ℒₜ.Fml → ℒₜ.Relations k → ℒ.Fml → ℒ.Fml :=
    sorry

  def subs_r_for_fml_in_set {k : ℕ} : Set (ℒₜ.Fml) → ℒₜ.Relations k → ℒ.Fml → Set (ℒ.Fml) :=
    sorry

  def subs_r_for_fml_in_finset {k : ℕ} : Finset (ℒₜ.Fml) → ℒₜ.Relations k → ℒ.Fml → Finset (ℒ.Fml) :=
    sorry

  notation Γ"/ₛ["R","φ"]" => subs_r_for_fml_in_set Γ R φ
  notation Γ"/["R","φ"]" => subs_r_for_fml_in_finset Γ R φ

  def subs_der {Th : Set (ℒₜ.Fml)} {Γ Δ : Finset (ℒₜ.Fml)} {k : ℕ} (R : ℒₜ.Relations k) (φ : ℒ.Fml) (d : Derivation Th Γ Δ) : Derivation (Th/ₛ[R,φ]) (Γ/[R,φ]) (Δ/[R,φ]) :=
    sorry

  open PAT
  open SyntaxTheory
  open TermEncoding
  inductive restricted_tb (Γ : Finset (ℒ.Fml)) : Set (ℒₜ.Formula ℕ) where
  | pat_axioms {φ} : peano_arithmetic_t φ → restricted_tb Γ φ
  | syntax_axioms {φ} : syntax_theory φ → restricted_tb Γ φ
  | disquotation {φ} {h : φ ∈ Γ} : restricted_tb Γ (T(⌜φ⌝) ⇔ φ)

  notation "𝐓𝐁 " Γ => restricted_tb Γ

  def relevant_disquotation_phis {φ : ℒ.Fml} (d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) : Finset (ℒ.Fml) := sorry

  def build_tau (Γ : Finset (ℒ.Fml)) : ℒ.Fml := sorry
  abbrev τ := build_tau

  def translate_to_l_set (Γ : Finset (ℒ.Fml)) : Set (ℒ.Fml) := (𝐓𝐁 Γ)/ₛ[.t, (τ Γ)]

  lemma pa_proves_finite_proof {Γ} : ∀φ ∈ (𝐓𝐁 Γ)/ₛ[L_T.Rel.t, (build_tau Γ)], 𝐏𝐀 ⊢ φ := sorry

  def tb_to_finite_tb {φ : ℒ.Fml} (d : Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) : Derivation (𝐓𝐁 (relevant_disquotation_phis d)) {} {ϕ.onFormula φ} := sorry

  def finite_tb_to_pa {φ} {Γ : Finset (ℒ.Fml)} : Derivation ((𝐓𝐁 Γ)/ₛ[.t, (build_tau Γ)]) ({}/[.t, (build_tau Γ)]) ({ϕ.onFormula φ}/[.t, (build_tau Γ)]) → Derivation 𝐏𝐀 {} {φ} := by
    sorry

  def translation {φ: ℒ.Fml} : (Derivation 𝐓𝐁 {} {ϕ.onFormula φ}) → (Derivation 𝐏𝐀 {} {φ}) := by
    intro d
    let tau : ℒ.Fml := build_tau (relevant_disquotation_phis d)
    apply tb_to_finite_tb at d
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
