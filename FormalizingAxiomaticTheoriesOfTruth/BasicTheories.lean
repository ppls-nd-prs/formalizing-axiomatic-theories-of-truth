import FormalizingAxiomaticTheoriesOfTruth.Syntax
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Semantics

open FirstOrder
open Language

variable {L : Language}[∀α n, Encodable (L.Term (α ⊕ Fin n))][∀α n, Encodable (L.BoundedFormula α n)]
notation "⌜"t"⌝" => numeral (Encodable.encode t)

namespace SyntaxAxioms
open Languages L_T LPA BoundedFormula

variable {L : Language}[SyntaxTheoretical L][Arithmetical L][∀α n, Encodable (L.Term (α ⊕ Fin n))][∀α n, Encodable (L.BoundedFormula α n)]

variable {α : Type*}
def neg_repres (φ : Formula L α) : L.Sentence :=
  (⬝∼ ⌜φ⌝) =' (⌜∼φ⌝)
def conj_repres (φ ψ : Formula L α): L.Sentence :=
  (⌜φ⌝ ⬝∧ ⌜ψ⌝) =' (⌜φ ⊔ ψ⌝)
def disj_repres (φ ψ : Formula L α) : L.Sentence :=
  (⌜φ⌝ ⬝∨ ⌜ψ⌝) =' (⌜φ ⊓ ψ⌝)
def cond_repres (φ ψ : Formula L α) : L.Sentence :=
  (⌜φ⌝ ⬝⟹ ⌜ψ⌝) =' (⌜φ ⟹ ψ⌝)
def forall_repres (φ : BoundedFormula L α 1) : L.Sentence :=
  (⬝∀ ⌜φ⌝) =' (⌜∀'φ⌝)
def exists_repres (φ : BoundedFormula L α 1) : L.Sentence :=
  (⬝∃ ⌜φ⌝) =' (⌜∃'φ⌝)
def subs_repres (φ : L.Term (α ⊕ Fin 0) → BoundedFormula L α 0) (fv : α) (t : Term L (α ⊕ Fin 0)) : L.Sentence :=
  Subs(⌜φ (#fv)⌝, ⌜(@Term.var L (α ⊕ Fin 0) (.inl fv))⌝, ⌜t⌝) =' ⌜φ t⌝
def term_repres (φ : Formula L α) : L.Sentence :=
  Trm( ⌜φ⌝ )
def formulaL_repres (φ : Formula L α) : L.Sentence :=
  FormL( ⌜φ⌝ )
def formulaL_T_repres (φ : Formula L α) : L.Sentence :=
  FormLT( ⌜φ⌝ )
def sentenceL_repres (φ : Formula L α) : L.Sentence :=
  SentenceL( ⌜φ⌝ )
def sentenceL_T_respres (φ : Formula L α) : L.Sentence :=
  SentenceLT( ⌜φ⌝ )
def closed_term_repres (t : L.Term (α ⊕ Fin 0)) : L.Sentence :=
  ClosedTerm(⌜t⌝)
def var_repres (φ : Formula L α) : L.Sentence :=
  Var( ⌜φ⌝ )
def const_repres (φ : Formula L α) : L.Sentence :=
  Const( ⌜φ⌝ )
def denote_repres (t : L.Term (Empty ⊕ Fin 0)) : L.Sentence :=
  ClosedTerm(⌜t⌝) ⟹ ((⬝°(⌜t⌝)) =' t)

end SyntaxAxioms

namespace SyntaxTheory
open Languages
open LPA
open SyntaxAxioms

variable {L : Language}[SyntaxTheoretical L][Arithmetical L][∀α n, Encodable (L.Term (α ⊕ Fin n))][∀α n, Encodable (L.BoundedFormula α n)]
inductive syntax_theory : L.Theory where
  | negation_representation {φ} : syntax_theory (neg_repres φ)
  | conjunction_representation {φ ψ} : syntax_theory (conj_repres φ ψ)
  | disjunction_representation {φ ψ} : syntax_theory (disj_repres φ ψ)
  | conditional_representation {φ ψ} : syntax_theory (cond_repres φ ψ)
  | forall_representation {φ} : syntax_theory (forall_repres φ)
  | exists_representation {φ} : syntax_theory (exists_repres φ)
  | term_representation {φ} : syntax_theory (term_repres φ)
  | formula_L_representation {φ} : syntax_theory (formulaL_repres φ)
  | formula_L_T_representation {φ} : syntax_theory (formulaL_T_repres φ)
  | sentence_L_representation {φ} : syntax_theory (sentenceL_repres φ)
  | sentence_L_T_representation {φ} : syntax_theory (sentenceL_T_respres φ)
  | closed_term_representation {φ} : syntax_theory (closed_term_repres φ)
  | variable_representation {φ} : syntax_theory (var_repres φ)
  | constant_representation {φ} : syntax_theory (const_repres φ)
  | denote_representation {t} : syntax_theory (denote_repres t)

open L_T
end SyntaxTheory

namespace Induction
open BoundedFormula

instance : Coe (L.BoundedFormula (Fin 1) 0) (L.BoundedFormula Empty (0 + 1)) where
coe := (fun bf => relabel (fun i : Fin 1 => .inr i) bf)

variable {L : Language}[Arithmetical L]
def ind (φ : L.Formula (Fin 1)) : L.Sentence :=
  ((φ.subst ![null]) ⊓ (∀'(φ ⟹ (Coe.coe (@subst _ (Fin 1) (Fin 1) 0 φ (fun _ : Fin 1 => S(.var 0)))))) ⟹ ∀'φ)

end Induction

namespace PA
  open Languages LPA L_T BoundedFormula SyntaxTheory Induction
  variable {L : Language}[Arithmetical L]
  /-- Peano arithemtic -/
  inductive peano_axioms : L.Theory where
    | first : peano_axioms (∀' ∼(null =' S(&0)))
    | second :peano_axioms (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
    | third : peano_axioms (∀' ((&0 add null) =' &0))
    | fourth : peano_axioms (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
    | fifth : peano_axioms (∀' ((&0 mult null) =' null))
    | sixth : peano_axioms (∀' ∀' ((&1 mult S(&0)) =' ((&1 mult &0)) add &1))
    | induction (ψ : L.Formula (Fin 1)) : peano_axioms (ind ψ)

  def pa : ℒ.Theory := peano_axioms

  notation "𝐏𝐀" => pa

  open Theory


  lemma PA.succ_ne_zero : ∀t : ℒ.Term (Empty ⊕ Fin 0), 𝐏𝐀 ⊨ᵇ ∼(S(t) =' null : ℒ.Sentence) := by
    intro t
    have pa_first : 𝐏𝐀 ⊨ᵇ ((∀' ∼(null =' S(&0))) : ℒ.Sentence) := by
      apply models_sentence_of_mem
      unfold pa
      apply peano_axioms.first

    have pa_first_base : 𝐏𝐀 ⊨ᵇ (∼(null =' (S(null))) : ℒ.Sentence) := by
      apply models_sentence_iff.mpr
      intro M
      apply models_sentence_iff.mp at pa_first
      have realization : ↑M ⊨ (∀'∼(null =' S((var ∘ Sum.inr) 0)) : ℒ.Sentence) := by
        exact pa_first M
      apply realize_all.mp at realization
      simp[Matrix.empty_eq] at realization
      apply realize_not.mpr
      simp only [realize_bdEqual]
      simp [Matrix.empty_eq]
      have ex : ∃a : ↑M, @Structure.funMap ℒ _ _ _ Arithmetical.zero_symbol ![] = a := by
        simp
      have a_realization := realization ex.choose
      simp [ex.choose_spec.symm,Fin.snoc] at a_realization
      exact a_realization

    have pa_first_is : 𝐏𝐀 ⊨ᵇ ((∀' (∼(null =' S(&0)) ⟹ (∼(null =' S(S(&0)))))) : ℒ.Sentence) := by
      apply models_sentence_iff.mpr
      intro M
      apply realize_all.mpr
      intro a
      apply realize_imp.mpr
      intro h₁
      apply realize_not.mpr
      simp [(realize_bdEqual _ _),Matrix.empty_eq]
      apply models_sentence_iff.mp at pa_first
      have realization := pa_first M
      apply realize_all.mp at realization
      have ex : ∃b : ↑M, b = @Structure.funMap ℒ _ _ _ Arithmetical.succ_symbol ![a] := by
        simp
      have b_realization := realization ex.choose
      simp[Matrix.empty_eq,Fin.snoc,Matrix.vec_single_eq_const] at b_realization
      simp [Fin.snoc]
      exact b_realization

    let ψ : ℒ.Formula (Fin 1) := (∼(null =' S(#0)))
    have ind : 𝐏𝐀 ⊨ᵇ ind ψ := by
      apply models_sentence_of_mem
      apply peano_axioms.induction ψ

    have forall_succ_ne_zero : 𝐏𝐀 ⊨ᵇ (∀'(∼(null =' &0)) : ℒ.Sentence) := by
      unfold Induction.ind at ind

      sorry

    unfold Induction.ind at ind

    apply models_sentence_iff.mp at ind
    apply models_sentence_iff.mpr

    intro M
    apply ind at M
    apply realize_imp.mp at M



    apply models_sentence_iff.mpr
    intro M
    apply models_sentence_iff.mp at pa_first
    apply pa_first at M
    apply realize_all.mp at M
    apply realize_not.mpr
    simp [(realize_bdEqual _ _),Term.realize_func,Matrix.empty_eq]
    simp [realize_not,Matrix.empty_eq,Fin.snoc] at M





    sorry

  lemma neq_terms_neq_realize : ∀n m : Nat, @numeral Empty ℒ _ n ≠ numeral m → 𝐏𝐀 ⊨ᵇ (∼(@numeral (Empty ⊕ Fin 0) ℒ _ n =' numeral m)) := by
    intro n m h₁
    have first_ax : 𝐏𝐀 ⊨ᵇ ((∀' ∼(null =' S(&0))) : ℒ.Sentence) := by
      apply models_sentence_of_mem
      unfold pa
      apply Or.intro_left
      apply peano_axioms.first

    induction n with
    | zero =>
      cases m with
      | zero =>
        contradiction
      | succ p =>

        sorry
    | succ n ih => sorry

end PA

namespace PAT
open Languages PA L_T SyntaxTheory BoundedFormula Induction

def pat : ℒₜ.Theory := peano_axioms ∪ {φ | ∃ψ, φ = ind ψ}
notation "𝐏𝐀𝐓" => pat

end PAT

namespace TB
open Languages L_T LPA PAT SyntaxTheory

variable [Encodable (ℒ.Sentence)]
def tarski_biconditional (ψ : ℒ.Sentence) : ℒₜ.Sentence := .rel L_T.Rel.t_symbol ![⌜ψ⌝] ⇔ ψ
def tb : ℒₜ.Theory := 𝐏𝐀𝐓 ∪ {φ | ∃ψ : ℒ.Sentence, φ = (tarski_biconditional ψ)}

notation "𝐓𝐁" => tb

end TB
