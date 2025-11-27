import FormalizingAxiomaticTheoriesOfTruth.Syntax
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Semantics

open FirstOrder
open Language

variable {L : Language}[∀α n, Encodable (L.Term (α ⊕ Fin n))][∀α n, Encodable (L.BoundedFormula α n)][Arithmetical L]
def term_encoding_1 {α n} : L.BoundedFormula α n → (L.Term (Empty ⊕ Fin 0)) := numeral ∘ Encodable.encode
def term_encoding_2 {α n} : L.Term (α ⊕ Fin n) → (L.Term (Empty ⊕ Fin 0)) := numeral ∘ Encodable.encode

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


  open Theory BoundedFormula
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

def alt_PA : ℒₜ.Theory := {φ | φ ∈ tb ∧ ¬contains_T φ}

notation "𝐓𝐁" => tb
notation "𝐏𝐀" => alt_PA

open Theory BoundedFormula PA
  lemma eq_symm : ∀{t₁ t₂ : ℒₜ.Term (Empty ⊕ Fin 0)}, 𝐏𝐀 ⊨ᵇ (t₁ =' t₂) ↔ 𝐏𝐀 ⊨ᵇ (t₂ =' t₁) := by
    intro t₁ t₂
    apply Iff.intro
    --mp
    simp[models_sentence_iff]
    intro h₁
    intro M
    apply (realize_bdEqual _ _).mpr
    symm
    apply h₁ at M
    exact (realize_bdEqual _ _).mp M
    --mpr
    simp[models_sentence_iff]
    intro h₁
    intro M
    apply (realize_bdEqual _ _).mpr
    symm
    apply h₁ at M
    exact (realize_bdEqual _ _).mp M

  lemma all_nums : ∀n m : Nat, n ≠ m → 𝐏𝐀 ⊨ᵇ (∼(numeral (n) =' (numeral m)) : ℒₜ.Sentence) := by
    intro n m h₁
    match n, m with
    | .zero, .zero =>
      simp at h₁
    | .zero, .succ n₁ =>
      apply models_sentence_iff.mpr
      intro M
      apply realize_not.mpr
      simp

      unfold alt_PA at M
      unfold TB.tb at M
      unfold PAT.pat at M


      have first : ↑M ⊨ ((∀' ∼(null =' S(&0))) : ℒₜ.Sentence) := by
        apply Theory.models_sentence_of_mem
        simp
        apply And.intro
        apply Or.intro_left
        apply Or.intro_left
        apply peano_axioms.first
        intro h
        simp only [Term.bdEqual,contains_T] at h

      apply realize_all.mp at first
      have step := first (Term.realize (Sum.elim default default : (Empty ⊕ Fin 0 → ↑M)) (numeral n₁ : ℒₜ.Term (Empty ⊕ Fin 0)))
      simp[Fin.snoc,Matrix.empty_eq] at step
      simp[Matrix.empty_eq]
      exact step

    | .succ n₁, .zero =>
      apply models_sentence_iff.mpr
      intro M
      apply realize_not.mpr
      simp

      have first : ↑M ⊨ ((∀' ∼(null =' S(&0))) : ℒ.Sentence) := by
        apply models_sentence_of_mem peano_axioms.first

      apply realize_all.mp at first
      have step := first (Term.realize (Sum.elim default default : (Empty ⊕ Fin 0 → ↑M)) (numeral n₁ : ℒ.Term (Empty ⊕ Fin 0)))
      simp[Fin.snoc,Matrix.empty_eq] at step
      simp[Matrix.empty_eq]
      intro h₂
      exact step h₂.symm

    | .succ n₁, .succ n₂ =>
      have step1 : n₁ ≠ n₂ := by
        revert h₁
        simp
      apply models_sentence_iff.mpr
      intro M
      have second : ↑M ⊨ ((∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0))): ℒₜ.Sentence) := by apply models_sentence_of_mem peano_axioms.second
      apply realize_not.mpr
      simp[(realize_bdEqual _ _),Matrix.empty_eq]
      have step2 : ↑M ⊨ (∼(numeral n₁ =' numeral n₂) : ℒ.Sentence) := by
        apply all_nums n₁ n₂ step1
      apply realize_all.mp at second
      have second_a₁ := second (Term.realize (Sum.elim default ![]) (numeral n₂ : ℒ.Term (Empty ⊕ Fin 0)))
      apply realize_all.mp at second_a₁
      have second_a₁a₂ := second_a₁ (Term.realize (Sum.elim default ![]) (numeral n₁ : ℒ.Term (Empty ⊕ Fin 0)))
      simp[Fin.snoc] at second_a₁a₂
      intro h₂
      apply second_a₁a₂ at h₂
      apply realize_not.mp at step2
      simp[realize_bdEqual _ _,Matrix.empty_eq] at step2
      contradiction

  variable [Encodable ℒ.Sentence]

  lemma all_fs : ∀φ₁ φ₂ : ℒ.Sentence, φ₁ ≠ φ₂ → 𝐏𝐀 ⊨ᵇ (∼(⌜φ₁⌝ =' ⌜φ₂⌝): ℒ.Sentence) := by
    intro φ₁ φ₂ h₁
    apply models_sentence_iff.mpr
    intro M
    apply realize_not.mpr
    intro h₂
    apply (realize_bdEqual _ _).mp at h₂

    have step1 : ↑M ⊨ (∼((numeral (Encodable.encode φ₁)) =' (numeral (Encodable.encode φ₂))): ℒ.Sentence) := by
      apply all_nums (Encodable.encode φ₁) (Encodable.encode φ₂)
      simp[h₁,Encodable.encode_inj]

    apply realize_not.mp at step1
    simp[realize_bdEqual _ _] at step1
    contradiction

  lemma PA.succ_ne_zero : ∀{t : ℒ.Term (Empty ⊕ Fin 0)}, 𝐏𝐀 ⊨ᵇ ∼(S(t) =' null : ℒ.Sentence) := by
    intro t
    have pa_first : 𝐏𝐀 ⊨ᵇ ((∀' ∼(null =' S(&0))) : ℒ.Sentence) := by
      apply models_sentence_of_mem
      unfold pa
      apply peano_axioms.first

    match t with
    | .var (.inl v) => contradiction
    | .var (.inr (.mk val isLt)) => contradiction
    | .func f ts =>
      apply models_sentence_iff.mpr
      intro M
      apply realize_not.mpr
      simp [Matrix.empty_eq]
      apply models_sentence_iff.mp at pa_first
      have realization := pa_first M
      apply realize_all.mp at realization
      simp [Matrix.empty_eq,Fin.snoc] at M
      have ex : ∃a : ↑M, (Structure.funMap f fun i ↦ Term.realize (Sum.elim default ![]) (ts i)) = a := by
        simp
      have a_realization := realization ex.choose
      simp [Matrix.empty_eq,Fin.snoc] at a_realization
      intro h₂
      apply a_realization
      exact h₂.symm

  lemma merp : ∀{t : ℒ.Term (Empty ⊕ Fin 0)}, 𝐏𝐀 ⊨ᵇ ∼(null =' S(t) : ℒ.Sentence) := by
    intro t
    apply PA.succ_ne_zero at t
    #check (eq_symm).mp
    sorry


end TB
