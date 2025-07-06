
import FormalizingAxiomaticTheoriesOfTruth.Syntax

open FirstOrder
open Language

namespace SyntaxAxioms
open Languages
open L_T
open LPA
open BoundedFormula
open TermEncoding

scoped notation "⌜"t"⌝" => LPA.numeral (sentence_term_tonat t)
scoped notation "⌜"φ"⌝" => LPA.numeral (formula_tonat φ)
scoped notation "⌜"t"⌝" => LPA.numeral (term_tonat t)
variable {α : Type*}
def neg_repres (φ : Formula ℒ ℕ) : ℒ.Sentence :=
  (⬝∼ ⌜φ⌝) =' (⌜∼φ⌝)
def conj_repres (φ ψ : Formula ℒ ℕ): ℒ.Sentence :=
  (⌜φ⌝ ⬝∧ ⌜ψ⌝) =' (⌜φ ∧' ψ⌝)
def disj_repres (φ ψ : Formula ℒ ℕ) : ℒ.Sentence :=
  (⌜φ⌝ ⬝∨ ⌜ψ⌝) =' (⌜φ ∨' ψ⌝)
def cond_repres (φ ψ : Formula ℒ ℕ) : ℒ.Sentence :=
  (⌜φ⌝ ⬝⟹ ⌜ψ⌝) =' (⌜φ ⟹ ψ⌝)
def forall_repres (φ : BoundedFormula ℒ ℕ 1) : ℒ.Sentence :=
  (⬝∀ ⌜φ⌝) =' (⌜∀'φ⌝)
def exists_repres (φ : BoundedFormula ℒ ℕ 1) : ℒ.Sentence :=
  (⬝∃ ⌜φ⌝) =' (⌜∃'φ⌝)
def subs_repres (φ : BoundedFormula ℒ ℕ 0) (t : Term ℒ (ℕ ⊕ Fin 0)) : ℒ.Sentence :=
  Subs(⌜φ⌝, ⌜(@Term.var ℒ (ℕ ⊕ Fin 0) (.inl 0))⌝, ⌜t⌝) =' ⌜φ/[t]⌝
def term_repres (φ : Formula ℒ ℕ) : ℒ.Sentence :=
  Trm( ⌜φ⌝ )
def formulaL_repres (φ : Formula ℒ ℕ) : ℒ.Sentence :=
  FormL( ⌜φ⌝ )
def formulaL_T_repres (φ : Formula ℒ ℕ) : ℒ.Sentence :=
  FormLT( ⌜φ⌝ )
def sentenceL_repres (φ : Formula ℒ ℕ) : ℒ.Sentence :=
  SentenceL( ⌜φ⌝ )
def sentenceL_T_respres (φ : Formula ℒ ℕ) : ℒ.Sentence :=
  SentenceLT( ⌜φ⌝ )
def closed_term_repres (t : Term ℒ (ℕ ⊕ Fin 0)) : ℒ.Sentence :=
  ClosedTerm(⌜t⌝)
def var_repres (φ : Formula ℒ ℕ) : ℒ.Sentence :=
  Var( ⌜φ⌝ )
def const_repres (φ : Formula ℒ ℕ) : ℒ.Sentence :=
  Const( ⌜φ⌝ )
def denote_repres (t : Term ℒ (Empty ⊕ Fin 0)) : ℒ.Sentence :=
  ClosedTerm(⌜t⌝) ⟹ ((⬝°(⌜t⌝)) =' t)

end SyntaxAxioms

namespace SyntaxTheory
open Languages
open LPA
open SyntaxAxioms
inductive syntax_theory_l : ℒ.Theory where
  | negation_representation {φ} : syntax_theory_l (neg_repres φ)
  | conjunction_representation {φ ψ} : syntax_theory_l (conj_repres φ ψ)
  | disjunction_representation {φ ψ} : syntax_theory_l (disj_repres φ ψ)
  | conditional_representation {φ ψ} : syntax_theory_l (cond_repres φ ψ)
  | forall_representation {φ} : syntax_theory_l (forall_repres φ)
  | exists_representation {φ} : syntax_theory_l (exists_repres φ)
  | term_representation {φ} : syntax_theory_l (term_repres φ)
  | formula_L_representation {φ} : syntax_theory_l (formulaL_repres φ)
  | formula_L_T_representation {φ} : syntax_theory_l (formulaL_T_repres φ)
  | sentence_L_representation {φ} : syntax_theory_l (sentenceL_repres φ)
  | sentence_L_T_representation {φ} : syntax_theory_l (sentenceL_T_respres φ)
  | closed_term_representation {φ} : syntax_theory_l (closed_term_repres φ)
  | variable_representation {φ} : syntax_theory_l (var_repres φ)
  | constant_representation {φ} : syntax_theory_l (const_repres φ)
  | denote_representation {t} : syntax_theory_l (denote_repres t)

open L_T
def syntax_theory : ℒₜ.Theory := syntax_theory_l
end SyntaxTheory

namespace PA
  open Languages
  open LPA
  open L_T
  open BoundedFormula
  open SyntaxTheory

  /-- Peano arithemtic -/
  inductive peano_axioms : ℒ.Theory where
    | first : peano_axioms (∀' ∼(LPA.null =' S(&0)))
    | second :peano_axioms (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
    | third : peano_axioms (∀' ((&0 add LPA.null) =' &0))
    | fourth : peano_axioms (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
    | fifth : peano_axioms (∀' ((&0 times LPA.null) =' LPA.null))
    | sixth : peano_axioms (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))

  namespace Induction
    variable {L : Language}

    @[simp]
    def term_substitution {n : ℕ} (t : L.Term (Empty ⊕ Fin n)) : L.Term (Fin 1 ⊕ Fin n) → L.Term (Empty ⊕ Fin n)
    | .var v => 
      match v with
      | .inl (.mk 0 _) => t
      | .inr m => Term.var (.inr m)
    | .func f ts => .func f (fun i => term_substitution t (ts i))

    @[simp]
    def up_bv_empty {n : ℕ} : L.Term (Empty ⊕ Fin n) → L.Term (Empty ⊕ Fin (n + 1))
    | .var v => 
      match v with
      | .inl m => 
        .var (.inl m)
      | .inr m => .var (.inr (to_extra_fin m))
    | .func f ts => .func f (fun i => up_bv_empty (ts i))

    @[simp]
    def up_bv_fin_1 {n : ℕ} : L.Term (Fin 1 ⊕ Fin n) → L.Term (Fin 1 ⊕ Fin (n + 1))
    | .var v => 
      match v with
      | .inl m => 
        .var (.inl m)
      | .inr m => .var (.inr (to_extra_fin m))
    | .func f ts => .func f (fun i => up_bv_fin_1 (ts i))

    @[simp]
    def formula_substitution : {n : ℕ} → (t : L.Term (Empty ⊕ Fin n)) → L.BoundedFormula (Fin 1) n → L.BoundedFormula Empty n
    | _, _, .falsum => .falsum
    | _, t, .equal t₁ t₂ => .equal (term_substitution t t₁) (term_substitution t t₂)
     | _, t, .rel R ts => .rel R (fun i => term_substitution t (ts i))
     | _, t, .imp φ ψ => .imp (formula_substitution t φ) (formula_substitution t ψ)
     | _, t, .all φ => .all (formula_substitution (up_bv_empty t) φ)
  
  scoped notation φ"/[" t "]" => formula_substitution t φ

  @[simp]
  def bv_term_substitution {n : ℕ} (t : L.Term (Empty ⊕ Fin (n + 1))) : L.Term (Fin 1 ⊕ Fin n) → L.Term (Empty ⊕ Fin (n + 1))
  | .var v => 
    match v with
    | .inl (.mk 0 _) => t
    | .inr m => up_bv_empty (Term.var (.inr m))
  | .func f ts => .func f (fun i => term_substitution t (up_bv_fin_1 (ts i)))

  @[simp]
  def bv_formula_substitution : {n : ℕ} → (t : L.Term (Empty ⊕ Fin (n + 1))) → L.BoundedFormula (Fin 1) n → L.BoundedFormula Empty (n + 1)
  | _, _, .falsum => .falsum
  | _, t, .equal t₁ t₂ => .equal (bv_term_substitution t t₁) (bv_term_substitution t t₂)
  | _, t, .rel R ts => .rel R (fun i => term_substitution t (up_bv_fin_1 (ts i)))
  | _, t, .imp φ ψ => .imp (bv_formula_substitution t φ) (bv_formula_substitution t ψ)
  | _, t, .all φ => .all (bv_formula_substitution (up_bv_empty t) φ)

  scoped notation φ"/bv["t"]" => bv_formula_substitution t φ

  def φ1 : ℒ.Formula (Fin 1) := #0 =' LPA.null
  def t1 : ℒ.Term (Empty ⊕ Fin 0) := LPA.null
  def ψ1 : ℒ.Sentence := LPA.null =' LPA.null

  example : φ1/[t1] = ψ1 := by
    simp[φ1,t1,ψ1,LPA.null,Term.bdEqual,Matrix.empty_eq]

  def φ2 : ℒ.Formula (Fin 1) := #0 =' LPA.null
  def t2 : ℒ.Term (Empty ⊕ Fin 1) := &0
  def ψ2 : ℒ.BoundedFormula Empty 1 := (&0) =' LPA.null

  example : φ2/bv[t2] = ψ2 := by
    simp[φ2,t2,ψ2,LPA.null,Term.bdEqual,Matrix.empty_eq]

  

  end Induction

  open Induction
  def peano_arithmetic : ℒ.Theory := peano_axioms ∪ {φ : ℒ.Sentence | ∃ψ : ℒ.Formula (Fin 1), φ = (ψ/[LPA.null] ∧' (∀'(ψ/bv[&0] ⟹ ψ/bv[S(&0)]))) ⟹ ∀'ψ/bv[&0]} ∪ syntax_theory_l
  
  notation "𝐏𝐀" => peano_arithmetic

end PA

namespace PAT
open Languages
  open PA
  open L_T
  open SyntaxTheory
  open BoundedFormula
  open Induction
  def pat : ℒₜ.Theory := peano_axioms ∪ {φ : ℒₜ.Sentence | ∃ψ : ℒₜ.Formula (Fin 1), φ = ψ/[L_T.null] ∧' ∀'(ψ/bv[&0] ⟹ ψ/bv[S(&0)]) ⟹ ∀'ψ/bv[&0]} ∪ syntax_theory

  notation "𝐏𝐀𝐓" => pat
end PAT

namespace TB
open Languages

open L_T
open LPA
open PAT
open SyntaxTheory
open TermEncoding

  def sentence_encoding (s : ℒ.Sentence) : ℒₜ.Term (Empty ⊕ Fin 0) := L_T.numeral (Encodable.encodeList (BoundedFormula.listEncode s))
  scoped notation "⌜"φ"⌝" => sentence_encoding φ 
  def tarski_biconditionals : ℒₜ.Theory := 𝐏𝐀𝐓 ∪ {φ | ∃ψ : ℒ.Sentence, φ = T(⌜ψ⌝) ⇔ ψ} 

notation "𝐓𝐁" => tarski_biconditionals
end TB
