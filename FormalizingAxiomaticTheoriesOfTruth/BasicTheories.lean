import FormalizingAxiomaticTheoriesOfTruth.Syntax

open FirstOrder
open Language

namespace SyntaxAxioms
open Languages
open L_T
open LPA
open BoundedFormula
open TermEncoding

scoped notation "⌜"φ"⌝" => LPA.numeral (formula_tonat φ)
scoped notation "⌜"t"⌝" => LPA.numeral (term_tonat t)
def neg_repres (φ : Formula ℒ ℕ) : Formula ℒ ℕ :=
  (⬝∼ ⌜φ⌝) =' (⌜∼φ⌝)
def conj_repres (φ ψ : Formula ℒ ℕ): Formula ℒ ℕ :=
  (⌜φ⌝ ⬝∧ ⌜ψ⌝) =' (⌜φ ∧' ψ⌝)
def disj_repres (φ ψ : Formula ℒ ℕ) : Formula ℒ ℕ :=
  (⌜φ⌝ ⬝∨ ⌜ψ⌝) =' (⌜φ ∨' ψ⌝)
def cond_repres (φ ψ : Formula ℒ ℕ) : Formula ℒ ℕ :=
  (⌜φ⌝ ⬝⟹ ⌜ψ⌝) =' (⌜φ ⟹ ψ⌝)
def forall_repres (φ : BoundedFormula ℒ ℕ 1) : Formula ℒ ℕ :=
  (⬝∀ ⌜φ⌝) =' (⌜∀'φ⌝)
def exists_repres (φ : BoundedFormula ℒ ℕ 1) : Formula ℒ ℕ :=
  (⬝∃ ⌜φ⌝) =' (⌜∃'φ⌝)
def subs_repres (φ : BoundedFormula ℒ ℕ 0) (t : Term ℒ (ℕ ⊕ Fin 0)) : Formula ℒ ℕ :=
  Subs(⌜φ⌝, ⌜(@Term.var ℒ (ℕ ⊕ Fin 0) (.inl 0))⌝, ⌜t⌝) =' ⌜φ////[t]⌝
def term_repres (φ : Formula ℒ ℕ) : Formula ℒ ℕ :=
  Trm( ⌜φ⌝ )
def formulaL_repres (φ : Formula ℒ ℕ) : Formula ℒ ℕ :=
  FormL( ⌜φ⌝ )
def formulaL_T_repres (φ : Formula ℒ ℕ) : Formula ℒ ℕ :=
  FormLT( ⌜φ⌝ )
def sentenceL_repres (φ : Formula ℒ ℕ) : Formula ℒ ℕ :=
  SentenceL( ⌜φ⌝ )
def sentenceL_T_respres (φ : Formula ℒ ℕ) : Formula ℒ ℕ :=
  SentenceLT( ⌜φ⌝ )
def closed_term_repres (t : Term ℒ (ℕ ⊕ Fin 0)) : Formula ℒ ℕ :=
  ClosedTerm(⌜t⌝)
def var_repres (φ : Formula ℒ ℕ) : Formula ℒ ℕ :=
  Var( ⌜φ⌝ )
def const_repres (φ : Formula ℒ ℕ) : Formula ℒ ℕ :=
  Const( ⌜φ⌝ )
def denote_repres (t : Term ℒ (ℕ ⊕ Fin 0)) : Formula ℒ ℕ :=
  ClosedTerm(⌜t⌝) ⟹ ((⬝°(⌜t⌝)) =' t)

end SyntaxAxioms

namespace SyntaxTheory
open Languages
open LPA
open SyntaxAxioms
inductive syntax_theory_l : Set (ℒ.Formula ℕ) where
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
def syntax_theory : Set (ℒₜ.Formula ℕ) := syntax_theory_l.image ϕ.onFormula
end SyntaxTheory

namespace PA
  open Languages
  open LPA
  open L_T
  open BoundedFormula
  open SyntaxTheory

  /-- Peano arithemtic -/
  inductive peano_axioms : Set (ℒ.Formula ℕ) where
    | first : peano_axioms (∀' ∼(LPA.null =' S(&0)))
    | second :peano_axioms (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
    | third : peano_axioms (∀' ((&0 add LPA.null) =' &0))
    | fourth : peano_axioms (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
    | fifth : peano_axioms (∀' ((&0 times LPA.null) =' LPA.null))
    | sixth : peano_axioms (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))

  def peano_arithmetic : Set (ℒ.Formula ℕ) := peano_axioms ∪ {φ : ℒ.Formula ℕ | ∃ψ : ℒ.Formula ℕ, φ = ∼(ψ////[LPA.null] ⟹ (∼(∀'(ψ////bv[&0] ⟹ ψ////bv[S(&0)])))) ⟹ ∀'ψ////bv[&0]} ∪ syntax_theory_l
  
  notation "𝐏𝐀" => peano_arithmetic

end PA

namespace PAT
open Languages
  open PA
  open L_T
  open SyntaxTheory
  
  def pat : Set (ℒₜ.Formula ℕ) := (peano_axioms.image ϕ.onFormula) ∪ {φ : ℒₜ.Formula ℕ | ∃ψ : ℒₜ.Formula ℕ, φ = ∼(ψ////[L_T.null] ⟹ (∼(∀'(ψ////bv[&0] ⟹ ψ////bv[S(&0)])))) ⟹ ∀'ψ////bv[&0]} ∪ syntax_theory

  notation "𝐏𝐀𝐓" => pat
end PAT

namespace TB
open Languages

open L_T
open LPA
open PAT
open SyntaxTheory
open TermEncoding

  def tarski_biconditionals : Set (ℒₜ.Formula ℕ) := 𝐏𝐀𝐓 ∪ {φ | ∃ψ : ℒ.Formula ℕ, φ = T(⌜ψ⌝) ⇔ ψ} 

notation "𝐓𝐁" => tarski_biconditionals
end TB
