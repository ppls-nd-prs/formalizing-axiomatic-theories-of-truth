
import FormalizingAxiomaticTheoriesOfTruth.Syntax

open FirstOrder
open Language

namespace SyntaxAxioms
open Languages
open L_T
open LPA
open BoundedFormula

variable [∀α n, Encodable (ℒ.Term (α ⊕ Fin n))][∀α n, Encodable (ℒ.BoundedFormula α n)]
scoped notation "⌜"t"⌝" => numeral (Encodable.encode t)

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

variable [∀α n, Encodable (ℒ.Term (α ⊕ Fin n))][∀α n, Encodable (ℒ.BoundedFormula α n)]
scoped notation "⌜"t"⌝" => numeral (Encodable.encode t)

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

namespace Induction
open BoundedFormula

variable {L : Language}[Arithmetic L]
def ind {φ : {n : ℕ} →  L.Term (Empty ⊕ Fin n) → L.BoundedFormula Empty n} : L.Sentence :=
  ((φ (null) ∧' (∀'((φ (&0)) ⟹ φ (S(&0))))) ⟹ ∀' φ (&0))

end Induction

namespace PA
  open Languages LPA L_T BoundedFormula SyntaxTheory Induction

  /-- Peano arithemtic -/
  inductive peano_axioms : ℒ.Theory where
    | first : peano_axioms (∀' ∼(null =' S(&0)))
    | second :peano_axioms (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
    | third : peano_axioms (∀' ((&0 add null) =' &0))
    | fourth : peano_axioms (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
    | fifth : peano_axioms (∀' ((&0 mult null) =' null))
    | sixth : peano_axioms (∀' ∀' ((&1 mult S(&0)) =' ((&1 mult &0)) add &1))

  def pa : ℒ.Theory := peano_axioms ∪ {φ | ∃ψ, φ = @ind ℒ _ ψ}

  notation "𝐏𝐀" => pa

end PA

namespace PAT
open Languages PA L_T SyntaxTheory BoundedFormula Induction

def pat : ℒₜ.Theory := peano_axioms ∪ {φ | ∃ψ, φ = @ind ℒₜ _ ψ}
notation "𝐏𝐀𝐓" => pat

end PAT

namespace TB
open Languages L_T LPA PAT SyntaxTheory

variable [Encodable (ℒ.Sentence)]
def tarski_biconditional (ψ : ℒ.Sentence) : ℒₜ.Sentence := T(⌜ψ⌝) ⇔ ψ
def tb : ℒₜ.Theory := 𝐏𝐀𝐓 ∪ {φ | ∃ψ : ℒ.Sentence, φ = (tarski_biconditional ψ)}

notation "𝐓𝐁" => tb

end TB
