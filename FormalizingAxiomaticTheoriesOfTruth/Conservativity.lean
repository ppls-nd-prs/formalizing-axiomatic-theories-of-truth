import FormalizingAxiomaticTheoriesOfTruth.ProofTheory

open FirstOrder
open Language

namespace PA
  open Languages
  open LPA
  open L_T
  open BoundedFormula

  /-- The induction function for ℒₚₐ -/
  def induction (f : BoundedFormula ℒ ℕ 0) : ℒ.Formula ℕ :=
    ∼ (f////[LPA.null] ⟹ (∼(∀'(f////[&0] ⟹ f////[S(&0)])))) ⟹ ∀'f////[&0]

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
  def induction (f : BoundedFormula ℒₜ ℕ 0) : ℒₜ.Formula ℕ :=
    ∼ (f////[L_T.null] ⟹ (∼(∀'(f////[&0] ⟹ f////[S(&0)])))) ⟹ ∀'f////[&0]

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
  | disquotation {φ : ℒ.Formula ℕ} : tarski_biconditionals (T(⌜φ⌝) ⇔ φ)

notation "𝐓𝐁" => tarski_biconditionals
end TB

namespace Conservativity
  open Languages
  open Calculus
  open TB
  open PA

  -- theorem conservativity_of_tb (f : Formula ℒ ℕ) : (𝐓𝐁 ⊢ f) → (𝐏𝐀 ⊢ f) := by
  --   sorry
end Conservativity
