import FormalizingAxiomaticTheoriesOfTruth.Syntax

open FirstOrder
open Language

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
