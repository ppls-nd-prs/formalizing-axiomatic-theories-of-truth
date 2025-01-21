import Foundation.Logic.Predicate.Language
import FormalizingAxiomaticTheoriesOfTruth.Basic



open LO
open FirstOrder

-- Constructing and printing some terms
-- Definition of useful LPA terms
-- the terms properties L, ξ and n should correspond to the
-- properties of the formula they will be a part of
def LPA_null : SyntacticTerm LPA := Semiterm.func LPA_Func.zero ![]

def LPA_numeral : ℕ → SyntacticTerm LPA
  | .zero => Semiterm.func LPA_Func.zero ![]
  | .succ n => Semiterm.func LPA_Func.succ ![LPA_numeral n]

def LTr_null : SyntacticTerm LTr := Semiterm.func LPA_Func.zero ![]
def LTr_numeral : ℕ → SyntacticTerm LTr
  | .zero => Semiterm.func LPA_Func.zero ![]
  | .succ n => Semiterm.func LPA_Func.succ ![LTr_numeral n]

def LTr_t1 : SyntacticTerm LTr := Semiterm.func LPA_Func.mult ![LTr_numeral 2, LTr_numeral 3]
#eval LTr_t1
#eval LPA_numeral 3

-- Some formulas
def PA_eq_null : SyntacticFormula LPA := Semiformula.rel LPA_Rel.eq ![LPA_null, LPA_null]
def PA_bound_variable : Semiterm LPA ℕ 1 := Semiterm.bvar 1
def PA_eq_exists : SyntacticFormula LPA := Semiformula.ex (Semiformula.rel LPA_Rel.eq ![PA_bound_variable,PA_bound_variable])
-- def PA_eq_null_sent : Sentence LPA := Semiformula.rel LPA_Rel.eq ![LPA_null, LPA_null]
def PA_eq_num_2_num_4 : SyntacticFormula LPA := Semiformula.rel LPA_Rel.eq ![LPA_numeral 2,LPA_numeral 4] --!
def PA_f3 : SyntacticFormula LPA := Semiformula.and PA_eq_num_2_num_4 PA_eq_num_2_num_4
def PA_f4 : SyntacticFormula LPA := Semiformula.or PA_eq_num_2_num_4 PA_eq_num_2_num_4
def PA_f1 : SyntacticFormula LPA := Semiformula.verum
def LTr_f1 : SyntacticFormula LTr := Semiformula.rel LTr_Rel.tr ![LTr_numeral 2]
#eval PA_eq_null
#eval PA_eq_num_2_num_4
#eval PA_f3
#eval PA_f4
#eval LTr_f1
#eval PA_f1

-- SCRATCH WORK FROM HERE ON OUT
-- Goal: have ¬=(S(S(S(0))),0) from PA axiom 1.
def first_PA_ax : Semiformula LPA ℕ 0 :=
  Semiformula.all (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ
  ![#0],Semiterm.func LPA_Func.zero ![]])
def first_PA_ax_b_free : Semiformula LPA ℕ 1 :=
  (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ
  ![#0],Semiterm.func LPA_Func.zero ![]])
def instance_first_PA_ax : Semiformula LPA ℕ 0 :=
  Semiformula.nrel LPA_Rel.eq ![(LPA_numeral 3),LPA_null]

#eval first_PA_ax_b_free/[LPA_numeral 3]
#eval (Rewriting.fix first_PA_ax)/[LPA_numeral 3]
#check (Rewriting.fix (Rewriting.fix first_PA_ax))

def finset1 : Finset ℕ := {1,2,3}
#check finset1

def PA : Theory LPA := {first_PA_ax}

def derivation : PA ⊢ instance_first_PA_ax := by
  have h0 : PA ⟹. instance_first_PA_ax := by
    have h1 : PA ⟹ [first_PA_ax] := by
      have h10 : first_PA_ax ∈ PA := by
        rw [PA]
        simp
      apply Derivation.root at h10
      exact h10
    apply Derivation.specialize (LPA_numeral 2) at h1
    rw[instance_first_PA_ax]
    simp at h1
    rw[LPA_numeral,LPA_null]
    exact h1
  apply Derivation.provableOfDerivable
  exact h0


def t2 : Semiterm LPA ℕ 1 := Semiterm.func LPA_Func.zero ![]
def t3 : Semiterm LPA ℕ 1 := #0
def f1 : Semiformula LPA ℕ 2 := Semiformula.rel LPA_Rel.eq
![#0, #1]
-- def t4 : Semiterm LPA ℕ 1 := Semiterm.func LPA_Func.add ![t2,t3]
#eval f1
#eval (∀' f1) -- TODO: search for relation with theoretical level
#eval (∀' f1)/[t3]
-- #eval t4/[LPA_numeral 2]

-- can you construct a semiformula from semiterms with a
-- different numbers of free bound variables? Answer: no (see below)
def tk0 : Semiterm LPA ℕ 2 := &0
def tk1 : Semiterm LPA ℕ 2 := &1
def tl : Semiterm LPA ℕ 1 := #0
-- def f2 : Semiformula LPA ℕ 2 := Semiformula.rel LPA_Rel.eq ![tk,tk]

-- can you subsitute in semiformulas with a number of free
-- bound variables different than 1? Answer: no (see below)
def f3 : Semiformula LPA ℕ 2 :=
  Semiformula.rel LPA_Rel.eq ![#0,#1]
#eval f3/[tk0,tk1]
#check f3/[tk0,tk1]
