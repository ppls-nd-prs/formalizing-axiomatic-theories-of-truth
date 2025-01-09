import Foundation.Logic.Predicate.Language
import FormalizingAxiomaticTheoriesOfTruth.Basic

open LO
open FirstOrder

-- Constructing and printing some terms
-- Definition of useful LPA terms
def LPA_null : SyntacticTerm LPA := Semiterm.func LPA_Func.zero (fun _ : Fin 0 => Semiterm.fvar 1)

def LPA_numeral : ℕ → SyntacticTerm LPA
  | .zero => Semiterm.func LPA_Func.zero (fun _ : Fin 0 => Semiterm.fvar 1)
  | .succ n => Semiterm.func LPA_Func.succ (fun _ : Fin 1 => LPA_numeral n)

def LTr_null : SyntacticTerm LTr := Semiterm.func LPA_Func.zero (fun _ : Fin 0 => Semiterm.fvar 1)
def LTr_numeral : ℕ → SyntacticTerm LTr
  | .zero => Semiterm.func LPA_Func.zero (fun _ : Fin 0 => Semiterm.fvar 1)
  | .succ n => Semiterm.func LPA_Func.succ (fun _ : Fin 1 => LTr_numeral n)

def LTr_t1 : SyntacticTerm LTr := Semiterm.func LPA_Func.mult ![LTr_numeral 2, LTr_numeral 3]
#eval LTr_t1

-- Some formulas
def PA_eq_null : SyntacticFormula LPA := Semiformula.rel LPA_Rel.eq (fun _ : Fin 2 => LPA_null)
def PA_eq_num_2_num_4 : SyntacticFormula LPA := Semiformula.rel LPA_Rel.eq (fun h : Fin 2 => ![LPA_numeral 2,LPA_numeral 4] h) --!
def PA_e_num_2_num_4 : SyntacticFormula LPA := Semiformula.rel LPA_Rel.eq ![LPA_numeral 2,LPA_numeral 4] --!
def PA_f3 : SyntacticFormula LPA := Semiformula.and PA_eq_num_2_num_4 PA_eq_num_2_num_4
def PA_f4 : SyntacticFormula LPA := Semiformula.or PA_eq_num_2_num_4 PA_eq_num_2_num_4
def PA_f1 : SyntacticFormula LPA := Semiformula.verum
def LTr_f1 : SyntacticFormula LTr := Semiformula.rel LTr_Rel.tr ![LTr_numeral 2]
#eval PA_eq_null
#eval PA_eq_num_2_num_4
#eval PA_f3
#eval PA_f4
#eval LTr_f1

-- SCRATCH WORK FROM HERE ON OUT
def one : SyntacticTerm LPA := Semiterm.func LPA_Func.succ (fun _ : Fin 1 => LPA_null)
def two : SyntacticTerm LPA := Semiterm.func LPA_Func.succ (fun _ : Fin 1 => one)
#eval LPA_Rel.eq
#eval (fun h : Fin 3 => if h = 0 then 2 else 4) -- ![2,4,4] then the index resulting from a modulo on the argument ∈ ℕ is returned
#eval (fun h : Fin 3 => if h = 0 then 2 else 4) 20 -- 4, as 20 % 3 = 2 and 4 is at index 2 (0-based indexing)
def PA_fvt0 : Semiterm LPA ℕ 1 := Semiterm.fvar 0
def PA_semf1 : Semiformula LPA ℕ 1 := Semiformula.rel LPA_Rel.eq (fun _ : Fin 2 => PA_fvt0)
def PA_f5 : SyntacticFormula LPA := Semiformula.all PA_semf1

-- Inhabited.mk (fun h₁ : LPA.Func 0 => (fun h₂ : Fin 0 → Semiterm LPA ℕ 0 => h₁)) PA_Func.zero

-- open Arith
-- open Theory
-- open Semiformula

-- variable
--   {L : Language}
--   {ξ : Type*}
--   {n : ℕ}

-- lemma sentence {k} (r : LPA.Rel k)(v : Fin k → Semiterm LPA ξ n): ∼(rel r v) = nrel r v := rfl
-- #check sentence

-- open LO
-- open Arith
-- open Language

-- -- variable {M : Type*} [ORingStruc M]
-- -- variable [M ⊧ₘ* 𝐏𝐀⁻]

-- lemma PA_add_zero (x : M) : x + 0 = x := by
--   simpa[models_iff]

-- lemma PA_univ_add_zero: ∀x, x + 0 = x := by
--   simpa[models_iff] using ModelsTheory.models M Theory.PAMinus.mulAssoc (fun _ ↦ x)

-- lemma PA_stuff (h : M): 11 * 2 = 22 := by
--     simpa[models_iff]

-- lemma test_two : 11 * 11 = 121 := by
--   simpa[models_iff]

-- lemma test_three : 100 - 4 = 96 := by
--   simpa[models_iff]

-- lemma test_four (y : M) (h : x = 100) : 2*x = 200 := by
--   rw [h]

-- lemma ind_schema: ∀ x, (x + 2 = x + 2) := by
--   simpa[models_iff]

-- import Mathlib.Data.Set.Basic
-- open Set

-- structure Signature where
--   Const : Type
--   Func : Type
--   Rel : Type
--   ArRel : Rel → Nat
--   ArFunc : Func → Nat

-- inductive PA_Const where
--   | zero

-- inductive PA_Func where
--   | succ
--   | add
--   | mul

-- inductive PA_Rel where
--   | eq : PA_Rel

-- def PA_Ar_Func : PA_Func → Nat
--   | .succ => 1
--   | .add => 2
--   | .mul => 2

-- def PA_Ar_Rel : PA_Rel → Nat
--   | .eq  => 2

-- def PA_Signature : Signature where
--   Const := PA_Const
--   Func :=  PA_Func
--   Rel := PA_Rel
--   ArRel := PA_Ar_Rel
--   ArFunc := PA_Ar_Func

-- inductive var where
--   | one : var
--   | succ : var → var

-- variable (S : Signature)



-- -- def get_terms : Signature → var → term
-- --   | .Const => .Const
-- --   | .Const => var
-- --   | func {f : Signature.Func} {ar : Signature.Func → Nat} => (Fin (ar f) → term) → term

-- -- def PA_term := term PA_Signature

-- -- #check PA_Const.zero
-- -- #check term.const
-- -- #check term.const PA_Signature

-- -- example : Inhabited PA_term := Inhabited.mk (term.const PA_Signature)
-- -- #check Fin 10

-- example : Inhabited (PA_Signature.Func → Nat) := Inhabited.mk PA_Signature.ArFunc
-- -- example : Inhabited Nat := Inhabited.mk 1
-- -- example : Inhabited var := Inhabited.mk (var.succ (var.succ var.one))
-- -- example : Inhabited (Primitive_Term PA_Signature) := Inhabited.mk var.one

-- -- #check Inhabited.mk (var.succ var.one)

-- -- example : PA_Ar_Func .succ = 1 := rfl

-- -- #print Nat
-- -- #print Inhabited

-- -- example : Inhabited Nat := Inhabited.mk 1
-- #check Fin 10
-- #check Fin.isLt

-- example : Inhabited (Fin 1) := Inhabited.mk 0
