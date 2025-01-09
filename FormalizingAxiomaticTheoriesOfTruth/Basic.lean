import Foundation.Logic.Predicate.Language
import Foundation.FirstOrder.Arith.Theory
import Foundation.FirstOrder.Arith.PeanoMinus

open LO
open FirstOrder

-- Definition of the language of arithmetic
inductive LPA_Func : ℕ → Type where
  | zero : LPA_Func 0
  | succ : LPA_Func 1
  | add : LPA_Func 2
  | mult : LPA_Func 2

inductive LPA_Rel : ℕ → Type where
  | eq : LPA_Rel 2

def LPA : Language where
  Func := LPA_Func
  Rel := LPA_Rel

-- Definition of the language of arithmetic including the truth
-- predicate
def LTr_Func := LPA_Func

inductive LTr_Rel : ℕ → Type where
  | eq : LTr_Rel 2
  | tr : LTr_Rel 1

def LTr : Language where
  Func := LTr_Func
  Rel := LTr_Rel

-- Printing terms
def LPA_funToStr {n}: LPA_Func n → String
  | .zero => "0"
  | .succ => "S"
  | .add => "+"
  | .mult => "×"
def LTr_funToStr {n} : LPA_Func n → String := LPA_funToStr
instance : ToString (LPA_Func n) := ⟨LPA_funToStr⟩

-- Printing formulas
def LPA_relToStr {n} : LPA_Rel n → String
| .eq => "="
def LTr_relToStr {n} : LTr_Rel n → String
| .eq => "="
| .tr => "T"
instance : ToString (LPA_Rel n) := ⟨LPA_relToStr⟩
instance : ToString (LTr_Rel n) := ⟨LTr_relToStr⟩
