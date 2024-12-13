import Foundation.Logic.Predicate.Language

open LO
open FirstOrder
open Language

inductive PA_Func : ℕ → Type where
  | zero : PA_Func 0
  | succ : PA_Func 1
  | add : PA_Func 2
  | mult : PA_Func 2

inductive PA_Rel : ℕ → Type where
  | eq : PA_Rel 2

def LPA : Language where
  Func := PA_Func
  Rel := PA_Rel
