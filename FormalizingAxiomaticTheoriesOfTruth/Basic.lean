import Foundation.Logic.Predicate.Language
import Foundation.FirstOrder.Arith.Theory
import Foundation.FirstOrder.Arith.PeanoMinus

open LO
open FirstOrder
open Language
open Semiterm

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

variable (ξ : ℕ) (n : ℕ)

#check (fun h : Nat => h + h) 2

example : Inhabited (Semiterm LPA ℕ 1) := Inhabited.mk (Semiterm.bvar 0)
example : Inhabited (Semiterm LPA ℕ 1) :=
Inhabited.mk (Semiterm.bvar 2)
example : Inhabited (Semiterm LPA ℕ 0) :=
Inhabited.mk (Semiterm.fvar 1)
example : Inhabited (SyntacticTerm LPA) :=
Inhabited.mk (Semiterm.fvar 1)
example : Inhabited (Term LPA ℕ) := Inhabited.mk (Semiterm.fvar 2)
example : Inhabited (Term LPA ℕ) := Inhabited.mk (Semiterm.func PA_Func.zero (fun _ : Fin 0 => Semiterm.fvar 1))
example : Inhabited (Term LPA ℕ) := Inhabited.mk (Semiterm.func PA_Func.succ (fun _ : Fin 1 => Semiterm.func PA_Func.zero (fun _ : Fin 0 => Semiterm.fvar 1)))
example : Inhabited (Term LPA ℕ) := Inhabited.mk (Semiterm.func PA_Func.mult (fun _ : Fin 2 => Semiterm.fvar 1))

def fvar_term : Term LPA ℕ := Semiterm.fvar 0
#eval freeVariables fvar_term
def not_fvar_term : Semiterm LPA ℕ 1 := Semiterm.bvar 6
#eval freeVariables not_fvar_term

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
