import Foundation.Logic.Predicate.Language
import Foundation.FirstOrder.Arith.Theory
import Foundation.FirstOrder.Arith.PeanoMinus

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

open Arith
open Theory
open Semiformula

variable
  {L : Language}
  {ξ : Type*}
  {n : ℕ}

lemma sentence {k} (r : LPA.Rel k)(v : Fin k → Semiterm LPA ξ n): ∼(rel r v) = nrel r v := rfl
#check sentence

open LO
open Arith
open Language

variable {M : Type*} [ORingStruc M]
variable [M ⊧ₘ* 𝐏𝐀⁻]

lemma PA_add_zero (x : M) : x + 0 = x := by
  simpa[models_iff]

lemma PA_univ_add_zero (x : M) : ∀x, x + 0 = x := by
  simpa[models_iff]

lemma PA_stuff (h : M): 11 * 2 = 22 := by
    simpa[models_iff]

lemma test_two : 11 * 11 = 121 := by
  simpa[models_iff]

lemma test_three : 100 - 4 = 96 := by
  simpa[models_iff]

lemma test_four (y : M) (h : x = 100) : 2*x = 200 := by
  rw [h]
