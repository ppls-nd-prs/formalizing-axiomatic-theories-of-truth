import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import FormalizingAxiomaticTheoriesOfTruth.Prelims

open FirstOrder
open Language
namespace LPATrying
open Languages.LPA
def zero_eq_zero : Formula ℒₚₐ ℕ :=
  .equal (.func Func.zero ![]) (.func Func.zero ![])
-- moet er nog uitzien als `zero = zero`

open Languages.L_T
def szero_eq_zero : Formula ℒₜ ℕ :=
  .equal (.func Func.zero ![]) (.func Func.zero ![])
