import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax

namespace Languages
  namespace L_T
    open FirstOrder
    inductive Func : ℕ → Type _ where
    | zero : Func 0
    | succ : Func 1
    | add : Func 2
    | mult : Func 2
    | neg : Func 1
    | conj : Func 2
    | disj : Func 2
    | cond : Func 2
    | forall : Func 1
    | exists : Func 1
    | denote : Func 1
    | subs : Func 3
    deriving DecidableEq

  inductive Rel : ℕ → Type _ where
    | var : Rel 1
    | const : Rel 1
    | t : Rel 1
    | term : Rel 1
    | clterm: Rel 1
    | forml : Rel 1
    | sentencel: Rel 1
    | formlt : Rel 1
    | sentencelt : Rel 1
    deriving DecidableEq

  def signature : Language :=
    ⟨Func, Rel⟩

  def ℒₜ {n} : Set (L_T.signature.BoundedFormula ℕ n) := Set.univ
