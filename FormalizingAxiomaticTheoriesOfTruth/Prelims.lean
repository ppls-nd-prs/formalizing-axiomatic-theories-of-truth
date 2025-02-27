import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax

namespace Languages

  namespace LPA
    open FirstOrder
    open Language

    inductive Func : ℕ → Type u where
      | zero : Func 0
      | succ : Func 1
      | add : Func 2
      | mult : Func 2

    def language : Language :=
      ⟨Func, fun _ => Empty⟩

    notation "ℒₚₐ" => language
  end LPA

  namespace L_T
    open FirstOrder
    open Language

    inductive Func : ℕ → Type u where
      | zero : Func 0
      | succ : Func 1
      | add : Func 2
      | mult : Func 2

    inductive Rel : ℕ → Type v where
      | t : Rel 1

    def language : Language :=
      ⟨Func, Rel⟩

    notation "ℒₜ" => language

  end L_T
end Languages
