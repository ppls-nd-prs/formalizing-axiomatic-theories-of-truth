import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax

namespace Languages
open FirstOrder
open Language

  namespace LPA
    inductive Func : ℕ → Type _ where
      | zero : Func 0
      | succ : Func 1
      | add : Func 2
      | mult : Func 2

    def signature : Language :=
      ⟨Func, fun _ => Empty⟩

    /-
    Useful notation
    -/
    prefix:60 "S" => Term.func Func.succ
    infix:60 "=" => BoundedFormula.equal
    prefix:60 "zero" => Term.func Func.zero
    prefix:60 "add" => Term.func Func.add
    prefix:60 "times" => Term.func Func.mult
    notation "ℒₚₐ" => signature

    /-
    Some useful terms
    -/
    def null : Term signature α :=
      zero ![]
    def numeral : ℕ → Term signature α
      | .zero => zero ![]
      | .succ n => S ![numeral n]
  end LPA

  namespace L_T
    open FirstOrder
    open Language

    inductive Func : ℕ → Type _ where
      | zero : Func 0
      | succ : Func 1
      | add : Func 2
      | mult : Func 2

    inductive Rel : ℕ → Type _ where
      | t : Rel 1

    def signature : Language :=
      ⟨Func, Rel⟩

    /-
    Some useful notation
    -/
    prefix:60 "T" => Formula.rel Rel.t
    notation "ℒₜ" => signature
  end L_T

  /-
  Some useful notation
  -/
  variable (l : Language)
  abbrev Fml : Type _ := Formula l ℕ -- perhaps

  /-
  A coercion from PA.lpa formulas to L_T.lt formulas as all lpa formulas are
  also lt formulas
  -/
  def to_lt_func {arity : ℕ} : (LPA.Func arity) → (L_T.Func arity)
    | .zero => .zero
    | .succ => .succ
    | .add => .add
    | .mult => .mult

  def to_lt_t: Term ℒₚₐ α → Term ℒₜ α
    | .var α => .var α
    | .func (l := n) f ts => .func (to_lt_func f) (fun i : Fin n => to_lt_t (ts i))

  def to_lt_f: BoundedFormula ℒₚₐ α n → BoundedFormula ℒₜ α n
    | .falsum => .falsum
    | .equal t₁ t₂ => .equal (to_lt_t t₁) (to_lt_t t₂)
    | .imp f₁ f₂ => .imp (to_lt_f f₁) (to_lt_f f₂)
    | .all f => .all (to_lt_f f)

  example: ∀φ:Fml ℒₚₐ, ∃ψ:Fml ℒₜ, ψ = to_lt_f φ :=
    fun a : Fml ℒₚₐ => Exists.intro (to_lt_f a) (Eq.refl (to_lt_f a))

  instance : Coe (Term ℒₚₐ α) (Term ℒₜ α) where
    coe t := to_lt_t t
  instance : Coe (Fml ℒₚₐ) (Fml ℒₜ) where
    coe φ := to_lt_f φ

end Languages
