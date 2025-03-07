import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax

open FirstOrder
open Language

section ToString
variable {L : Language}{α : Type}
-- variable [∀ k, ToString (L.Functions k)] [∀ k, ToString (L.Relations k)] [ToString ξ]

def toStr {n} : BoundedFormula L α n → String
  | falsum                    => "\\bot"
  | equal   t₁ t₂                  => "(" ++ toString t₁ ++ " = " ++ toString t₂ ++ ")"
  | rel                       => toString r ++ "(" ++ String.vecToStr (fun i => toString (v i)) ++ ")"
  | rel (arity := 0) R _      => toString r
  | imp f₁ f₂                 => "(" ++ toStr f₁ ++ " → " ++ toStr f₂ ++ ")"
  | all φ                     => "∀x" ++ toString n ++ "}) " ++ toStr φ
  | ex φ                      => "(\\exists x_{" ++ toString n ++ "}) " ++ toStr φ

instance : Repr (BoundedFormula L α n) := ⟨fun t _ => toStr t⟩

instance : ToString (BoundedFormula L α n) := ⟨toStr⟩

end ToString

namespace Languages
  namespace LPA -- change to L
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
    notation "S(" n ")" => Term.func Func.succ ![n]
    notation "zero" => Term.func Func.zero ![]
    notation n "add" m => Term.func Func.add ![n,m]
    notation n "times" m => Term.func Func.mult ![n,m]
    notation "ℒₚₐ" => signature

    /-
    Some useful terms
    -/
    def null : Term signature α :=
      zero
    def numeral : ℕ → Term signature α
      | .zero => zero
      | .succ n => S(numeral n)
  end LPA

  namespace L_T

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
  def to_lt_func ⦃n : ℕ⦄ : (LPA.signature.Functions n) → (L_T.signature.Functions n)
    | .zero => .zero
    | .succ => .succ
    | .add => .add
    | .mult => .mult

  def to_lt_rel ⦃n : ℕ⦄ : (LPA.signature.Relations n) → (L_T.signature.Relations n) :=
    Empty.casesOn -- i.e. there are no LPA relations

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

  def ϕ : LHom ℒₚₐ ℒₜ where
    onFunction := to_lt_func
    onRelation := to_lt_rel

end Languages

namespace Calculus
  open Languages
  open BoundedFormula
  notation f "↑'" n "#" m => liftAt n m f
  notation f "↑" n => f ↑' n # 0
  notation A "/[" t "]" => subst A ![t]
  inductive prf : Set (BoundedFormula L α n) → BoundedFormula L β m → Type _ where
  | axm Γ A : A ∈ Γ → prf Γ A
  | impI Γ A B : prf (insert A Γ) B → prf Γ (A ⟹ B)
  | impE Γ A B : prf Γ (A ⟹ B) → prf Γ A → prf Γ B
  | falsumE Γ A : prf (insert ∼A Γ) ⊥ → prf Γ A
  | allI Γ A : prf ((λf => f ↑ 1) '' Γ) A → prf Γ (∀' A)
  | allE₂ Γ A t : prf Γ (∀' A) → prf Γ (A/[t])
  | ref Γ t : prf Γ (t =' t')
  | subst₂ Γ s t f : prf Γ (s =' t) → prf Γ (f/[s]) → prf Γ (f/[t])
end Calculus

namespace PA
  open Languages
  open LPA
  open BoundedFormula

  /-
  Running into trouble with the indexing typing in combination with substitution.
  -/
  def var : Term ℒₚₐ ℕ :=
    Term.var 0
  def eq_var : BoundedFormula ℒₚₐ (Fin 1) 1 :=
    S((Term.var ∘ Sum.inl) 0) =' S(&0)
  #print eq_var
  def tof_eq_var : Formula ℒₚₐ (Fin 1 ⊕ Fin 1) :=
    eq_var.toFormula
  #print tof_eq_var

  #check ℕ ⊕ (Fin 1)
  def thing : BoundedFormula ℒₚₐ (Fin 1) 0 := eq_var/[S(Term.var 0)]
  #check thing
  #check ∀' thing

  def var_eq_var : BoundedFormula ℒₚₐ (Fin 2) 0 :=
    ∀' ((&0) =' (&1))

  #check subst var_eq_var ![LPA.null, Term.var 1]

  def var_eq_var2 : BoundedFormula ℒₚₐ (Fin 2) 0 :=
    ∀' ∀' ((&0) =' (&1))

  #eval var_eq_var

  def replace_bound_variable (φ : BoundedFormula ℒₚₐ (Fin 1) 1) (t : Term ℒₚₐ Empty) : Sentence ℒₚₐ :=
    subst φ.toFormula (fun _ : Fin 1 ⊕ Fin 1 => t)
  notation A "//[" t "]" => replace_bound_variable A t

  def replace_bv_with_S_bv (φ : BoundedFormula ℒₚₐ (Fin 1 ⊕ Empty) 0) : BoundedFormula ℒₚₐ Empty 1 :=
    (subst (φ ↑ 1) (fun _ : Fin 1 ⊕ Empty => S(&0)))

  def replace_bv_with_bv_term (φ : BoundedFormula ℒₚₐ Empty 1) (t : Term ℒₚₐ (Fin 1)) : BoundedFormula ℒₚₐ Empty 1 :=
    subst (φ.toFormula ↑ 1) (fun _ : Fin 1 ⊕ Empty => t)

  def replace_bound

  inductive axioms : Theory ℒₚₐ where
  | first : axioms (∀' ∼(LPA.null =' S(&0)))
  | second :axioms (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
  | third : axioms (∀' ((&0 add LPA.null) =' &0))
  | fourth : axioms (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
  | fifth : axioms (∀' ((&0 times LPA.null) =' LPA.null))
  | sixth : axioms (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
  | induction {n : ℕ} (φ : BoundedFormula ℒₚₐ (Fin 1) 1) : axioms (∼ (φ//[LPA.null] ⟹ (∼(∀'(φ ⟹ φ/[S(&0)])))) ⟹ ∀'(φ))

  /-
  A coercion from ℒₚₐ Axioms to ℒₜ Axioms as all ℒₚₐ Axioms are also
  ℒₜ Axioms -/
  def to_lt_T : Theory ℒₚₐ → Theory ℒₜ := by
    repeat rewrite[Theory]
    repeat rewrite[Set]
    intro set
    intro φ
    sorry
  -- inductive axioms : Theory ℒₚₐ where
  -- | first :
end PA
