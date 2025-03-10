import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax

open FirstOrder
open Language

namespace String
  def vecToStr : ∀ {n}, (Fin n → String) → String
  | 0,     _ => ""
  | n + 1, s => if n = 0 then s 0 else s 0 ++ ", " ++ @vecToStr n (fun i => s (Fin.succ i))

  #eval vecToStr !["a","b","c"]

end String

namespace Term
  variable {L : Language} {α β : Type}
  variable [∀ k, ToString (L.Functions k)] [ToString α] [ToString β]

  section ToString
    def toStr : Term L (α ⊕ β) → String :=
      fun t : Term L (α ⊕ β) =>
        match t with
        | .var k =>
          match k with
            | (Sum.inl l) => "#" ++ toString l
            | (Sum.inr l) => "&" ++ toString l
        | .func (l := 0) c _ => toString c
        | .func (l := _ + 1) f ts => toString f ++ "(" ++ String.vecToStr (fun i => toStr (ts i)) ++ ")"

    instance : Repr (Term L (α ⊕ β)) := ⟨fun t _ => toStr t⟩
    instance : ToString (Term L (α ⊕ β)) := ⟨toStr⟩
  end ToString
end Term

namespace BoundedFormula
  section ToString
    variable {L : Language} {α : Type}
    variable [∀ k, ToString (L.Functions k)] [∀ k, ToString (L.Relations k)] [ToString α]

    def toStr {n} : BoundedFormula L α n → String
      | .falsum                    => "⊥"
      | .equal t₁ t₂               => toString t₁ ++ " = " ++ toString t₂
      | .rel R ts                  => toString R ++ "(" ++ String.vecToStr (fun i => toString (ts i)) ++ ")"
      | .imp f₁ f₂                 => "(" ++ toStr f₁ ++ " → " ++ toStr f₂ ++ ")"
      | .all f                     => "∀" ++ toStr f

    instance : Repr (BoundedFormula L α n) := ⟨fun t _ => toStr t⟩
    instance : ToString (BoundedFormula L α n) := ⟨toStr⟩
  end ToString
end BoundedFormula

namespace Languages
  namespace LPA -- change to L
    inductive Func : ℕ → Type _ where
      | zero : Func 0
      | succ : Func 1
      | add : Func 2
      | mult : Func 2

    def signature : Language :=
      ⟨Func, fun _ => Empty⟩

    def funToStr {n}: Func n → String
      | .zero => "0"
      | .succ => "S"
      | .add => "+"
      | .mult => "×"
    instance {n : ℕ}: ToString (signature.Functions n) := ⟨funToStr⟩

    instance : ToString (Empty) := -- necessary for string function relations
      ⟨ Empty.casesOn ⟩

    def relToStr {n} : signature.Relations n → String :=
      fun _ => ""
    instance : ToString (signature.Relations n) := ⟨relToStr⟩

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
  A homomorphism between PA.lpa and L_T.lt formulas is constructed, as all lpa formulas are
  also lt formulas.
  The homomorphism can be used to translate from ℒₚₐ BoundedFormulas to ℒₜ BoundedFormulas using:
    - FirstOrder.Language.LHom.onBoundedFormula for BoundedFormulas
    - FirstOrder.Language.LHom.onFormula for Formulas
    - FirstOrder.Language.LHom.onSentence for Sentences and
    - FirstOrder.Language.LHom.onTheory for Theories.
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
  open ToString
  open Languages
  open LPA
  open BoundedFormula

  /-
  Running into trouble with the indexing typing in combination with substitution.
  -/
  scoped[FirstOrder] prefix:arg "#" => FirstOrder.Language.Term.var ∘ Sum.inl

  def v_eq_v_lpa : BoundedFormula ℒₚₐ (ℕ) 1 :=
    ((#0) =' (&0)) ⟹ ((#0) =' (&0))
  #check ∀' v_eq_v_lpa
  def zero_term : Term ℒₚₐ ℕ :=
    LPA.null
  #eval Term.toStr zero_term
  #eval subst (∀' v_eq_v_lpa) (fun _ => zero_term)
  def v_eq_v_lt : Formula ℒₜ (Fin 1) :=
    LHom.onFormula ϕ v_eq_v_lpa
  def var {n m : ℕ} {β : Fin n} {α : Fin m} : Term ℒₚₐ (β ⊕ γ) :=
    Term.var 0
  #eval var
  def var_eq_var : BoundedFormula ℒₚₐ (Fin 1) 0 :=
    var =' var
  def var_eq_var
  def eq_var : BoundedFormula ℒₚₐ (Fin 1) 1 :=
    S((Term.var ∘ Sum.inl) 0) =' S(&0)
  #eval eq_var
  def tof_eq_var : Formula ℒₚₐ (Fin 1 ⊕ Fin 1) :=
    eq_var.toFormula
  #print tof_eq_var

  #check ℕ ⊕ (Fin 1)


  def test1 : BoundedFormula ℒₚₐ ℕ 0 :=
    (#0) =' (#0)
  #eval (∀' (test1 ↑ 1) ↑ 1)

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
