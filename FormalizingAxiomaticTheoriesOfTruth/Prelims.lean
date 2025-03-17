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
  namespace L
    inductive Func : ℕ → Type _ where
      | zero : Func 0
      | succ : Func 1
      | add : Func 2
      | mult : Func 2
      | num : Func 1
      | neg : Func 1
      | conj : Func 2
      | disj : Func 2
      | cond : Func 2
      | forall : Func 1
      | exists : Func 1
      | denote : Func 1

    inductive Rel : ℕ → Type _ where
      | var : Rel 1
      | const : Rel 1
      | Term : Rel 1
      | Form : Rel 1
      | Sentence : Rel 1
      | Proof : Rel 2

    def signature : Language :=
      ⟨Func, Rel⟩

    def funToStr {n}: Func n → String
      | .zero => "0"
      | .succ => "S"
      | .add => "+"
      | .mult => "×"
      | .num => "𝑛𝑢𝑚"
      | .neg => "𝑛𝑒𝑔"
      | .conj => "𝑐𝑜𝑛𝑗"
      | .disj => "𝑑𝑖𝑠𝑗"
      | .cond => "𝑐𝑜𝑛𝑑"
      | .forall => "𝑎𝑙𝑙"
      | .exists => "𝑒𝑥"
      | .denote => "𝑑𝑒𝑛"
    instance {n : ℕ}: ToString (signature.Functions n) := ⟨funToStr⟩

    def relToStr {n} : signature.Relations n → String
      | .var => "𝑣𝑎𝑟"
      | .const => "𝑐𝑜𝑛𝑠𝑡"
      | .Term => "𝑡𝑒𝑟𝑚"
      | .Form => "𝑓𝑜𝑟𝑚"
      | .Sentence => "𝑠𝑒𝑛𝑡"
      | .Proof => "𝑝𝑟𝑜𝑜𝑓"
    instance : ToString (signature.Relations n) := ⟨relToStr⟩

    /-
    Useful notation
    -/
    notation "S(" n ")" => Term.func Func.succ ![n]
    notation "zero" => Term.func Func.zero ![]
    notation n "add" m => Term.func Func.add ![n,m]
    notation n "times" m => Term.func Func.mult ![n,m]
    notation n "and" m => Term.func Func.conj ![n,m]
    notation n "or" m => Term.func Func.disj ![n,m]
    notation "num(" n ")" => Term.func Func.num ![n]
    notation "not" n => Term.func Func.neg ![n]
    notation n "then" m => Term.func Func.cond ![n,m]
    notation "forall" n => Term.func Func.forall ![n]
    notation "exists" n => Term.func Func.exists ![n]
    notation n "°" => Term.func Func.denote ![n]
    notation "ℒ" => signature
    scoped[Languages] prefix:arg "#" => FirstOrder.Language.Term.var ∘ Sum.inl

    /-
    Some useful terms
    -/
    def null : Term signature α :=
      zero
    def numeral : ℕ → Term signature α
      | .zero => zero
      | .succ n => S(numeral n)
  end L

  namespace L_T

    inductive Func : ℕ → Type _ where
      | zero : Func 0
      | succ : Func 1
      | add : Func 2
      | mult : Func 2
      | num : Func 1
      | neg : Func 1
      | conj : Func 2
      | disj : Func 2
      | cond : Func 2
      | forall : Func 1
      | exists : Func 1
      | denote : Func 1

    inductive Rel : ℕ → Type _ where
      | var : Rel 1
      | const : Rel 1
      | t : Rel 1
      | Term : Rel 1
      | Form : Rel 1
      | Sentence : Rel 1
      | Proof : Rel 2

    def signature : Language :=
      ⟨Func, Rel⟩

    def funToStr {n}: Func n → String
      | .zero => "0"
      | .succ => "S"
      | .add => "+"
      | .mult => "×"
      | .num => "𝑛𝑢𝑚"
      | .neg => "𝑛𝑒𝑔"
      | .conj => "𝑐𝑜𝑛𝑗"
      | .disj => "𝑑𝑖𝑠𝑗"
      | .cond => "𝑐𝑜𝑛𝑑"
      | .forall => "𝑎𝑙𝑙"
      | .exists => "𝑒𝑥"
      | .denote => "𝑑𝑒𝑛"
    instance {n : ℕ}: ToString (signature.Functions n) := ⟨funToStr⟩

    def relToStr {n} : signature.Relations n → String
      | .var => "𝑣𝑎𝑟"
      | .const => "𝑐𝑜𝑛𝑠𝑡"
      | .t => "T"
      | .Term => "𝑡𝑒𝑟𝑚"
      | .Form => "𝑓𝑜𝑟𝑚"
      | .Sentence => "𝑠𝑒𝑛𝑡"
      | .Proof => "𝑝𝑟𝑜𝑜𝑓"
    instance : ToString (signature.Relations n) := ⟨relToStr⟩

    /-
    Some useful notation
    -/
    prefix:60 "T" => Formula.rel Rel.t
    notation "Term(" t ")" => Formula.rel Rel.Term ![t]
    notation "Form(" t ")" => Formula.rel Rel.Form ![t]
    notation "sentence(" t ")" => Formula.rel Rel.Sentence ![t]
    notation "Proof(" t "," s ")" => Formula.rel Rel.Proof ![t,s]
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
  def to_lt_func ⦃arity : ℕ⦄ : (L.Func arity) → (L_T.Func arity)
    | .zero => .zero
    | .succ => .succ
    | .add => .add
    | .mult => .mult
    | .num => .num
    | .neg => .neg
    | .conj => .conj
    | .disj => .disj
    | .cond => .cond
    | .forall => .forall
    | .exists => .exists
    | .denote => .denote

  def to_lt_rel ⦃n : ℕ⦄ : (L.signature.Relations n) → (L_T.signature.Relations n)
      | .var => .var
      | .const => .const
      | .Term => .Term
      | .Form => .Form
      | .Sentence => .Sentence
      | .Proof => .Proof

  def ϕ : LHom ℒ ℒₜ where
      onFunction := to_lt_func
      onRelation := to_lt_rel
end Languages

namespace encoding

end encoding

namespace Calculus
  open Languages
  open BoundedFormula
  notation f " ↑' " n " at "  m => liftAt n m f
  notation f "↑" n => f ↑' n at 0
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
  open L
  open L_T

  /-
  Playing around
  -/

  def and_assoc : BoundedFormula ℒ (Fin 1) 0 :=
    ∀' ∀' ∀' (((&0 and &1) and &2) =' (&0 and (&1 and &2)))

  def commutative : BoundedFormula ℒ (Fin 1) 0 :=
    ∀' ∀' ((&0 and &1) =' (&1 and &0))

  def eq_forall : BoundedFormula ℒ (Fin 1) 1 :=
    ∀'(&0 =' forall &0)


  -- /-
  -- Running into trouble with the indexing typing in combination with substitution.
  -- -/

  -- def eq_var : BoundedFormula ℒ (Fin 1) 1 :=
  --   S(&0) =' S(&0)
  -- #check eq_var.toFormula
  -- #check eq_var/[L.null]
  -- def replace : Sentence ℒ :=
  --   ((S(&0) =' S(&0))/[L.null])
  -- example : (eq_var/[L.null]) = (S(L.null) =' S(L.null)) :=
  -- #check ∀' eq_var
  -- inductive axioms : Theory ℒ where
  -- | first : axioms (∀' ∼(L.null =' S(&0)))
  -- | second :axioms (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
  -- | third : axioms (∀' ((&0 add L.null) =' &0))
  -- | fourth : axioms (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
  -- | fifth : axioms (∀' ((&0 times L.null) =' L.null))
  -- | sixth : axioms (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
  -- | induction φ : (axioms (∼ (((φ/[L.null]) ⟹ ∼(∀'(φ ⟹ φ/[succ_var_term]))) ⟹ ∀' φ)))
  -- /-
  -- A coercion from ℒₚₐ Axioms to ℒₜ Axioms as all ℒₚₐ Axioms are also
  -- ℒₜ Axioms -/
  -- def
  -- def to_lt_T : Theory ℒ → Theory ℒₜ := by
  --   repeat rewrite[Theory]
  --   repeat rewrite[Set]
  --   intro set
  --   intro φ
  --   sorry
  -- inductive axioms : Theory ℒ where
  -- | first :
end PA
