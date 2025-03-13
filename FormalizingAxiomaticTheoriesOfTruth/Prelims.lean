import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax

open FirstOrder
open Language

namespace Syntax
  variable (L : Language.{u, v}) {L' : Language}
  /-- A term on `α` is either a variable indexed by an element of `α`
    or a function symbol applied to simpler terms. -/
  inductive Term (n : ℕ): Type max u u'
    | var (m : Fin n): Term n
    | func : ∀ {l : ℕ} (_f : L.Functions l) (_ts : Fin l → Term (n)), Term n

  variable (L : Language)
  /-- `BoundedFormula α n` is the type of formulas with free variables indexed by `α` and up to `n`
    additional free variables. -/
  inductive Formula : ℕ → Type _ where
    | falsum : Formula 0
    | equal {n}: Syntax.Term L n → Syntax.Term L n →  Formula n
    | rel {n} (R : L.Relations l) (ts : Fin l → Syntax.Term L n) : Formula n
    | imp {n} (f₁ f₂ : Formula n) : Formula n
    | all {n} (f : Formula (n+1)) : Formula n

  abbrev Sentence :=
    Syntax.Formula L 0

end Syntax

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

    def funToStr {n}: Func n → String
      | .zero => "0"
      | .succ => "S"
      | .add => "+"
      | .mult => "×"
    instance {n : ℕ}: ToString (signature.Functions n) := ⟨funToStr⟩

    def relToStr {n} : signature.Relations n → String
      | .t => "T"
    instance : ToString (signature.Relations n) := ⟨relToStr⟩

    /-
    Some useful notation
    -/
    notation "T(" t ")" => Formula.rel Rel.t ![t]
    notation "ℒₜ" => signature
  end L_T

  namespace LPA -- change to L
    inductive Func : ℕ → Type _ where
      | zero : Func 0
      | succ : Func 1
      | add : Func 2
      | mult : Func 2

    def signature : Language :=
      ⟨Func, fun _ => Empty⟩

    def funToStr {n}: Func n → String
      | .zero => L_T.funToStr L_T.Func.zero
      | .succ => L_T.funToStr L_T.Func.succ
      | .add => L_T.funToStr L_T.Func.add
      | .mult => L_T.funToStr L_T.Func.mult
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

    def var_eq_var : Syntax.Formula ℒₚₐ 2 :=
      Syntax.Formula.equal (Syntax.Term.var 1) (Syntax.Term.var 2)

    def var_eq_var_sent : Syntax.Sentence ℒₚₐ :=
      Syntax.Formula.all (Syntax.Formula.all var_eq_var)

  end LPA

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

  example: ∀φ:Formula ℒₚₐ ℕ, ∃ψ:Formula ℒₜ ℕ, ψ = to_lt_f φ :=
    fun a : Formula ℒₚₐ ℕ => Exists.intro (to_lt_f a) (Eq.refl (to_lt_f a))

  def ϕ : LHom ℒₚₐ ℒₜ where
    onFunction := to_lt_func
    onRelation := to_lt_rel

  /- Useful notation for formula operations -/
  open BoundedFormula
  notation f "↑'" n "#" m => liftAt n m f
  notation f "↑" n => f ↑' n # 0
  notation A "/[" t "]" => subst A (fun k => t)

  variable {L : Language}
  def replace_bound_variable (φ : BoundedFormula L Empty 1) (t : Term L Empty) : Sentence L :=
    subst φ.toFormula (fun _ : Empty ⊕ Fin 1 => t)
  notation A "//[" t "]" => replace_bound_variable A t
  def g : (Empty ⊕ Fin 1) → Empty ⊕ Fin 1 :=
    fun t => t

end Languages

namespace PA
  open Languages
  open LPA
  open BoundedFormula

  /-- The induction function for ℒₚₐ -/
  def induction (φ : BoundedFormula ℒₚₐ Empty 1) : Sentence ℒₚₐ :=
    ∼ (φ//[LPA.null] ⟹ (∼(∀'(φ ⟹ (relabel g (φ.toFormula/[S(&0)])))))) ⟹ ∀'(φ)

  /-- Peano arithemtic -/
  inductive peano_arithmetic : Theory ℒₚₐ where
  | first : peano_arithmetic (∀' ∼(LPA.null =' S(&0)))
  | second :peano_arithmetic (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
  | third : peano_arithmetic (∀' ((&0 add LPA.null) =' &0))
  | fourth : peano_arithmetic (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
  | fifth : peano_arithmetic (∀' ((&0 times LPA.null) =' LPA.null))
  | sixth : peano_arithmetic (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
  | induction (φ) : peano_arithmetic (induction φ)

  notation "𝐏𝐀" => peano_arithmetic
end PA

namespace PAT
  open Languages
  open LPA
  open BoundedFormula

  /-- The induction function for ℒₜ-/
  def induction (φ : BoundedFormula ℒₜ Empty 1) : Sentence ℒₜ :=
    ∼ (φ//[LHom.onTerm ϕ LPA.null] ⟹ (∼(∀'(φ ⟹ (relabel g (φ.toFormula/[LHom.onTerm ϕ S(&0)])))))) ⟹ ∀'(φ)

  /-- Peano arithemtic -/
  inductive peano_arithmetic_with_t : Theory ℒₜ where
  | first : peano_arithmetic_with_t (LHom.onSentence ϕ (∀' ∼(LPA.null =' S(&0))))
  | second :peano_arithmetic_with_t (LHom.onSentence ϕ (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0))))
  | third : peano_arithmetic_with_t (LHom.onSentence ϕ (∀' ((&0 add LPA.null) =' &0)))
  | fourth : peano_arithmetic_with_t (LHom.onSentence ϕ (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0))))
  | fifth : peano_arithmetic_with_t (LHom.onSentence ϕ (∀' ((&0 times LPA.null) =' LPA.null)))
  | sixth : peano_arithmetic_with_t (LHom.onSentence ϕ (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1)))
  | induction (φ) : peano_arithmetic_with_t (induction φ)

  notation "𝐏𝐀𝐓" => peano_arithmetic_with_t
end PAT

namespace Calculus
  open Languages
  inductive prf : Set (BoundedFormula L α n) → BoundedFormula L β m → Type _ where
  | axm {A} : A ∈ Γ → prf Γ A
  | impI {Γ A B} : prf (insert A Γ) B → prf Γ (A ⟹ B)
  | impE {Γ A B} : prf Γ (A ⟹ B) → prf Γ A → prf Γ B
  | falsumE {Γ A} : prf (insert ∼A Γ) ⊥ → prf Γ A
  | allI {Γ A} : prf ((λf => f ↑ 1) '' Γ) A → prf Γ (∀' A)
  | allE₂ {Γ A} (t) : prf Γ (∀' A) → prf Γ (A//[t])
  | ref {Γ t} : prf Γ (t =' t')
  | subst₂ {Γ} {s : Term L (α ⊕ Fin n)} {t : Term L (α ⊕ Fin n)} {f : BoundedFormula L α m} : prf Γ (s =' t) → prf Γ (BoundedFormula.subst f (fun _ : α => t)) → prf Γ (BoundedFormula.subst f (fun _ : α => s))

  /-- Proof that ∼ (LPA.null =' SSS(3)) is provable from 𝐏𝐀 -/
  def to_prove : Sentence ℒₚₐ :=
    ∼(Languages.LPA.null =' S(S(S(Languages.LPA.null))))
  example : Calculus.prf 𝐏𝐀 to_prove := by
    let f1 : BoundedFormula ℒₚₐ Empty 0 := (∀' ∼(Languages.LPA.null =' S(&0)))
    have step1 : f1 ∈ 𝐏𝐀 := by
      apply PA.peano_arithmetic.first
    have step2 : prf 𝐏𝐀 f1 := by
      apply prf.axm step1
    let t1 : Term ℒₚₐ Empty :=
      S(S(LPA.null))
    let f2 : BoundedFormula ℒₚₐ Empty 1 :=
      (∼(LPA.null =' func LPA.Func.succ ![&0]))
    let f3 : BoundedFormula ℒₚₐ Empty 0 :=
      ∼ (LPA.null =' func LPA.Func.succ ![func LPA.Func.succ ![func LPA.Func.succ ![LPA.null] ] ])
    have step4 :  f2//[t1] = f3 := by
      simp[f2,t1,f3]
      simp[replace_bound_variable,BoundedFormula.subst,BoundedFormula.not]
      rfl
      sorry
    have step3 : prf 𝐏𝐀 to_prove := by
      rw[to_prove]
      apply prf.allE₂ t1 step2

    sorry
end Calculus

  /-- Proof that there is a homomorphism between 𝐏𝐀 and some Theory of ℒₜ -/
  example : Theory ℒₜ := LHom.onTheory Languages.ϕ 𝐏𝐀

  /-- A coercion from 𝐏𝐀 Axioms to 𝐏𝐀𝐓 Axioms as all 𝐏𝐀 Axioms are also
  𝐏𝐀𝐓 Axioms -/
  def to_lt_T : Theory ℒₚₐ → Theory ℒₜ := by
    repeat rewrite[Theory]
    repeat rewrite[Set]
    intro set
    intro φ
    sorry
  -- inductive axioms : Theory ℒₚₐ where
  -- | first :
