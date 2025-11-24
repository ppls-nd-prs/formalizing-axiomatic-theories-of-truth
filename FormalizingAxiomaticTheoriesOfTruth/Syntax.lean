import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Encoding

open FirstOrder
open Language

namespace FirstOrder.Language
namespace Term
variable {L : Language}{n : Nat}
def to_closed : L.Term (Fin 1 ⊕ Fin n) → L.Term (Empty ⊕ Fin n) → L.Term (Empty ⊕ Fin n)
| .var (.inl _), t_in => t_in
| .var (.inr v), _ => .var (.inr v)
| .func f ts, t => .func f (fun i => to_closed (ts i) t)
end Term

namespace BoundedFormula
open Term
variable {L : Language}
def to_prop_func : {n : Nat} → L.BoundedFormula (Fin 1) n → (L.Term (Empty ⊕ Fin n) → L.BoundedFormula Empty n)
| _, .falsum => fun _ => .falsum
| _, .equal t₁ t₂ => fun t_in => .equal (to_closed t₁ t_in) (to_closed t₂ t_in)
| _, .rel r ts => fun t_in => .rel r (fun i => to_closed (ts i) t_in)
| _, .imp φ₁ φ₂ => fun t_in => .imp (to_prop_func φ₁ t_in) (to_prop_func φ₂ t_in)
| _, .all φ => fun t_in => .all ((to_prop_func φ) (t_in.liftAt 1 1))
end BoundedFormula

namespace Formula
open Term
variable {L : Language}
@[simp]
def to_bf {α} : {n : Nat} → L.BoundedFormula α n → L.BoundedFormula α (n + 1) :=
  fun {n} => fun φ => @BoundedFormula.castLE _ _ n (n + 1) (by simp) φ
end Formula

/-- A language is arithmetic when it has +, ×, 0 and S. -/
class Arithmetical (L : Language) where
  zero_symbol : L.Functions 0
  succ_symbol : L.Functions 1
  mult_symbol : L.Functions 2
  add_symbol : L.Functions 2

scoped notation "S("t")" => Term.func Arithmetical.succ_symbol ![t]
scoped notation t₁ "add" t₂ => Term.func Arithmetical.add_symbol ![t₁, t₂]
scoped notation t₁ "mult" t₂ => Term.func Arithmetical.mult_symbol ![t₁, t₂]

variable {α : Type}{L : Language}[Arithmetical L]
@[simp]
def null : L.Term α :=
  Term.func Arithmetical.zero_symbol ![]

scoped notation "null" => null

@[simp]
def numeral : ℕ → L.Term α
  | .zero => null
  | .succ n => S(numeral n)

class SyntaxTheoretical (L : Language) where
  neg_symbol : L.Functions 1
  conj_symbol : L.Functions 2
  disj_symbol : L.Functions 2
  cond_symbol : L.Functions 2
  forall_symbol : L.Functions 1
  exists_symbol : L.Functions 1
  denote_symbol : L.Functions 1
  subs_symbol : L.Functions 3
  var_symbol : L.Relations 1
  const_symbol : L.Relations 1
  term_symbol : L.Relations 1
  clterm_symbol : L.Relations 1
  forml_symbol : L.Relations 1
  sentencel_symbol : L.Relations 1
  formlt_symbol : L.Relations 1
  sentencelt_symbol : L.Relations 1

  scoped notation n "⬝∧" m => Term.func SyntaxTheoretical.conj_symbol ![n,m]
  scoped notation n "⬝∨" m => Term.func SyntaxTheoretical.disj_symbol ![n,m]
  scoped notation "⬝∼" n => Term.func SyntaxTheoretical.neg_symbol ![n]
  scoped notation n "⬝⟹" m => Term.func SyntaxTheoretical.cond_symbol ![n,m]
  scoped notation "⬝∀" n => Term.func SyntaxTheoretical.forall_symbol ![n]
  scoped notation "⬝∃" n => Term.func SyntaxTheoretical.exists_symbol ![n]
  scoped notation "⬝°"n  => Term.func SyntaxTheoretical.denote_symbol ![n]
  scoped notation "Subs(" n "," x "," t ")" => Term.func SyntaxTheoretical.subs_symbol ![n, x, t]
  scoped notation "Var(" x ")" => BoundedFormula.rel SyntaxTheoretical.var_symbol ![x]
  scoped notation "Const(" c ")" => BoundedFormula.rel SyntaxTheoretical.const_symbol ![c]
  scoped notation "Trm(" t ")" => BoundedFormula.rel SyntaxTheoretical.term_symbol ![t]
  scoped notation "ClosedTerm(" t")" => BoundedFormula.rel SyntaxTheoretical.clterm_symbol ![t]
  scoped notation "FormL(" t ")" => BoundedFormula.rel SyntaxTheoretical.forml_symbol ![t]
  scoped notation "SentenceL(" t ")" => BoundedFormula.rel SyntaxTheoretical.sentencel_symbol ![t]
  scoped notation "FormLT(" t ")" => BoundedFormula.rel SyntaxTheoretical.formlt_symbol ![t]
  scoped notation "SentenceLT(" t ")" => BoundedFormula.rel SyntaxTheoretical.sentencelt_symbol ![t]

  scoped prefix:arg "#" => FirstOrder.Language.Term.var ∘ Sum.inl

end FirstOrder.Language

namespace Languages
  namespace LPA
    inductive Func : ℕ → Type _ where
      | zero_symbol : Func 0
      | succ_symbol : Func 1
      | add_symbol : Func 2
      | mult_symbol : Func 2
      -- | neg_symbol : Func 1
      -- | conj_symbol : Func 2
      -- | disj_symbol : Func 2
      -- | cond_symbol : Func 2
      -- | forall_symbol : Func 1
      -- | exists_symbol : Func 1
      -- | denote_symbol : Func 1
      -- | subs_symbol : Func 3
      deriving DecidableEq

    -- inductive Rel : ℕ → Type _ where
    --   | var_symbol : Rel 1
    --   | const_symbol : Rel 1
    --   | term_symbol : Rel 1
    --   | clterm_symbol : Rel 1
    --   | forml_symbol : Rel 1
    --   | sentencel_symbol : Rel 1
    --   | formlt_symbol : Rel 1
    --   | sentencelt_symbol : Rel 1
    --   deriving DecidableEq

    def signature : Language :=
      ⟨Func, fun _ => Empty⟩

    abbrev ℒ := signature

    instance : Arithmetical ℒ where
      zero_symbol := LPA.Func.zero_symbol
      succ_symbol := LPA.Func.succ_symbol
      add_symbol := LPA.Func.add_symbol
      mult_symbol := LPA.Func.mult_symbol

    -- instance : SyntaxTheoretical ℒ where
    --   neg_symbol := LPA.Func.neg_symbol
    --   conj_symbol := LPA.Func.conj_symbol
    --   disj_symbol := LPA.Func.disj_symbol
    --   cond_symbol := LPA.Func.conj_symbol
    --   forall_symbol := LPA.Func.forall_symbol
    --   exists_symbol := LPA.Func.exists_symbol
    --   denote_symbol := LPA.Func.denote_symbol
    --   subs_symbol := LPA.Func.subs_symbol
    --   var_symbol := LPA.Rel.var_symbol
    --   const_symbol := LPA.Rel.const_symbol
    --   term_symbol := LPA.Rel.term_symbol
    --   clterm_symbol := LPA.Rel.clterm_symbol
    --   forml_symbol := LPA.Rel.forml_symbol
    --   sentencel_symbol := LPA.Rel.sentencel_symbol
    --   formlt_symbol := LPA.Rel.formlt_symbol
    --   sentencelt_symbol := LPA.Rel.sentencelt_symbol

    @[simp]
    def num_inv {α} : ℒ.Term α → Option Nat
    | .var _ => none
    | .func .zero_symbol _ => some 0
    | .func .succ_symbol ts => if h : (num_inv (ts 0)).isSome then some (((num_inv (ts 0)).get h) + 1) else none
    | _ => none

    lemma num_has_inv {α} : ∀{n}, @num_inv α (numeral n) = n := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        simp[ih]

    @[simp]
    lemma num_inj {α} : Function.Injective (@numeral α ℒ _) := by
      unfold Function.Injective
      intro a₁ a₂ h
      have inv_eq : @num_inv α (numeral a₁) = @num_inv α (numeral a₂) := by
        rw[h]
      simp[num_has_inv] at inv_eq
      exact inv_eq

  end LPA

  namespace L_T
    inductive Func : ℕ → Type _ where
      | zero_symbol : Func 0
      | succ_symbol : Func 1
      | add_symbol : Func 2
      | mult_symbol : Func 2
      -- | neg_symbol : Func 1
      -- | conj_symbol : Func 2
      -- | disj_symbol : Func 2
      -- | cond_symbol : Func 2
      -- | forall_symbol : Func 1
      -- | exists_symbol : Func 1
      -- | denote_symbol : Func 1
      -- | subs_symbol : Func 3
      deriving DecidableEq

    inductive Rel : ℕ → Type _ where
    --   | var_symbol : Rel 1
    --   | const_symbol : Rel 1
      | t_symbol : Rel 1
    --   | term_symbol : Rel 1
    --   | clterm_symbol : Rel 1
    --   | forml_symbol : Rel 1
    --   | sentencel_symbol : Rel 1
    --   | formlt_symbol : Rel 1
    --   | sentencelt_symbol : Rel 1
      deriving DecidableEq

    def signature : Language :=
      ⟨Func, Rel⟩

    abbrev ℒₜ := signature

    instance : Arithmetical ℒₜ where
      zero_symbol := L_T.Func.zero_symbol
      add_symbol := L_T.Func.add_symbol
      mult_symbol := L_T.Func.mult_symbol
      succ_symbol := L_T.Func.succ_symbol

    -- instance : SyntaxTheoretical ℒₜ where
    --   neg_symbol := L_T.Func.neg_symbol
    --   conj_symbol := L_T.Func.conj_symbol
    --   disj_symbol := L_T.Func.disj_symbol
    --   cond_symbol := L_T.Func.conj_symbol
    --   forall_symbol := L_T.Func.forall_symbol
    --   exists_symbol := L_T.Func.exists_symbol
    --   denote_symbol := L_T.Func.denote_symbol
    --   subs_symbol := L_T.Func.subs_symbol
    --   var_symbol := L_T.Rel.var_symbol
    --   const_symbol := L_T.Rel.const_symbol
    --   term_symbol := L_T.Rel.term_symbol
    --   clterm_symbol := L_T.Rel.clterm_symbol
    --   forml_symbol := L_T.Rel.forml_symbol
    --   sentencel_symbol := L_T.Rel.sentencel_symbol
    --   formlt_symbol := L_T.Rel.formlt_symbol
    --   sentencelt_symbol := L_T.Rel.sentencelt_symbol
  end L_T

  open LPA L_T
  def onFunction ⦃n : Nat⦄ : ℒ.Functions n → ℒₜ.Functions n
  | .zero_symbol => .zero_symbol
  -- | .subs_symbol => .subs_symbol
  -- | .denote_symbol => .denote_symbol
  -- | .exists_symbol => .exists_symbol
  -- | .forall_symbol => .forall_symbol
  -- | .cond_symbol => .cond_symbol
  -- | .disj_symbol => .disj_symbol
  -- | .conj_symbol => .conj_symbol
  -- | .neg_symbol => .neg_symbol
  | .mult_symbol => .mult_symbol
  | .add_symbol => .add_symbol
  | .succ_symbol => .succ_symbol

  def onRelation ⦃n : Nat⦄ : ℒ.Relations n → ℒₜ.Relations n := by
  intro a
  cases a
  -- | .var_symbol => .var_symbol
  -- | .sentencelt_symbol => .sentencelt_symbol
  -- | .formlt_symbol => .formlt_symbol
  -- | .sentencel_symbol => .sentencel_symbol
  -- | .forml_symbol => .forml_symbol
  -- | .clterm_symbol => .clterm_symbol
  -- | .term_symbol => .term_symbol
  -- | .const_symbol => .const_symbol

  def ϕ : LHom ℒ ℒₜ where
    onFunction := onFunction
    onRelation := onRelation

  def lt_l_onFunction ⦃n : Nat⦄ : ℒₜ.Functions n → ℒ.Functions n
  | .zero_symbol => .zero_symbol
  -- | .subs_symbol => .subs_symbol
  -- | .denote_symbol => .denote_symbol
  -- | .exists_symbol => .exists_symbol
  -- | .forall_symbol => .forall_symbol
  -- | .cond_symbol => .cond_symbol
  -- | .disj_symbol => .disj_symbol
  -- | .conj_symbol => .conj_symbol
  -- | .neg_symbol => .neg_symbol
  | .mult_symbol => .mult_symbol
  | .add_symbol => .add_symbol
  | .succ_symbol => .succ_symbol

  def lt_l_onTerm {α} {n : Nat} : ℒₜ.Term (α ⊕ Fin n) → ℒ.Term (α ⊕ Fin n)
  | .var v => .var v
  | .func f ts => .func (lt_l_onFunction f) (fun i => lt_l_onTerm (ts i))

  instance {α n} : Coe (ℒₜ.Term (α ⊕ Fin n)) (ℒ.Term (α ⊕ Fin n)) where
    coe := lt_l_onTerm
  instance {α n} : Coe (ℒ.Term (α ⊕ Fin n)) (ℒₜ.Term (α ⊕ Fin n)) where
    coe := ϕ.onTerm
  instance {α n} : Coe (ℒ.BoundedFormula α n) (ℒₜ.BoundedFormula α n) where
    coe := ϕ.onBoundedFormula
end Languages
