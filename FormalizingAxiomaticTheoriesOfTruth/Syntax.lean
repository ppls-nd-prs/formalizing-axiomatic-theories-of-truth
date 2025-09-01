import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Encoding

open FirstOrder
open Language

namespace FirstOrder.Language
/-- A language is arithmetic when it has +, ×, 0 and S. -/
class Arithmetic (L : Language) where
  zero_symbol : L.Functions 0
  succ_symbol : L.Functions 1
  mult_symbol : L.Functions 2
  add_symbol : L.Functions 2

scoped notation "S("t")" => Term.func Arithmetic.succ_symbol ![t]
scoped notation t₁ "add" t₂ => Term.func Arithmetic.add_symbol ![t₁, t₂]
scoped notation t₁ "mult" t₂ => Term.func Arithmetic.mult_symbol ![t₁, t₂]

variable {α : Type}{L : Language}[Arithmetic L]
@[simp]
def null : L.Term α :=
  Term.func Arithmetic.zero_symbol ![]

scoped notation "null" => null

@[simp]
def numeral : ℕ → L.Term α
  | .zero => null
  | .succ n => .func Arithmetic.succ_symbol ![numeral n]

end FirstOrder.Language

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
    def toStr : Term L ℕ → String :=
      fun t : Term L ℕ =>
        match t with
        | .var k => "⬝" ++ toString k
        | .func (l := 0) c _ => toString c
        | .func (l := _ + 1) f ts => toString f ++ "(" ++ String.vecToStr (fun i => toStr (ts i)) ++ ")"

    instance : Repr (Term L ℕ) := ⟨fun t _ => toStr t⟩
    instance : ToString (Term L ℕ) := ⟨toStr⟩

    def toStr_oplus : Term L (α ⊕ β) → String :=
      fun t : Term L (α ⊕ β) =>
        match t with
        | .var k =>
          match k with
            | (Sum.inl l) => "#" ++ toString l
            | (Sum.inr l) => "&" ++ toString l
        | .func (l := 0) c _ => toString c
        | .func (l := _ + 1) f ts => toString f ++ "(" ++ String.vecToStr (fun i => toStr_oplus (ts i)) ++ ")"

    instance : Repr (Term L (α ⊕ β)) := ⟨fun t _ => toStr_oplus t⟩
    instance : ToString (Term L (α ⊕ β)) := ⟨toStr_oplus⟩
  end ToString
end Term

namespace BoundedFormula
  section ToString
    variable {L : Language} {α : Type} {n : ℕ}
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

 @[simp]
  def to_extra_fin {n : ℕ} (v : Fin n) : Fin (n + 1) :=
    match v with
    | .mk val isLt => by
      have step1 : n < n + 1 := by
        simp
      have step2 : val < n + 1 := by
        apply Nat.lt_trans isLt step1
      apply Fin.mk val step2

variable {L : Language}

namespace Substitution
def term_substitution {n : ℕ} (t : L.Term (ℕ ⊕ Fin n)) : L.Term (ℕ ⊕ Fin n) → L.Term (ℕ ⊕ Fin n)
| .var v => if v = (.inl 0) then t else (.var v)
| .func f ts => .func f (fun i => term_substitution t (ts i))

def up_bv {n : ℕ} : L.Term (α ⊕ Fin n) → L.Term (α ⊕ Fin (n + 1))
| .var v =>
  match v with
  | .inl m =>
    .var (.inl m)
  | .inr m => .var (.inr (to_extra_fin m))
| .func f ts => .func f (fun i => up_bv (ts i))

def formula_substitution : {n : ℕ} → (t : L.Term (ℕ ⊕ Fin n)) → L.BoundedFormula ℕ n → L.BoundedFormula ℕ n
| _, _, .falsum => .falsum
| _, t, .equal t₁ t₂ => .equal (term_substitution t t₁) (term_substitution t t₂)
| _, t, .rel R ts => .rel R (fun i => term_substitution t (ts i))
| _, t, .imp φ ψ => .imp (formula_substitution t φ) (formula_substitution t ψ)
| _, t, .all φ => .all (formula_substitution (up_bv t) φ)

notation φ"/["t"]" => formula_substitution t φ

def bv_term_substitution {n : ℕ} (t : L.Term (ℕ ⊕ Fin (n + 1))) : L.Term (ℕ ⊕ Fin n) → L.Term (ℕ ⊕ Fin (n + 1))
| .var v => if v = (.inl 0) then t else (up_bv (.var  v))
| .func f ts => .func f (fun i => term_substitution t (up_bv (ts i)))

def bv_formula_substitution : {n : ℕ} → (t : L.Term (ℕ ⊕ Fin (n + 1))) → L.BoundedFormula ℕ n → L.BoundedFormula ℕ (n + 1)
| _, _, .falsum => .falsum
| _, t, .equal t₁ t₂ => .equal (bv_term_substitution t t₁) (bv_term_substitution t t₂)
| _, t, .rel R ts => .rel R (fun i => term_substitution t (up_bv (ts i)))
| _, t, .imp φ ψ => .imp (bv_formula_substitution t φ) (bv_formula_substitution t ψ)
| _, t, .all φ => .all (bv_formula_substitution (up_bv t) φ)

notation φ"/bv["t"]" => bv_formula_substitution t φ
end Substitution

inductive simple_func : ℕ → Type where
  | one : simple_func 0

def simple_l : Language := ⟨simple_func, (fun _ => Empty)⟩

def φ : simple_l.BoundedFormula ℕ 0 := (.var (.inl 0)) =' (.func simple_func.one ![])
def ψ : simple_l.BoundedFormula ℕ 0 := (.func simple_func.one ![]) =' (.func simple_func.one ![])
def t₁ : simple_l.Term (ℕ ⊕ Fin 0) := .func simple_func.one ![]

open Substitution
example : (φ/[t₁]) = ψ  := by
  simp[formula_substitution,t₁,φ,ψ,Term.bdEqual,term_substitution,Matrix.empty_eq]

def φ₂ : simple_l.BoundedFormula ℕ 0 := (.var (.inl 0)) =' (.func simple_func.one ![])
def ψ₂ : simple_l.BoundedFormula ℕ 1 := (.var (.inr 0)) =' (.func simple_func.one ![])
def t₂ : simple_l.Term (ℕ ⊕ Fin 1) := (.var (.inr 0))

example : (φ₂/bv[t₂]) = ψ₂  := by
  simp[bv_formula_substitution,t₂,φ₂,ψ₂,Term.bdEqual,bv_term_substitution,Matrix.empty_eq]

end BoundedFormula

namespace Languages
  namespace LPA
    inductive Func : ℕ → Type _ where
      | zero_symbol : Func 0
      | succ_symbol : Func 1
      | add_symbol : Func 2
      | mult_symbol : Func 2
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
      | term : Rel 1
      | clterm: Rel 1
      | forml : Rel 1
      | sentencel: Rel 1
      | formlt : Rel 1
      | sentencelt : Rel 1
      deriving DecidableEq

    def signature : Language :=
      ⟨Func, Rel⟩

    def funToStr {n}: Func n → String
      | .zero_symbol => "0"
      | .succ_symbol => "S"
      | .add_symbol => "+"
      | .mult_symbol => "×"
      | .neg => "𝑛𝑒𝑔"
      | .conj => "𝑐𝑜𝑛𝑗"
      | .disj => "𝑑𝑖𝑠𝑗"
      | .cond => "𝑐𝑜𝑛𝑑"
      | .forall => "𝑎𝑙𝑙"
      | .exists => "𝑒𝑥"
      | .denote => "𝑑𝑒𝑛"
      | .subs => "𝑠𝑢𝑏𝑠"
    instance {n : ℕ}: ToString (signature.Functions n) := ⟨funToStr⟩

    def relToStr {n} : signature.Relations n → String
      | .var => "𝑣𝑎𝑟"
      | .const => "𝑐𝑜𝑛𝑠𝑡"
      | .term => "𝑡𝑒𝑟𝑚"
      | .clterm => "𝑐𝑙𝑡𝑒𝑟𝑚"
      | .forml => "𝑓𝑜𝑟𝑚𝑙"
      | .sentencel => "𝑠𝑒𝑛𝑡𝑙"
      | .formlt => "𝑓𝑜𝑟𝑚𝑙𝑡"
      | .sentencelt => "𝑠𝑒𝑛𝑡𝑙𝑡"
    instance {n} : ToString (signature.Relations n) := ⟨relToStr⟩

    /-
    Useful notation
    -/
    scoped notation n "times" m => Term.func Func.mult ![n,m]
    scoped notation n "⬝∧" m => Term.func Func.conj ![n,m]
    scoped notation n "⬝∨" m => Term.func Func.disj ![n,m]
    scoped notation "⬝∼" n => Term.func Func.neg ![n]
    scoped notation n "⬝⟹" m => Term.func Func.cond ![n,m]
    scoped notation "⬝∀" n => Term.func Func.forall ![n]
    scoped notation "⬝∃" n => Term.func Func.exists ![n]
    scoped notation "⬝°"n  => Term.func Func.denote ![n]
    scoped notation "Subs(" n "," x "," t ")" => Term.func Func.subs ![n, x, t]
    scoped notation "Var(" x ")" => BoundedFormula.rel Rel.var ![x]
    scoped notation "Const(" c ")" => BoundedFormula.rel Rel.const ![c]
    scoped notation "Trm(" t ")" => BoundedFormula.rel Rel.term ![t]
   scoped notation "ClosedTerm(" t")" => BoundedFormula.rel Rel.clterm ![t]
    scoped notation "FormL(" t ")" => BoundedFormula.rel Rel.forml ![t]
    scoped notation "SentenceL(" t ")" => BoundedFormula.rel Rel.sentencel ![t]
    scoped notation "FormLT(" t ")" => BoundedFormula.rel Rel.formlt ![t]
    scoped notation "SentenceLT(" t ")" => BoundedFormula.rel Rel.sentencelt ![t]
    abbrev ℒ := signature
    scoped[Languages] prefix:arg "#" => FirstOrder.Language.Term.var ∘ Sum.inl

    instance : Arithmetic ℒ where
      zero_symbol := LPA.Func.zero_symbol
      succ_symbol := LPA.Func.succ_symbol
      add_symbol := LPA.Func.add_symbol
      mult_symbol := LPA.Func.mult_symbol

    section Coding
      variable {k : ℕ}
      def Func_enc : signature.Functions k → ℕ
        | .zero_symbol => Nat.pair 0 0 + 1
        | .succ_symbol => Nat.pair 1 0 + 1
        | .denote => Nat.pair 1 1 + 1
        | .exists => Nat.pair 1 2 + 1
        | .forall => Nat.pair 1 3 + 1
        | .neg => Nat.pair 1 4 + 1
        | .add_symbol => Nat.pair 2 0 + 1
        | .mult_symbol => Nat.pair 2 1 + 1
        | .cond => Nat.pair 2 2 + 1
        | .disj => Nat.pair 2 3 + 1
        | .conj => Nat.pair 2 4 + 1
        | .subs => Nat.pair 3 0 + 1

      def Func_dec : (n : ℕ) → Option (signature.Functions k)
        | 0 => none
        | e + 1 =>
          match k with
            | 0 =>
              match e.unpair.2 with
                | 0 => some (.zero_symbol)
                | _ => none
            | 1 =>
              match e.unpair.2 with
                | 0 => some (.succ_symbol)
                | 1 => some (.denote)
                | 2 => some (.exists)
                | 3 => some (.forall)
                | 4 => some (.neg)
                | _ => none
            | 2 =>
              match e.unpair.2 with
                | 0 => some (.add_symbol)
                | 1 => some (.mult_symbol)
                | 2 => some (.cond)
                | 3 => some (.disj)
                | 4 => some (.conj)
                | _ => none
            | 3 =>
              match e.unpair.2 with
                | 0 => some (.subs)
                | _ => none
            | _ => none

      lemma Func_enc_dec : ∀ f : signature.Functions k, Func_dec (Func_enc f) = (some f) := by
        intro h
        induction h
        simp [Func_enc,Nat.pair,Func_dec]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

      instance enc_f : Encodable (signature.Functions k) where
        encode := Func_enc
        decode := Func_dec
        encodek := Func_enc_dec

      def Rel_enc : signature.Relations k → ℕ
        | .var => Nat.pair 1 0 + 1
        | .const => Nat.pair 1 1 + 1
        | .term => Nat.pair 1 2 + 1
        | .clterm => Nat.pair 1 3 + 1
        | .forml => Nat.pair 1 4 + 1
        | .sentencel => Nat.pair 1 5 + 1
        | .formlt => Nat.pair 1 6 + 1
        | .sentencelt => Nat.pair 1 7 + 1

      def Rel_dec : (n : ℕ) → Option (signature.Relations k)
        | 0 => none
        | e + 1 =>
          match k with
            | 1 =>
              match e.unpair.2 with
                | 0 => some .var
                | 1 => some .const
                | 2 => some .term
                | 3 => some .clterm
                | 4 => some .forml
                | 5 => some .sentencel
                | 6 => some .formlt
                | 7 => some .sentencelt
                | _ => none
            | _ => none

      lemma Rel_enc_dec : ∀ f : signature.Relations k, Rel_dec (Rel_enc f) = (some f) := by
        intro h
        induction h
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

      instance enc_r : Encodable (signature.Relations k) where
        encode := Rel_enc
        decode := Rel_dec
        encodek := Rel_enc_dec

    end Coding
  end LPA

  namespace L_T

    inductive Func : ℕ → Type _ where
      | null : Func 0
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

    variable {n : ℕ}
    def funToStr : Func n → String
      | .null => "0"
      | .succ => "S"
      | .add => "+"
      | .mult => "×"
      | .neg => "𝑛𝑒𝑔"
      | .conj => "𝑐𝑜𝑛𝑗"
      | .disj => "𝑑𝑖𝑠𝑗"
      | .cond => "𝑐𝑜𝑛𝑑"
      | .forall => "𝑎𝑙𝑙"
      | .exists => "𝑒𝑥"
      | .denote => "𝑑𝑒𝑛"
      | .subs => "𝑠𝑢𝑏𝑠"
    instance : ToString (signature.Functions n) := ⟨funToStr⟩

    def relToStr : signature.Relations n → String
      | .var => "𝑣𝑎𝑟"
      | .const => "𝑐𝑜𝑛𝑠𝑡"
      | .t => "T"
      | .term => "𝑡𝑒𝑟𝑚"
      | .clterm => "𝑐𝑙𝑡𝑒𝑟𝑚"
      | .forml => "𝑓𝑜𝑟𝑚𝑙"
      | .sentencel => "𝑠𝑒𝑛𝑡𝑙"
      | .formlt => "𝑓𝑜𝑟𝑚𝑙𝑡"
      | .sentencelt => "𝑠𝑒𝑛𝑡𝑙𝑡"
    instance : ToString (signature.Relations n) := ⟨relToStr⟩

    /-
    Some useful notation
    -/
    scoped notation "T(" n ")" => BoundedFormula.rel Rel.t ![n]
    -- scoped notation "S(" n ")" => Term.func Func.succ ![n]
--    scoped notation "zero" => Term.func Func.zero ![]
    -- scoped notation n "add" m => Term.func Func.add ![n,m]
    scoped notation n "times" m => Term.func Func.mult ![n,m]
    scoped notation n "⬝∧" m => Term.func Func.conj ![n,m]
    scoped notation n "⬝∨" m => Term.func Func.disj ![n,m]
    scoped notation "⬝∼" n => Term.func Func.neg ![n]
    scoped notation n "⬝⟹" m => Term.func Func.cond ![n,m]
    scoped notation "⬝∀" n => Term.func Func.forall ![n]    variable {α : Type}
    scoped notation "⬝∃" n => Term.func Func.exists ![n]
    scoped notation "⬝°" n  => Term.func Func.denote ![n]
    scoped notation "Subs(" n "," x "," t ")" => Term.func Func.subs ![n,x,t]
    scoped notation "Var(" x ")" => BoundedFormula.rel L_T.Rel.var ![x]
    scoped notation "Const(" c ")" => BoundedFormula.rel L_T.Rel.const ![c]
    scoped notation "Trm(" t ")" => BoundedFormula.rel Rel.term ![t]
    scoped notation "ClosedTerm(" t")" => BoundedFormula.rel L_T.Rel.clterm ![t]
    scoped notation "FormL(" t ")" => BoundedFormula.rel L_T.Rel.forml ![t]
    scoped notation "SentenceL(" t ")" => BoundedFormula.rel L_T.Rel.sentencel ![t]
    scoped notation "FormLT(" t ")" => BoundedFormula.rel L_T.Rel.formlt ![t]
    scoped notation "SentenceLT(" t ")" => BoundedFormula.rel L_T.Rel.sentencelt ![t]
    abbrev ℒₜ := signature

    instance : Arithmetic ℒₜ where
      zero_symbol := L_T.Func.null
      add_symbol := L_T.Func.add
      mult_symbol := L_T.Func.mult
      succ_symbol := L_T.Func.succ

  /-- Gives whether a BoundedFormula contains a T predicate-/
  @[simp] def contains_T {n} : ℒₜ.BoundedFormula α n → Prop
  | .rel L_T.Rel.t _ => true
  | .imp f₁ f₂ => contains_T f₁ ∨ contains_T f₂
  | .all f => contains_T f
  | _ => false

  namespace FirstOrder.Language.Sentence
    variable {L : Language}
    open Languages
    @[simp]
    def contains_T (s : ℒₜ.Sentence) : Prop := L_T.contains_T s
  end FirstOrder.Language.Sentence

  /-- Proves that contains_T is a decidable predicate-/
  def decPred_contains_T : {n : ℕ} → (a : ℒₜ.BoundedFormula α n) → Decidable (contains_T a)
  | _, .falsum => by
    apply Decidable.isFalse
    simp
  | _, .equal t₁ t₂ => by
    apply Decidable.isFalse
    simp
  | _, .rel R ts => by cases R with
    | t =>
      apply Decidable.isTrue
      simp
    | _ =>
      apply Decidable.isFalse
      simp
  | _, .imp f₁ f₂ => by
    simp[contains_T]
    apply decPred_contains_T at f₁
    apply decPred_contains_T at f₂
    apply instDecidableOr
  | _, .all f => by
    apply decPred_contains_T at f
    simp
    exact f

  instance : DecidablePred (@contains_T ℕ 0) := decPred_contains_T
  instance : DecidablePred (@contains_T Empty 0) := decPred_contains_T

    section Coding
      variable {k : ℕ}
      def Func_enc : signature.Functions k → ℕ
        | .null => Nat.pair 0 0 + 1
        | .succ => Nat.pair 1 0 + 1
        | .denote => Nat.pair 1 1 + 1
        | .exists => Nat.pair 1 2 + 1
        | .forall => Nat.pair 1 3 + 1
        | .neg => Nat.pair 1 4 + 1
        | .add => Nat.pair 2 0 + 1
        | .mult => Nat.pair 2 1 + 1
        | .cond => Nat.pair 2 2 + 1
        | .disj => Nat.pair 2 3 + 1
        | .conj => Nat.pair 2 4 + 1
        | .subs => Nat.pair 3 0 + 1

      def Func_dec : (n : ℕ) → Option (signature.Functions k)
        | 0 => none
        | e + 1 =>
          match k with
            | 0 =>
              match e.unpair.2 with
                | 0 => some (.null)
                | _ => none
            | 1 =>
              match e.unpair.2 with
                | 0 => some (.succ)
                | 1 => some (.denote)
                | 2 => some (.exists)
                | 3 => some (.forall)
                | 4 => some (.neg)
                | _ => none
            | 2 =>
              match e.unpair.2 with
                | 0 => some (.add)
                | 1 => some (.mult)
                | 2 => some (.cond)
                | 3 => some (.disj)
                | 4 => some (.conj)
                | _ => none
            | 3 =>
              match e.unpair.2 with
                | 0 => some (.subs)
                | _ => none
            | _ => none

      lemma Func_enc_dec : ∀ f : signature.Functions k, Func_dec (Func_enc f) = (some f) := by
        intro h
        induction h
        simp [Func_enc,Nat.pair,Func_dec]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

      instance enc_f : Encodable (signature.Functions k) where
        encode := Func_enc
        decode := Func_dec
        encodek := Func_enc_dec

      def Rel_enc : signature.Relations k → ℕ
        | .var => Nat.pair 1 0 + 1
        | .const => Nat.pair 1 1 + 1
        | .term => Nat.pair 1 2 + 1
        | .clterm => Nat.pair 1 3 + 1
        | .forml => Nat.pair 1 4 + 1
        | .sentencel => Nat.pair 1 5 + 1
        | .formlt => Nat.pair 1 6 + 1
        | .sentencelt => Nat.pair 1 7 + 1
        | .t => Nat.pair 1 8 + 1

      def Rel_dec : (n : ℕ) → Option (signature.Relations k)
        | 0 => none
        | e + 1 =>
          match k with
            | 1 =>
              match e.unpair.2 with
                | 0 => some .var
                | 1 => some .const
                | 2 => some .term
                | 3 => some .clterm
                | 4 => some .forml
                | 5 => some .sentencel
                | 6 => some .formlt
                | 7 => some .sentencelt
                | 8 => some .t
                | _ => none
            | _ => none

      lemma Rel_enc_dec : ∀ f : signature.Relations k, Rel_dec (Rel_enc f) = (some f) := by
        intro h
        induction h
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]


      instance enc_r : Encodable (signature.Relations k) where
        encode := Rel_enc
        decode := Rel_dec
        encodek := Rel_enc_dec

    end Coding
  end L_T

namespace TermEncoding
  variable {L : Language}[∀i, Encodable (L.Functions i)][∀i, Encodable (L.Relations i)]
  /-- Encodes terms as natural numbers -/
  def term_tonat : Term L (ℕ ⊕ Fin 0) → ℕ :=
    fun t => Encodable.encodeList (Term.listEncode t)
  def sentence_term_tonat : Term L (Empty ⊕ Fin 0) → ℕ :=
    fun t => Encodable.encodeList (Term.listEncode t)

 /-- Encodes BoundedFormulas as natural numbers -/
  def sent_tonat : BoundedFormula L Empty 0 → ℕ :=
    fun f => Encodable.encodeList (BoundedFormula.listEncode f)
  def formula_tonat {n : ℕ} : BoundedFormula L ℕ n → ℕ :=
    fun f => Encodable.encodeList (BoundedFormula.listEncode f)

  scoped notation "⌜" φ "⌝" => numeral (formula_tonat φ)
  scoped notation "⌜" t₁ "⌝" => numeral (term_tonat t₁)

end TermEncoding

  open LPA
  open L_T

  /--
  A coercion from PA.lpa formulas to L_T.lt formulas as all lpa formulas are
  also lt formulas
  -/
  def to_lt_func ⦃arity : ℕ⦄ : (ℒ.Functions arity) → (ℒₜ.Functions arity)
    | .zero_symbol => .null
    | .succ_symbol => .succ
    | .add_symbol => .add
    | .mult_symbol => .mult
    | .neg => .neg
    | .conj => .conj
    | .disj => .disj
    | .cond => .cond
    | .forall => .forall
    | .exists => .exists
    | .denote => .denote
    | .subs => .subs

  def to_lt_rel ⦃n : ℕ⦄ : (ℒ.Relations n) → (ℒₜ.Relations n)
      | .var => .var
      | .const => .const
      | .term => .term
      | .clterm => .clterm
      | .forml => .forml
      | .sentencel => .sentencel
      | .formlt => .formlt
      | .sentencelt => .sentencelt

  def to_lt_term : ℒ.Term (α ⊕ Fin n) → ℒₜ.Term (α ⊕ Fin n)
    | .var v => match v with
      | .inl m => #m
      | .inr m => &m
    | .func f ts => .func (to_lt_func f) fun i => to_lt_term (ts i)

  def to_lt_bf : {n : ℕ} → ℒ.BoundedFormula α n → ℒₜ.BoundedFormula α n
    | _, .falsum => .falsum
    | _, .equal t₁ t₂ => .equal (to_lt_term t₁) (to_lt_term t₂)
    | _, .rel R ts => .rel (to_lt_rel R) fun i => to_lt_term (ts i)
    | _, .imp φ ψ => .imp (to_lt_bf φ) (to_lt_bf ψ)
    | _, .all φ => .all (to_lt_bf φ)

  instance : Coe (Formula ℒ ℕ) (Formula ℒₜ ℕ) where
    coe := to_lt_bf
  instance : Coe (Sentence ℒ) (Sentence ℒₜ) where
    coe := to_lt_bf
  instance : Coe (Term ℒ (Empty ⊕ Fin 0)) (Term ℒₜ (Empty ⊕ Fin 0)) where
    coe := to_lt_term
  instance : Coe (Theory ℒ) (Theory ℒₜ) where
    coe := fun t => t.image to_lt_bf

end Languages

namespace FirstOrder.Language.BoundedFormula
  variable {L : Language}{α : Type}{n : ℕ}

  def land (f₁ f₂: BoundedFormula L α n) :=
    ∼(f₁ ⟹ ∼f₂)
  scoped notation f₁ "∧'" f₂ => land f₁ f₂
  def lor (f₁ f₂ : BoundedFormula L α n) :=
    ((∼f₁) ⟹ f₂)
  scoped notation f₁ "∨'" f₂ => lor f₁ f₂
end FirstOrder.Language.BoundedFormula
