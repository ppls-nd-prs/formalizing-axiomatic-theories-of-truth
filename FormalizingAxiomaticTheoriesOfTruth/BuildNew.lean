import Foundation.Logic.Predicate.Language
import Foundation.FirstOrder.Arith.Theory
import Foundation.FirstOrder.Arith.PeanoMinus

open LO
open FirstOrder
/-
# Definitions for the language L_T
-/
namespace Formula
inductive Func : ℕ → Type where
  | zero : Func 0
  | succ : Func 1
  | add : Func 2
  | mult : Func 2

inductive Rel : ℕ → Type where
  | t : Rel 1
  | eq : Rel 2

def signature : Language where
  Func := Func
  Rel := Rel

/-
# Useful notation
-/
prefix:60 "pt_succ" => Semiterm.func Func.succ
prefix:60 "pt_eq" => Semiformula.rel Rel.eq
prefix:60 "pt_zero" => Semiterm.func Func.zero
prefix:60 "pt_add" => Semiterm.func Func.add
prefix:60 "pt_mult" => Semiterm.func Func.mult

/-
# Some useful terms
-/
def null : SyntacticTerm signature :=
  pt_zero ![]
def numeral : ℕ → SyntacticTerm signature
  | .zero => pt_zero ![]
  | .succ n => pt_succ ![numeral n]

def funToStr {n}: Func n → String
  | .zero => "0"
  | .succ => "S"
  | .add => "+"
  | .mult => "\\times"
instance : ToString (Func n) := ⟨funToStr⟩

def relToStr {n} : Rel n → String
| .t => "T"
| .eq => "="

instance : ToString (Rel n) := ⟨relToStr⟩

def Func_enc : Func k → ℕ
  | .zero => Nat.pair 0 0 + 1
  | .succ => Nat.pair 1 0 + 1
  | .add => Nat.pair 2 0 + 1
  | .mult => Nat.pair 2 1 + 1

def Func_dec : (n : ℕ) → Option (Func k)
  | 0 => none
  | e + 1 =>
    match k with
      | 0 =>
        match e.unpair.2 with
          | 0 => some (Func.zero)
          | _ => none
      | 1 =>
        match e.unpair.2 with
          | 0 => some (Func.succ)
          | _ => none
      | 2 =>
        match e.unpair.2 with
          | 0 => some (Func.add)
          | 1 => some (Func.mult)
          | _ => none
      | _ => none

lemma Func_enc_dec {k : ℕ}: ∀ f : Func k, Func_dec (Func_enc f) = (some f) := by
  intro h
  induction h
  simp [Func_enc,Nat.pair,Func_dec]
  simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
  simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
  simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

instance enc_f (k : ℕ) : Encodable (signature.Func k) where
  encode := Func_enc
  decode := Func_dec
  encodek := Func_enc_dec

def Rel_enc : Rel k → ℕ
  | .t => Nat.pair 1 0 + 1
  | .eq => Nat.pair 2 0 + 1

def Rel_dec : (n : ℕ) → Option (Rel k)
  | 0 => none
  | e + 1 =>
    match k with
      | 1 =>
        match e.unpair.2 with
          | 0 => some .t
          | _ => none
      | 2 =>
        match e.unpair.2 with
          | 0 => some (Rel.eq)
          | _ => none
      | _ => none

lemma Rel_enc_dec {k : ℕ}: ∀ f : Rel k, Rel_dec (Rel_enc f) = (some f) := by
  intro h
  induction h
  simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
  simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

instance enc_r (k : ℕ) : Encodable (signature.Rel k) where
  encode := Rel_enc
  decode := Rel_dec
  encodek := Rel_enc_dec

def contains_T {n : ℕ}: (Semiformula signature ℕ n) → Bool
| .verum => false
| .falsum => false
| .rel .eq _ => false
| .rel .t _ => true
| .nrel .eq _ => false
| .nrel .t _ => true
| .and φ ψ => (contains_T φ) ∨ (contains_T ψ)
| .or φ ψ => (contains_T φ) ∨ (contains_T ψ)
| .all φ => (contains_T φ)
| .ex φ => (contains_T φ)

#eval not true

/-
# Definitions for the PAT theory
-/
namespace PAT
open Formula
infixr:60 " pt_bi_imp " => LogicalConnective.iff
infixr:60 " pt_imp " => Arrow.arrow

def psucc : (Fin 1 → Semiterm signature ξ n) → Semiterm signature ξ n := .func Func.succ
def first_ax : Semiformula signature ℕ 0 :=
 .all (Semiformula.nrel Rel.eq ![Semiterm.func Func.succ
  ![#0],Semiterm.func Func.zero ![]])
def second_ax : SyntacticFormula signature :=
  ∀' ∀' ((pt_eq ![pt_succ ![#1],pt_succ ![#0]]) pt_imp (pt_eq ![#1,#0]))
def third_ax : SyntacticFormula signature :=
  ∀' (pt_eq ![pt_add ![#0, pt_zero ![]], #0])
def fourth_ax : SyntacticFormula signature :=
  ∀' ∀' (pt_eq ![pt_add ![#1,pt_succ ![#0]],pt_succ ![pt_add ![#1,#0]]])
def fifth_ax : SyntacticFormula signature :=
  ∀' (pt_eq ![pt_mult ![#0,pt_zero ![]], pt_zero ![]])
def sixth_ax : SyntacticFormula signature :=
  ∀' ∀' (pt_eq ![pt_mult ![#1,pt_succ ![#0]],pt_add ![pt_mult ![#1,#0],#1]])

def zero_term : Semiterm signature ℕ 0 := .func .zero ![]
def succ_var_term : Semiterm signature ℕ 1 := .func .succ ![#0]

def induction_schema (φ : Semiformula signature ℕ 1) : Semiformula signature ℕ 0 :=
  (.and
    (φ/[PAT.zero_term])
    (∀' (φ pt_imp φ/[succ_var_term]))) pt_imp
    ∀' φ
def induction_set (Γ : Semiformula signature ℕ 1 → Prop) : (Semiformula signature ℕ 0) → Prop :=
  fun ψ => ∃ φ : Semiformula signature ℕ 1, Γ φ ∧ ψ = (induction_schema φ)

def axiom_set : Theory signature := {
  first_ax,
  second_ax,
  third_ax,
  fourth_ax,
  fifth_ax,
  sixth_ax
}

example : ∀φ ∈ axiom_set, (not (contains_T φ)) := by
  intro φ
  intro h1
  cases h1 with
  | inl h2 => rw[h2]; rfl
  | inr h1 =>
    cases h1 with
    | inl h1 => rw[h1]; rfl
    | inr h1 =>
      cases h1 with
      | inl h1 => rw[h1]; rfl
      | inr h1 =>
        cases h1 with
        | inl h1 => rw[h1]; rfl
        | inr h1 =>
          cases h1 with
          | inl h1 => rw[h1]; rfl
          | inr h1 =>
            cases h1 with
            | refl => rfl

def lt : Set (Semiformula signature ℕ 0) := Set.univ
def lpa : Set (Semiformula signature ℕ 0) := {φ | ¬ contains_T φ}

def t_pat : Theory signature := axiom_set ∪ (induction_set Set.univ)
def t_pa : Theory signature := t_pat ∩ lpa

namespace TB
def disquotation_schema (φ : Semiformula signature ℕ 0) : Semiformula signature ℕ 0 :=
  .rel .t ![numeral (Semiformula.toNat (φ))] pt_bi_imp φ
def disquotation_set (Γ : Semiformula signature ℕ 0 → Prop) : Theory signature :=
  { ψ | ∃ φ : Semiformula signature ℕ 0, Γ φ ∧ ψ = (disquotation_schema φ)}
def tb : Theory signature := {φ | t_pat φ ∨ (disquotation_set Set.univ) φ}
end TB


example : ∀φ ∈ lpa, TB.tb ⊢! φ → t_pa ⊢! φ := by
  sorry
