import Foundation.Logic.Predicate.Language
import Foundation.FirstOrder.Arith.Theory
import Foundation.FirstOrder.Arith.PeanoMinus

open LO
open FirstOrder

/-
# Definitions for the language of PA
-/
namespace PA
inductive Func : ℕ → Type where
  | zero : Func 0
  | succ : Func 1
  | add : Func 2
  | mult : Func 2

inductive Rel : ℕ → Type where
  | eq : Rel 2

def lpa : Language where
  Func := Func
  Rel := Rel

/-
# Useful notation
-/
prefix:60 "p_succ" => Semiterm.func Func.succ
prefix:60 "p_eq" => Semiformula.rel Rel.eq
prefix:60 "p_zero" => Semiterm.func Func.zero
prefix:60 "p_add" => Semiterm.func Func.add
prefix:60 "p_mult" => Semiterm.func Func.mult

/-
# Some useful terms
-/
def null : SyntacticTerm lpa :=
  p_zero ![]
def numeral : ℕ → SyntacticTerm lpa
  | .zero => p_zero ![]
  | .succ n => p_succ ![numeral n]

-- Printing terms
def funToStr {n}: Func n → String
  | .zero => "0"
  | .succ => "S"
  | .add => "+"
  | .mult => "\\times"
instance : ToString (Func n) := ⟨funToStr⟩

-- Printing formulas
def relToStr {n} : Rel n → String
| .eq => "="
instance : ToString (Rel n) := ⟨relToStr⟩

-- pairwise encoding functions for LPA.Func, LPA.Rel, LTr.Func
-- and LTr.Rel
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

instance enc_f (k : ℕ) : Encodable (lpa.Func k) where
  encode := Func_enc
  decode := Func_dec
  encodek := Func_enc_dec

def Rel_enc : Rel k → ℕ
  | .eq => Nat.pair 2 0 + 1

def Rel_dec : (n : ℕ) → Option (Rel k)
  | 0 => none
  | e + 1 =>
    match k with
      | 2 =>
        match e.unpair.2 with
          | 0 => some (Rel.eq)
          | _ => none
      | _ => none

lemma Rel_enc_dec {k : ℕ}: ∀ f : Rel k, Rel_dec (Rel_enc f) = (some f) := by
  intro h
  induction h
  simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

instance enc_r (k : ℕ) : Encodable (lpa.Rel k) where
  encode := Rel_enc
  decode := Rel_dec
  encodek := Rel_enc_dec

/-
# Theory of PA and useful notation
-/
infixr:60 " p_imp " => Arrow.arrow

def psucc : (Fin 1 → Semiterm lpa ξ n) → Semiterm lpa ξ n := .func Func.succ
def first_ax : Semiformula lpa ℕ 0 :=
 ∀' (Semiformula.nrel Rel.eq ![Semiterm.func Func.succ
  ![#0],Semiterm.func Func.zero ![]])
def second_ax : SyntacticFormula lpa :=
  ∀' ∀' ((p_eq ![p_succ ![#1],p_succ ![#0]]) p_imp (p_eq ![#1,#0]))
def third_ax : SyntacticFormula lpa :=
  ∀' (p_eq ![p_add ![#0, p_zero ![]], #0])
def fourth_ax : SyntacticFormula lpa :=
  ∀' ∀' (p_eq ![p_add ![#1,p_succ ![#0]],p_succ ![p_add ![#1,#0]]])
def fifth_ax : SyntacticFormula lpa :=
  ∀' (p_eq ![p_mult ![#0,p_zero ![]], p_zero ![]])
def sixth_ax : SyntacticFormula lpa :=
  ∀' ∀' (p_eq ![p_mult ![#1,p_succ ![#0]],p_add ![p_mult ![#1,#0],#1]])

def zero_term : Semiterm lpa ℕ 0 := .func .zero ![]
def succ_var_term : Semiterm lpa ℕ 1 := .func .succ ![#0]
def induction_schema (φ : Semiformula lpa ℕ 1) : SyntacticFormula lpa :=
  (.and
    (φ/[zero_term])
    (∀' (φ p_imp φ/[succ_var_term]))) p_imp
    ∀' φ
def induction_set (Γ : Semiformula lpa ℕ 1 → Prop) : Theory lpa :=
  { ψ | ∃ φ : Semiformula lpa ℕ 1, Γ φ ∧ ψ = (induction_schema φ)}

def axiom_set : Theory lpa := {first_ax,
                        second_ax,
                        third_ax,
                        fourth_ax,
                        fifth_ax,
                        sixth_ax}
def t_pa : Theory lpa := axiom_set + induction_set Set.univ
/-
# (Sanity check) Proof that ((0 = 0) ∧ ∀x(x = x → S(x) = S(x))) → ∀x(x = x) ∈ PA_plus_induction (below)
-/
def the_formula : Semiformula lpa ℕ 0 := (Semiformula.and ((Semiformula.rel Rel.eq ![zero_term,zero_term]))
          (∀' (Semiformula.rel Rel.eq ![#0,#0] p_imp .rel Rel.eq ![succ_var_term,succ_var_term]))) p_imp
          ∀' (Semiformula.rel Rel.eq ![#0,#0])
#eval the_formula
def φ : Semiformula lpa ℕ 1 := Semiformula.rel Rel.eq ![#0,#0]

example : the_formula ∈ t_pa := by
          rw[t_pa]
          have step1 : φ ∈ Set.univ := by simp
          have step2 : Set.univ φ := by
            apply step1
          have step3 : the_formula ∈ (induction_set Set.univ) := by
            rw[induction_set]
            have h : Set.univ φ ∧ the_formula = induction_schema φ := by
              apply And.intro
              apply step2
              rw[the_formula]
              simp[induction_schema]
              apply And.intro
              apply And.intro
              rw[φ]
              simp
              apply And.intro
              rfl
              rw[φ]
              simp
              rfl
            apply Exists.intro φ h
          apply Set.mem_union_right
          apply step3

end PA
/-
# Definitions for the language L_T
-/
namespace L_T
inductive Func : ℕ → Type where
  | zero : Func 0
  | succ : Func 1
  | add : Func 2
  | mult : Func 2

inductive Rel : ℕ → Type where
  | eq : Rel 2
  | t : Rel 1

def lt : Language where
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
def null : SyntacticTerm lt :=
  pt_zero ![]
def numeral : ℕ → SyntacticTerm lt
  | .zero => pt_zero ![]
  | .succ n => pt_succ ![numeral n]

def funToStr {n}: Func n → String
  | .zero => "0"
  | .succ => "S"
  | .add => "+"
  | .mult => "\\times"
instance : ToString (Func n) := ⟨funToStr⟩

def relToStr {n} : Rel n → String
| .eq => "="
| .t => "T"

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

instance enc_f (k : ℕ) : Encodable (lt.Func k) where
  encode := Func_enc
  decode := Func_dec
  encodek := Func_enc_dec

def Rel_enc : Rel k → ℕ
  | .eq => Nat.pair 2 0 + 1
  | .t => Nat.pair 1 0 + 1

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

instance enc_r (k : ℕ) : Encodable (lt.Rel k) where
  encode := Rel_enc
  decode := Rel_dec
  encodek := Rel_enc_dec
end L_T
/-
# Definitions for the PAT theory
-/
namespace PAT
open L_T
infixr:60 " pt_bi_imp " => LogicalConnective.iff
infixr:60 " pt_imp " => Arrow.arrow

def psucc : (Fin 1 → Semiterm lt ξ n) → Semiterm lt ξ n := .func Func.succ
def first_ax : Semiformula lt ℕ 0 :=
 ∀' (Semiformula.nrel Rel.eq ![Semiterm.func Func.succ
  ![#0],Semiterm.func Func.zero ![]])
def second_ax : SyntacticFormula lt :=
  ∀' ∀' ((pt_eq ![pt_succ ![#1],pt_succ ![#0]]) pt_imp (pt_eq ![#1,#0]))
def third_ax : SyntacticFormula lt :=
  ∀' (pt_eq ![pt_add ![#0, pt_zero ![]], #0])
def fourth_ax : SyntacticFormula lt :=
  ∀' ∀' (pt_eq ![pt_add ![#1,pt_succ ![#0]],pt_succ ![pt_add ![#1,#0]]])
def fifth_ax : SyntacticFormula lt :=
  ∀' (pt_eq ![pt_mult ![#0,pt_zero ![]], pt_zero ![]])
def sixth_ax : SyntacticFormula lt :=
  ∀' ∀' (pt_eq ![pt_mult ![#1,pt_succ ![#0]],pt_add ![pt_mult ![#1,#0],#1]])

def zero_term : Semiterm lt ℕ 0 := .func .zero ![]
def succ_var_term : Semiterm lt ℕ 1 := .func .succ ![#0]
def induction_schema (φ : Semiformula lt ℕ 1) : SyntacticFormula lt :=
  (.and
    (φ/[zero_term])
    (∀' (φ p_imp φ/[succ_var_term]))) p_imp
    ∀' φ
def induction_set (Γ : Semiformula lt ℕ 1 → Prop) : Theory lt :=
  { ψ | ∃ φ : Semiformula lt ℕ 1, Γ φ ∧ ψ = (induction_schema φ)}

def axiom_set : Theory lt := {
  first_ax,
  second_ax,
  third_ax,
  fourth_ax,
  fifth_ax,
  sixth_ax
}
def t_pat : Theory lt := axiom_set + induction_set Set.univ
end PAT
