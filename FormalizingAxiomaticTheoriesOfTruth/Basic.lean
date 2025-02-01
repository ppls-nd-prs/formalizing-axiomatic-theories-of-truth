import Foundation.Logic.Predicate.Language
import Foundation.FirstOrder.Arith.Theory
import Foundation.FirstOrder.Arith.PeanoMinus

open LO
open FirstOrder

-- Definition of the language of arithmetic
inductive LPA_Func : ℕ → Type where
  | zero : LPA_Func 0
  | succ : LPA_Func 1
  | add : LPA_Func 2
  | mult : LPA_Func 2

inductive LPA_Rel : ℕ → Type where
  | eq : LPA_Rel 2

def LPA : Language where
  Func := LPA_Func
  Rel := LPA_Rel

-- Definition of the language of arithmetic including the truth
-- predicate
def LTr_Func := LPA_Func

inductive LTr_Rel : ℕ → Type where
  | eq : LTr_Rel 2
  | tr : LTr_Rel 1

def LTr : Language where
  Func := LTr_Func
  Rel := LTr_Rel

-- Printing terms
def LPA_funToStr {n}: LPA_Func n → String
  | .zero => "0"
  | .succ => "S"
  | .add => "+"
  | .mult => "\\times"
def LTr_funToStr {n} : LPA_Func n → String := LPA_funToStr
instance : ToString (LPA_Func n) := ⟨LPA_funToStr⟩

-- Printing formulas
def LPA_relToStr {n} : LPA_Rel n → String
| .eq => "="
def LTr_relToStr {n} : LTr_Rel n → String
| .eq => "="
| .tr => "Tr"
instance : ToString (LPA_Rel n) := ⟨LPA_relToStr⟩
instance : ToString (LTr_Rel n) := ⟨LTr_relToStr⟩

-- pairwise encoding functions for LPA.Func, LPA.Rel, LTr.Func
-- and LTr.Rel
def LPA_Func_enc : LPA_Func k → ℕ
  | .zero => Nat.pair 0 0 + 1
  | .succ => Nat.pair 1 0 + 1
  | .add => Nat.pair 2 0 + 1
  | .mult => Nat.pair 2 1 + 1
def LTr_Func_enc : LTr_Func k → ℕ := LPA_Func_enc

def LPA_Func_dec : (n : ℕ) → Option (LPA_Func k)
  | 0 => none
  | e + 1 =>
    match k with
      | 0 =>
        match e.unpair.2 with
          | 0 => some (LPA_Func.zero)
          | _ => none
      | 1 =>
        match e.unpair.2 with
          | 0 => some (LPA_Func.succ)
          | _ => none
      | 2 =>
        match e.unpair.2 with
          | 0 => some (LPA_Func.add)
          | 1 => some (LPA_Func.mult)
          | _ => none
      | _ => none
def LTr_Func_dec : (n : ℕ) → Option (LTr_Func k) := LPA_Func_dec

lemma LPA_Func_enc_dec {k : ℕ}: ∀ f : LPA_Func k, LPA_Func_dec (LPA_Func_enc f) = (some f) := by
  intro h
  induction h
  simp [LPA_Func_enc,Nat.pair,LPA_Func_dec]
  simp [LPA_Func_enc,Nat.pair,LPA_Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
  simp [LPA_Func_enc,Nat.pair,LPA_Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
  simp [LPA_Func_enc,Nat.pair,LPA_Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
lemma LTr_Func_enc_dec {k : ℕ}: ∀ f : LTr_Func k, LTr_Func_dec (LTr_Func_enc f) = (some f) :=
  LPA_Func_enc_dec

instance enc_pa_f (k : ℕ) : Encodable (LPA.Func k) where
  encode := LPA_Func_enc
  decode := LPA_Func_dec
  encodek := LPA_Func_enc_dec
instance enc_ltr_f (k : ℕ) : Encodable (LTr.Func k) :=
  enc_pa_f k

def LPA_Rel_enc : LPA_Rel k → ℕ
  | .eq => Nat.pair 2 0 + 1

def LTr_Rel_enc : LTr_Rel k → ℕ
  | .eq => Nat.pair 2 0 + 1
  | .tr => Nat.pair 1 0 + 1

def LPA_Rel_dec : (n : ℕ) → Option (LPA_Rel k)
  | 0 => none
  | e + 1 =>
    match k with
      | 2 =>
        match e.unpair.2 with
          | 0 => some (LPA_Rel.eq)
          | _ => none
      | _ => none

def LTr_Rel_dec : (n : ℕ) → Option (LTr_Rel k)
  | 0 => none
  | e + 1 =>
    match k with
      | 1 =>
        match e.unpair.2 with
          | 0 => some (LTr_Rel.tr)
          | _ => none
      | 2 =>
        match e.unpair.2 with
          | 0 => some (LTr_Rel.eq)
          | _ => none
      | _ => none

lemma LPA_Rel_enc_dec {k : ℕ}: ∀ f : LPA_Rel k, LPA_Rel_dec (LPA_Rel_enc f) = (some f) := by
  intro h
  induction h
  simp [LPA_Rel_enc,Nat.pair,LPA_Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

lemma LTr_Rel_enc_dec {k : ℕ}: ∀ f : LTr_Rel k, LTr_Rel_dec (LTr_Rel_enc f) = (some f) := by
  intro h
  induction h
  simp [LTr_Rel_enc,Nat.pair,LTr_Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
  simp [LTr_Rel_enc,Nat.pair,LTr_Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

instance enc_lpa_r (k : ℕ) : Encodable (LPA.Rel k) where
  encode := LPA_Rel_enc
  decode := LPA_Rel_dec
  encodek := LPA_Rel_enc_dec

instance enc_ltr_r (k : ℕ) : Encodable (LTr.Rel k) where
  encode := LTr_Rel_enc
  decode := LTr_Rel_dec
  encodek := LTr_Rel_enc_dec

-- pairwise encoding functions for LTr.Func and LTr.Rel

/-
# Theory of PA and useful notation
-/
infixr:60 " imp " => Arrow.arrow
prefix:60 "p_succ" => Semiterm.func LPA_Func.succ
prefix:60 "p_eq" => Semiformula.rel LPA_Rel.eq
prefix:60 "p_zero" => Semiterm.func LPA_Func.zero
prefix:60 "p_add" => Semiterm.func LPA_Func.add
prefix:60 "p_mult" => Semiterm.func LPA_Func.mult

namespace TPA
def psucc : (Fin 1 → Semiterm LPA ξ n) → Semiterm LPA ξ n := .func LPA_Func.succ
def first_PA_ax : Semiformula LPA ℕ 0 :=
 ∀' (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ
  ![#0],Semiterm.func LPA_Func.zero ![]])
def first_PA_ax_b_free : Semiformula LPA ℕ 1 :=
  (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ
  ![#0],Semiterm.func LPA_Func.zero ![]])
def second_PA_ax : SyntacticFormula LPA :=
  ∀' ∀' ((p_eq ![p_succ ![#1],p_succ ![#0]]) imp (p_eq ![#1,#0]))
def third_PA_ax : SyntacticFormula LPA :=
  ∀' (p_eq ![p_add ![#0, p_zero ![]], #0])
def fourth_PA_ax : SyntacticFormula LPA :=
  ∀' ∀' (p_eq ![p_add ![#1,p_succ ![#0]],p_succ ![p_add ![#1,#0]]])
def fifth_PA_ax : SyntacticFormula LPA :=
  ∀' (p_eq ![p_mult ![#0,p_zero ![]], p_zero ![]])
def sixth_PA_ax : SyntacticFormula LPA :=
  ∀' ∀' (p_eq ![p_mult ![#1,p_succ ![#0]],p_add ![p_mult ![#1,#0],#1]])

def zero_term : Semiterm LPA ℕ 0 := .func .zero ![]
def succ_var_term : Semiterm LPA ℕ 1 := .func .succ ![#0]
def induction_scheme (φ : Semiformula LPA ℕ 1) : SyntacticFormula LPA :=
  (.and (φ/[zero_term])
   (∀' (φ imp φ/[succ_var_term]))) imp ∀' φ
def induction_set (Γ : Semiformula LPA ℕ 1 → Prop) : Theory LPA :=
  { ψ | ∃ φ : Semiformula LPA ℕ 1, Γ φ ∧ ψ = (induction_scheme φ)}

def PA : Theory LPA := {first_PA_ax,
                        second_PA_ax,
                        third_PA_ax,
                        fourth_PA_ax,
                        fifth_PA_ax,
                        sixth_PA_ax}
def PA_plus_induction : Theory LPA := PA + induction_set Set.univ
def the_formula : Semiformula LPA ℕ 0 := (Semiformula.and ((Semiformula.rel LPA_Rel.eq ![zero_term,zero_term]))
          (∀' (Semiformula.rel LPA_Rel.eq ![#0,#0] imp .rel LPA_Rel.eq ![succ_var_term,succ_var_term]))) imp
          ∀' (Semiformula.rel LPA_Rel.eq ![#0,#0])
#eval the_formula
def φ : Semiformula LPA ℕ 1 := Semiformula.rel LPA_Rel.eq ![#0,#0]

/-
# (Sanity check) Proof that ((0 = 0) ∧ ∀x(x = x → S(x) = S(x))) → ∀x(x = x) ∈ PA_plus_induction (below)
-/
example : the_formula ∈ PA_plus_induction := by
          rw[PA_plus_induction]
          have step1 : φ ∈ Set.univ := by simp
          have step2 : Set.univ φ := by
            apply step1
          have step3 : the_formula ∈ (induction_set Set.univ) := by
            rw[induction_set]
            have h : Set.univ φ ∧ the_formula = induction_scheme φ := by
              apply And.intro
              apply step2
              rw[the_formula]
              simp[induction_scheme]
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
