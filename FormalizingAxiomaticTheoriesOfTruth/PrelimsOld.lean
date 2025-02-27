import Foundation.Logic.Predicate.Language
import Foundation.Logic.Predicate.Term
import Foundation.FirstOrder.Basic.Syntax.Formula
import Foundation.FirstOrder.Basic.Syntax.Rew
import Foundation.Logic.System
import Foundation.FirstOrder.Basic.Calculus

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
  | f : Rel 0
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
| .f => "ERROR: TRIED TRANSLATING FROM LT FORMULA WITH T"
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
  | .f => Nat.pair 0 0 + 1
  | .eq => Nat.pair 2 0 + 1

def Rel_dec : (n : ℕ) → Option (Rel k)
  | 0 => none
  | e + 1 =>
    match k with
      | 0 =>
        match e.unpair.2 with
          | 0 => some (Rel.f)
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
def second_ax : Semiformula lpa ℕ 0 :=
  ∀' ∀' ((p_eq ![p_succ ![#1],p_succ ![#0]]) p_imp (p_eq ![#1,#0]))
def third_ax : Semiformula lpa ℕ 0 :=
  ∀' (p_eq ![p_add ![#0, p_zero ![]], #0])
def fourth_ax : Semiformula lpa ℕ 0 :=
  ∀' ∀' (p_eq ![p_add ![#1,p_succ ![#0]],p_succ ![p_add ![#1,#0]]])
def fifth_ax : Semiformula lpa ℕ 0 :=
  ∀' (p_eq ![p_mult ![#0,p_zero ![]], p_zero ![]])
def sixth_ax : Semiformula lpa ℕ 0 :=
  ∀' ∀' (p_eq ![p_mult ![#1,p_succ ![#0]],p_add ![p_mult ![#1,#0],#1]])

def zero_term : Semiterm lpa ℕ 0 := .func .zero ![]
def succ_var_term : Semiterm lpa ℕ 1 := .func .succ ![#0]
-- def induction_schema (φ : Semiformula lpa ℕ 1) : SyntacticFormula lpa :=
--   (.and
--     (φ/[zero_term])
--     (∀' (φ p_imp φ/[succ_var_term]))) p_imp
--     ∀' φ
-- def induction_set (Γ : Semiformula lpa ℕ 1 → Prop) : (Semiformula lpa ℕ 0) → Prop :=
--   fun ψ => ∃ φ : Semiformula lpa ℕ 1, Γ φ ∧ ψ = (induction_schema φ)

variable {L: Language}{ξ : Type*}{n : ℕ}

def set1 : Set (Semiformula L ξ n) := Set.univ

lemma ding : DecidablePred (set1) := by
  intro h
  induction h with
  | verum => sorry
  | falsum => sorry
  | rel => sorry
  | nrel => sorry
  | and => sorry -- kan dus niet zonder IH
  | or => sorry -- kan ook niet zonder IH
  | all => sorry
  | ex => sorry


inductive axiom_set : (Semiformula lpa ℕ 0) → Prop
  | first : axiom_set first_ax
  | second : axiom_set second_ax
  | third : axiom_set third_ax
  | fourth : axiom_set fourth_ax
  | fifth : axiom_set fifth_ax
  | sixth : axiom_set sixth_ax
  | ind φ : axiom_set ((.and (φ/[zero_term]) (∀' (φ p_imp φ/[succ_var_term]))) p_imp ∀' φ)

instance : DecidablePred (axiom_set) := by
  intro a
  cases a with
  | verum => sorry
  | falsum => sorry
  | rel => sorry
  | nrel => sorry
  | and => sorry -- kan dus niet zonder IH
  | or => sorry -- kan ook niet zonder IH
  | all => sorry
  | ex => sorry

#check axiom_set first_ax
example : axiom_set first_ax := axiom_set.first
example : axiom_set third_ax := axiom_set.third

def t_pa : Theory lpa := {φ | (axiom_set φ) ∨ (induction_set Set.univ) φ}

/-
# (Sanity check) Proof that ((0 = 0) ∧ ∀x(x = x → S(x) = S(x))) → ∀x(x = x) ∈ PA_plus_induction (below)
-/
def the_formula : Semiformula lpa ℕ 0 := (Semiformula.and ((Semiformula.rel Rel.eq ![zero_term,zero_term]))
          (∀' (Semiformula.rel Rel.eq ![#0,#0] p_imp .rel Rel.eq ![succ_var_term,succ_var_term]))) p_imp
          ∀' (Semiformula.rel Rel.eq ![#0,#0])
#eval the_formula
-- #eval axiom_set the_formula
def φ : Semiformula lpa ℕ 1 := Semiformula.rel Rel.eq ![#0,#0]

example : t_pa the_formula  := by
          rw[t_pa]
          have step1 : φ ∈ Set.univ := by simp
          have step2 : Set.univ φ := by
            apply step1
          have step3 : (induction_set Set.univ) the_formula := by
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
          apply Or.intro_right
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
  | f : Rel 0
  | t : Rel 1
  | eq : Rel 2

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
| .f => "ERROR: TRIED TRANSLATING LT FORMULA WITH T TO LPA"
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

instance enc_f (k : ℕ) : Encodable (lt.Func k) where
  encode := Func_enc
  decode := Func_dec
  encodek := Func_enc_dec

def Rel_enc : Rel k → ℕ
  | .f => Nat.pair 0 0 + 1
  | .t => Nat.pair 1 0 + 1
  | .eq => Nat.pair 2 0 + 1

def Rel_dec : (n : ℕ) → Option (Rel k)
  | 0 => none
  | e + 1 =>
    match k with
      | 0 =>
        match e.unpair.2 with
          | 0 => some .f
          | _ => none
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
  simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]


instance enc_r (k : ℕ) : Encodable (lt.Rel k) where
  encode := Rel_enc
  decode := Rel_dec
  encodek := Rel_enc_dec

/-
A coercion from PA.lpa formulas to L_T.lt formulas as all lpa formulas are
also lt formulas
-/
def to_lt_func {arity : ℕ} : (PA.lpa.Func arity) → (L_T.lt.Func arity)
  | .zero => .zero
  | .succ => .succ
  | .add => .add
  | .mult => .mult

def to_lt_rel {n : ℕ} : (PA.lpa.Rel n) → (L_T.lt.Rel n)
  | .f => .f
  | .eq => .eq

def to_lt_t {n : ℕ}: Semiterm PA.lpa ℕ n → Semiterm L_T.lt ℕ n
  | #x => #x
  | &x => &x
  | .func (arity := n) f v => .func (to_lt_func f) (fun i : Fin n => to_lt_t (v i))

def to_lt_vt {n: ℕ} (v : Fin k → Semiterm PA.lpa ℕ n) : Fin k → Semiterm L_T.lt ℕ n :=
  fun i => to_lt_t (v i)

def to_lt_f {n : ℕ} : Semiformula PA.lpa ℕ n → Semiformula L_T.lt ℕ n
| .verum => .verum
| .falsum => .falsum
| .rel r v => .rel (to_lt_rel r) (to_lt_vt v)
| .nrel r v => .nrel (to_lt_rel r) (to_lt_vt v)
| .and φ ψ => .and (to_lt_f φ) (to_lt_f ψ)
| .or φ ψ => .or (to_lt_f φ) (to_lt_f ψ)
| .all φ => .all (to_lt_f φ)
| .ex φ => .ex (to_lt_f φ)

example {n : ℕ}: ∀φ:Semiformula PA.lpa ℕ n, ∃ψ:Semiformula L_T.lt ℕ n, ψ = to_lt_f φ :=
  fun a : Semiformula PA.lpa ℕ n => Exists.intro (to_lt_f a) (Eq.refl (to_lt_f a))

instance : Coe (Semiterm PA.lpa ℕ n) (Semiterm lt ℕ n) where
  coe t := to_lt_t t
instance : Coe (Semiformula PA.lpa ℕ n) (Semiformula lt ℕ n) where
  coe φ := to_lt_f φ

/-
A partial translation function from lt to lpa
-/
def to_lpa_func {arity : ℕ} : (lt.Func arity) → (PA.lpa.Func arity)
  | .zero => .zero
  | .succ => .succ
  | .add => .add
  | .mult => .mult

def to_lpa_t {n : ℕ}: Semiterm lt ℕ n → Semiterm PA.lpa ℕ n
  | #x => #x
  | &x => &x
  | .func (arity := n) f v => .func (to_lpa_func f) (fun i : Fin n => to_lpa_t (v i))

def to_lpa_vt {k n: ℕ} (v : Fin k → Semiterm lt ℕ n) : Fin k → Semiterm PA.lpa ℕ n :=
  fun i => to_lpa_t (v i)

def to_lpa_f : Semiformula L_T.lt ℕ n → Semiformula PA.lpa ℕ n
| .verum => .verum
| .falsum => .falsum
| .rel .eq v => .rel .eq (to_lpa_vt v)
| .rel .t _ => .rel .f ![]
| .rel .f v => .rel .f (to_lpa_vt v)
| .nrel .eq v => .nrel .eq (to_lpa_vt v)
| .nrel .t _ => .nrel .f ![]
| .nrel .f v => .nrel .f (to_lpa_vt v)
| .and φ ψ => .and (to_lpa_f φ) (to_lpa_f ψ)
| .or φ ψ => .or (to_lpa_f φ) (to_lpa_f ψ)
| .all φ => .all (to_lpa_f φ)
| .ex φ => .ex (to_lpa_f φ)

def t_sentence : Semiformula lt ℕ 0 := .rel .t ![&1]
def non_t_sentence : Semiformula lt ℕ 0 := .rel .eq ![&0,&1]
def t_and_non_t_sentence : Semiformula lt ℕ 0 := .and (t_sentence) (non_t_sentence)
#eval to_lpa_f t_sentence
#eval to_lt_f (to_lpa_f t_sentence)
#eval to_lpa_f non_t_sentence
#eval to_lt_f (to_lpa_f non_t_sentence)
#eval to_lpa_f t_and_non_t_sentence
#eval to_lt_f (to_lpa_f t_and_non_t_sentence)

lemma func_is_func {n : ℕ}: ∀func: PA.Func n, to_lpa_func (to_lt_func func) = func := by
  intro func
  induction func
  rfl
  rfl
  rfl
  rfl

lemma t_is_t : ∀φ:Semiterm PA.lpa ℕ 0, to_lpa_t (to_lt_t φ) = φ := by
  intro h
  induction h
  case bvar x =>
    rfl
  case fvar x =>
    rfl
  case func f v q =>
    induction f with
    | zero =>
      rw[to_lt_t,to_lpa_t,to_lt_func,to_lpa_func]
      simp [q]
    | succ =>
      rw[to_lt_t,to_lpa_t,to_lt_func,to_lpa_func]
      simp[q]
    | add =>
      rw[to_lt_t,to_lpa_t,to_lt_func,to_lpa_func]
      simp[q]
    | mult =>
      rw[to_lt_t,to_lpa_t,to_lt_func,to_lpa_func]
      simp[q]

lemma vt_is_vt {k : ℕ}: ∀vt:Fin k → Semiterm PA.lpa ℕ 0, to_lpa_vt (to_lt_vt vt) = vt := by
  intro vt
  have step1 : (to_lt_vt vt) = (fun i => to_lt_t (vt i)) := by
    rfl
  have step2 (vt : Fin k → Semiterm lt ℕ 0): (to_lpa_vt vt) = (fun i => to_lpa_t (vt i)) := by
    rfl
  simp[step1,step2]
  have step3 : vt = (fun i => vt i) := by
    rfl
  nth_rewrite 2 [step3]
  have step4 (i : Fin k) : to_lpa_t (to_lt_t (vt i)) = vt i := by
    apply t_is_t
  simp[step4]

lemma exists_some_lpa : ∀φ:Semiformula PA.lpa ℕ 0,∃ψ:Semiformula L_T.lt ℕ 0, to_lpa_f ψ = φ := by
  intro φ
  cases φ with
  | verum =>
    let step1 : Semiformula L_T.lt ℕ 0 := Semiformula.verum
    have step2 : to_lpa_f step1 = Semiformula.verum := by
      rfl
    apply Exists.intro step1 step2
  | falsum =>
    let step1 : Semiformula L_T.lt ℕ 0 := Semiformula.falsum
    have step2 : to_lpa_f step1 = Semiformula.falsum := by
      rfl
    apply Exists.intro step1 step2
  | rel r v =>
    cases r with
    | eq =>
      let ψ : Semiformula L_T.lt ℕ 0 := Semiformula.rel .eq (to_lt_vt v)
      have step2 : to_lpa_f ψ = Semiformula.rel PA.Rel.eq v := by
        simp[ψ]
        rw[to_lpa_f]
        simp[vt_is_vt]
      apply Exists.intro ψ step2
    | f =>
      let ψ : Semiformula L_T.lt ℕ 0 := Semiformula.rel .f (to_lt_vt v)
      have step2 : to_lpa_f ψ = Semiformula.rel PA.Rel.f v := by
        simp[ψ]
        rw[to_lpa_f]
        simp[vt_is_vt]
      apply Exists.intro ψ step2
  | nrel r v =>
    cases r with
    | eq =>
      let ψ : Semiformula L_T.lt ℕ 0 := Semiformula.nrel .eq (to_lt_vt v)
      have step2 : to_lpa_f ψ = Semiformula.nrel PA.Rel.eq v := by
        simp[ψ]
        rw[to_lpa_f]
        simp[vt_is_vt]
      apply Exists.intro ψ step2
    | f =>
      let ψ : Semiformula L_T.lt ℕ 0 := Semiformula.nrel .f (to_lt_vt v)
      have step2 : to_lpa_f ψ = Semiformula.nrel PA.Rel.f v := by
        simp[ψ]
        rw[to_lpa_f]
        simp[vt_is_vt]
      apply Exists.intro ψ step2
  | and δ π =>
    let ψ : Semiformula L_T.lt ℕ 0 := Semiformula.and (to_lt_f δ) (to_lt_f π)
    sorry
  | or => sorry
  | all => sorry
  | ex => sorry

end L_T

/-
# Definitions for the PAT theory
-/
namespace PAT
open L_T
infixr:60 " pt_bi_imp " => LogicalConnective.iff
infixr:60 " pt_imp " => Arrow.arrow

-- def psucc : (Fin 1 → Semiterm lt ξ n) → Semiterm lt ξ n := .func Func.succ
-- def first_ax : Semiformula lt ℕ 0 :=
--  ∀' (Semiformula.nrel Rel.eq ![Semiterm.func Func.succ
--   ![#0],Semiterm.func Func.zero ![]])
-- def second_ax : SyntacticFormula lt :=
--   ∀' ∀' ((pt_eq ![pt_succ ![#1],pt_succ ![#0]]) pt_imp (pt_eq ![#1,#0]))
-- def third_ax : SyntacticFormula lt :=
--   ∀' (pt_eq ![pt_add ![#0, pt_zero ![]], #0])
-- def fourth_ax : SyntacticFormula lt :=
--   ∀' ∀' (pt_eq ![pt_add ![#1,pt_succ ![#0]],pt_succ ![pt_add ![#1,#0]]])
-- def fifth_ax : SyntacticFormula lt :=
--   ∀' (pt_eq ![pt_mult ![#0,pt_zero ![]], pt_zero ![]])
-- def sixth_ax : SyntacticFormula lt :=
--   ∀' ∀' (pt_eq ![pt_mult ![#1,pt_succ ![#0]],pt_add ![pt_mult ![#1,#0],#1]])

def zero_term : Semiterm lt ℕ 0 := PA.zero_term
def succ_var_term : Semiterm lt ℕ 1 := PA.succ_var_term

def first_ax : Semiformula lt ℕ 0 := PA.first_ax
def second_ax : Semiformula lt ℕ 0 := PA.second_ax
def third_ax : Semiformula lt ℕ 0 := PA.third_ax
def fourth_ax : Semiformula lt ℕ 0 := PA.fourth_ax
def fifth_ax : Semiformula lt ℕ 0 := PA.fifth_ax
def sixth_ax : Semiformula lt ℕ 0 := PA.sixth_ax

def induction_schema (φ : Semiformula lt ℕ 1) : SyntacticFormula lt :=
  (.and
    (φ/[PAT.zero_term])
    (∀' (φ p_imp φ/[succ_var_term]))) p_imp
    ∀' φ
def induction_set (Γ : Semiformula lt ℕ 1 → Prop) : (Semiformula lt ℕ 0) → Prop :=
  fun ψ => ∃ φ : Semiformula PA.lpa ℕ 1, Γ φ ∧ ψ = (induction_schema φ)

-- def axiom_set : Theory lt := {
--   first_ax,
--   second_ax,
--   third_ax,
--   fourth_ax,
--   fifth_ax,
--   sixth_ax
-- }

inductive axiom_set : (Semiformula lt ℕ 0) → Prop
  | first : axiom_set (to_lt_f PA.first_ax)
  | second : axiom_set PA.second_ax
  | third : axiom_set PA.third_ax
  | fourth : axiom_set PA.fourth_ax
  | fifth : axiom_set PA.fifth_ax
  | sixth : axiom_set PA.sixth_ax

/-
Proof that all PA axioms are in PAT
-/
lemma lem_pa_ax_to_pat_ax (φ : Semiformula PA.lpa ℕ 0) : PA.axiom_set φ → axiom_set φ
  | .first => axiom_set.first
  | .second => axiom_set.second
  | .third => axiom_set.third
  | .fourth => axiom_set.fourth
  | .fifth => axiom_set.fifth
  | .sixth => axiom_set.sixth

lemma all_pa_ax_pat_ax : ∀φ:Semiformula PA.lpa ℕ 0, (PA.axiom_set φ) → (axiom_set φ) :=
  fun φ : Semiformula PA.lpa ℕ 0 =>
    lem_pa_ax_to_pat_ax φ

def t_pat : Theory lt := {φ | axiom_set φ ∨ (induction_set Set.univ) φ}
end PAT

/-
# The namespace sandbox is an environment for experimentation
-/
namespace Sandbox
open PA
def psucc : (Fin 1 → Semiterm lpa ξ n) → Semiterm lpa ξ n := .func .succ
def first_PA_ax : Semiformula lpa ℕ 0 :=
 ∀' (Semiformula.nrel .eq ![Semiterm.func .succ
  ![#0],Semiterm.func .zero ![]])
def first_PA_ax_b_free : Semiformula lpa ℕ 1 :=
  (Semiformula.nrel .eq ![Semiterm.func .succ
  ![#0],Semiterm.func .zero ![]])

def instance_first_PA_ax : Semiformula lpa ℕ 0 :=
  Semiformula.nrel .eq ![(numeral 3),null]

def PA : Theory lpa := {first_PA_ax}

open Theory

def instance_first_PA : Semiformula lpa ℕ 1 :=
  Semiformula.rel .eq ![#0,#0]


open Semiterm
/-
# Goal: have that ¬=(S(S(S(0))),0) is provable from PA axiom 1.
-/
/-
## The intuitive one using tactics
-/
def provable_instance : PA ⊢ instance_first_PA_ax := by
  have step1 : first_PA_ax ∈ PA := by
    rw [PA]
    simp
  have step2 : PA ⟹ [first_PA_ax] := by
    apply Derivation.root at step1
    exact step1
  have step3 : PA ⟹. instance_first_PA_ax := by
    apply Derivation.specialize (numeral 2) at step2
    rw[instance_first_PA_ax]
    simp at step2
    rw[numeral,null]
    exact step2
  apply Derivation.provableOfDerivable
  exact step3

lemma instance_first_PA_ax_from_PA : PA ⊢! instance_first_PA_ax :=
  Nonempty.intro provable_instance

  /-
What print gives from the above (but that relies on that proof
itself)
-/
#print provable_instance

def provable_instance_2 : PA ⊢ instance_first_PA_ax :=
let_fun step1 := provable_instance.proof_2;
let_fun step2 := Derivation.root step1;
let_fun step3 :=
  provable_instance.proof_3.mpr
    (provable_instance.proof_4.mpr
      (provable_instance.proof_5.mpr (provable_instance.proof_6.mp (Derivation.specialize (numeral 2) step2))));
Derivation.provableOfDerivable step3

/-
What you get when printing and copying all instances of provable_instance.proof_#
and rewriting the let_funs to their inductive meaning
-/
def provable_instance_3 : PA ⊢ instance_first_PA_ax :=
  (fun step1 : first_PA_ax ∈ PA =>
    (fun step2 : PA ⟹ [first_PA_ax] =>
      (fun step3 : (PA ⟹. instance_first_PA_ax) = (PA ⟹. .nrel .eq ![numeral 3, null]) =>
        (fun step4 : (PA ⟹. .nrel .eq ![numeral 3, null]) = (PA ⟹. .nrel .eq ![.func .succ ![numeral 2], null]) =>
          (fun step5 : (PA ⟹. .nrel .eq ![.func .succ ![numeral 2], null]) = (PA ⟹..nrel Rel.eq ![.func .succ ![numeral 2], .func .zero ![]]) =>
            (fun step6 : (PA ⟹ [(Rewriting.app (Rew.substs ![numeral 2])) (Semiformula.nrel Rel.eq ![Semiterm.func Func.succ ![#0], Semiterm.func Func.zero ![]])]) = (PA ⟹ [Semiformula.nrel Rel.eq ![Semiterm.func Func.succ ![numeral 2], Semiterm.func Func.zero ![]]]) =>
              (fun step7 : PA ⊢ instance_first_PA_ax =>
                Derivation.provableOfDerivable step7)
            (step3.mpr (step4.mpr (step5.mpr (step6.mp (Derivation.specialize (numeral 2) step2))))))
          (congrArg (fun x ↦ PA ⟹ [x]) (Eq.trans (Semiformula.rew_nrel2 (Rew.substs ![numeral 2])) (congrArg (Semiformula.nrel Rel.eq) (congr (congrArg Matrix.vecCons (Eq.trans (Rew.func1 (Rew.substs ![numeral 2]) Func.succ #0) (congrArg (fun x ↦ Semiterm.func Func.succ ![x]) (Eq.trans (Rew.substs_bvar ![numeral 2] 0) (Matrix.cons_val_fin_one (numeral 2) ![] 0))))) (congrArg (fun x ↦ ![x]) (Rew.func0 (Rew.substs ![numeral 2]) Func.zero ![])))))))
        (id (congrArg (fun _a ↦ PA ⟹. Semiformula.nrel Rel.eq ![Semiterm.func Func.succ ![numeral 2], _a]) null.eq_1)))
      (congrArg (fun _a ↦ PA ⟹. .nrel .eq ![_a, null]) (numeral.eq_2 2)))
    (congrArg (fun _a ↦ PA ⟹. _a) instance_first_PA_ax.eq_1))
   (Derivation.root step1))
  (Eq.mpr ((congrArg (fun _a ↦ first_PA_ax ∈ _a) PA.eq_1)) (Set.mem_singleton_iff.mpr (Eq.refl first_PA_ax)))

/-
A self-constructed inductive proof (provable_instance_without_tactics) without tactics that relies on a rather
complicated rewriting and simplying bit (rw_and_simp_(with/without)_tactics), but further is rather concise.
More notes:
* PA.eq_1 produces the proposition that PA is equal to
what it is defined as being equal to, i.e. {first_PA_axiom}.
* Rewriting parts of the equation can be done with congrArg (see above).
-/
theorem rw_and_simp_with_tactics : (PA ⟹ [instance_first_PA_ax]) = (PA ⟹ [(Semiformula.nrel Rel.eq ![func Func.succ ![#0], func Func.zero ![]])/[numeral 2]]) := by
  simp
  rw[instance_first_PA_ax,numeral,null]

theorem rw_and_simp_without_tactics : (PA ⟹ [instance_first_PA_ax]) = (PA ⟹ [(Semiformula.nrel Rel.eq ![func Func.succ ![#0], func Func.zero ![]])/[numeral 2]]) :=
  Eq.mpr
  (id
    (congrArg (fun x ↦ (PA ⟹ [instance_first_PA_ax]) = (PA ⟹ [x]))
      (Eq.trans (Semiformula.rew_nrel2 (Rew.substs ![numeral 2]))
        (congrArg (Semiformula.nrel Rel.eq)
          (congr
            (congrArg Matrix.vecCons
              (Eq.trans (Rew.func1 (Rew.substs ![numeral 2]) Func.succ #0)
                (congrArg (fun x ↦ func Func.succ ![x])
                  (Eq.trans (Rew.substs_bvar ![numeral 2] 0) (Matrix.cons_val_fin_one (numeral 2) ![] 0)))))
            (congrArg (fun x ↦ ![x]) (Rew.func0 (Rew.substs ![numeral 2]) Func.zero ![])))))))
  (Eq.refl (PA ⟹ [instance_first_PA_ax]))

def provable_instance_without_tactics : PA ⊢ instance_first_PA_ax :=
(fun h1 : PA ⟹ [instance_first_PA_ax] => Derivation.provableOfDerivable h1)
  ((fun h2 : PA ⟹ [(Semiformula.nrel Rel.eq ![func Func.succ ![#0], func Func.zero ![]])/[numeral 2]] =>
    rw_and_simp_without_tactics.mpr h2)
    ((fun h3 : PA ⟹ [first_PA_ax] => Derivation.specialize (numeral 2) h3)
      ((fun h4 : first_PA_ax ∈ PA => Derivation.root h4)
        ((fun h5 : first_PA_ax ∈ {first_PA_ax} => (congrArg (fun _a => first_PA_ax ∈ _a) (PA.eq_1)).mpr h5)
            (Set.mem_singleton_iff.mpr (Eq.refl first_PA_ax))))))

/-
* So, this goes well, but thm23 is just very complicated, i.e. #print thm23 yields
-/
end Sandbox
