import Foundation.Logic.Predicate.Language
import FormalizingAxiomaticTheoriesOfTruth.Basic



open LO
open FirstOrder

-- Constructing and printing some terms
-- Definition of useful LPA terms
-- the terms properties L, ξ and n should correspond to the
-- properties of the formula they will be a part of
def LPA_null : SyntacticTerm LPA := Semiterm.func LPA_Func.zero ![]

def LPA_numeral : ℕ → SyntacticTerm LPA
  | .zero => Semiterm.func LPA_Func.zero ![]
  | .succ n => Semiterm.func LPA_Func.succ ![LPA_numeral n]

def LTr_null : SyntacticTerm LTr := Semiterm.func LPA_Func.zero ![]
def LTr_numeral : ℕ → SyntacticTerm LTr
  | .zero => Semiterm.func LPA_Func.zero ![]
  | .succ n => Semiterm.func LPA_Func.succ ![LTr_numeral n]

def LTr_t1 : SyntacticTerm LTr := Semiterm.func LPA_Func.mult ![LTr_numeral 2, LTr_numeral 3]
#eval LTr_t1
#eval LPA_numeral 3

-- Some formulas
def PA_eq_null : SyntacticFormula LPA := Semiformula.rel LPA_Rel.eq ![LPA_null, LPA_null]
def PA_bound_variable : Semiterm LPA ℕ 1 := Semiterm.bvar 1
def PA_eq_exists : SyntacticFormula LPA := Semiformula.ex (Semiformula.rel LPA_Rel.eq ![PA_bound_variable,PA_bound_variable])
-- def PA_eq_null_sent : Sentence LPA := Semiformula.rel LPA_Rel.eq ![LPA_null, LPA_null]
def PA_eq_num_2_num_4 : SyntacticFormula LPA := Semiformula.rel LPA_Rel.eq ![LPA_numeral 2,LPA_numeral 4] --!
def PA_f3 : SyntacticFormula LPA := Semiformula.and PA_eq_num_2_num_4 PA_eq_num_2_num_4
def PA_f4 : SyntacticFormula LPA := Semiformula.or PA_eq_num_2_num_4 PA_eq_num_2_num_4
def PA_f1 : SyntacticFormula LPA := Semiformula.verum
def LTr_f1 : SyntacticFormula LTr := Semiformula.rel LTr_Rel.tr ![LTr_numeral 2]
#eval PA_eq_null
#eval PA_eq_num_2_num_4
#eval PA_f3
#eval PA_f4
#eval LTr_f1
#eval PA_f1

-- SCRATCH WORK FROM HERE ON OUT
def one : SyntacticTerm LPA := Semiterm.func LPA_Func.succ (fun _ : Fin 1 => LPA_null)
def two : SyntacticTerm LPA := Semiterm.func LPA_Func.succ (fun _ : Fin 1 => one)
#eval LPA_Rel.eq
#eval (fun h : Fin 3 => if h = 0 then 2 else 4) -- ![2,4,4] then the index resulting from a modulo on the argument ∈ ℕ is returned
#eval (fun h : Fin 3 => if h = 0 then 2 else 4) 20 -- 4, as 20 % 3 = 2 and 4 is at index 2 (0-based indexing)
def PA_fvt0 : Semiterm LPA ℕ 1 := Semiterm.fvar 0
def PA_semf1 : Semiformula LPA ℕ 1 := Semiformula.rel LPA_Rel.eq (fun _ : Fin 2 => PA_fvt0)
def PA_f5 : SyntacticFormula LPA := Semiformula.all PA_semf1

-- variable {L : Language} {T : Theory L}
def singleton_theory : Theory LPA := {PA_f4}
def PA_theory : Theory LPA := {}
theorem mem : PA_f4 ∈ singleton_theory := by
  rw [singleton_theory] -- PA_f4 ∈ {PA_f4}
  simp -- no goals
def double_theory : Theory LPA := {PA_f3,PA_f4}
theorem mem2 : PA_f3 ∈ double_theory := by
  rw [double_theory]
  simp
theorem mem3 : PA_f4 ∈ double_theory := by
  rw [double_theory]
  simp -- no goals

-- variable (L : Language)
def der1 : Derivation T (⊤ :: [PA_f4]) := Derivation.verum [PA_f4]
def der2 : Derivation T (⊤ :: [PA_f4,PA_f3]) := Derivation.verum [PA_f4,PA_f3]
--def der3 : Derivation T (PA_f4 ⋏ PA_f3 :: [PA_f4,PA_f3]) := Derivation.and
-- def der4 : Derivation T (Semiformula.rel LPA_Rel.eq ![LPA_null,LPA_null] :: [Semiformula.rel LPA_Rel.eq ![LPA_null,LPA_null]]) := Derivation.axL [] LPA_Rel.eq ![LPA_null,LPA_null]
--def der8 : Derivation T (LPA_f4 ⋏ LPA_f3 :: [LPA_f4,LPA_f3]) := Derivation.and Derivation.axL (LPA_f4 :: [LPA_f4,LPA_f3])
def der5 : Derivation singleton_theory [PA_f4] := Derivation.root (mem)
def der6 : Derivation double_theory [PA_f3] := Derivation.root (mem2)
def der7 : Derivation double_theory [PA_f4] := Derivation.root (mem3)
def der8 : Derivation double_theory [PA_f3 ⋏ PA_f4 ] :=
  Derivation.and der6 der7
def der9 : Derivation double_theory [PA_f3 ⋏ PA_f3 ⋏ PA_f4] :=
  Derivation.and der6 der8
lemma sub1 : [PA_f3] ⊆ [PA_f3,PA_f4] := by
  simp
def der10 : Derivation double_theory [PA_f3,PA_f4] :=
  Derivation.wk der6 sub1
def der11 : Derivation double_theory [PA_f3 ⋎ PA_f4] :=
  Derivation.or der10
def theory3 : Theory LPA := {PA_eq_null}
def one_sided_der1 : singleton_theory ⟹ [PA_f4] := by
  apply der5
def one_sided_der2 : OneSided.Derivation₁ singleton_theory PA_f4 :=
  one_sided_der1
def provable1 : singleton_theory ⊢ PA_f4 :=
  Derivation.provableOfDerivable one_sided_der2
def provable2 : double_theory ⊢ PA_f3 ⋏ PA_f4 :=
  Derivation.provableOfDerivable der8

-- provable3 and provable4 prove the same
def provable3 : double_theory ⊢ PA_f3 ⋏ PA_f4 := by
  have h1 : PA_f3 ∈ double_theory := by
    rw [double_theory]
    simp
  have h2 : PA_f4 ∈ double_theory := by
    rw [double_theory]
    simp
  have der_3 : Derivation double_theory [PA_f3] :=
    Derivation.root (h1)
  have der_4 : Derivation double_theory [PA_f4] :=
    Derivation.root (h2)
  have der_and : Derivation double_theory [PA_f3 ⋏ PA_f4] :=
    Derivation.and der_3 der_4
  apply Derivation.provableOfDerivable at der_and
  exact der_and

def provable4 : double_theory ⊢ PA_f3 ⋏ PA_f4 := by
  have h1 : PA_f3 ∈ double_theory := by
    rw [double_theory]
    simp
  have h2 : PA_f4 ∈ double_theory := by
    rw [double_theory]
    simp
  apply Derivation.root at h1
  apply Derivation.root at h2
  apply Derivation.and h1 h2

def theory2 : Theory LPA := {PA_eq_null}
def provable5 : theory2 ⊢ PA_eq_null ⋎ PA_eq_null := by
  have der1 : PA_eq_null ∈ theory2 := by
    rw [theory2]
    simp
  apply Derivation.root at der1
  have der2 : Derivation theory2 [PA_eq_null,PA_eq_null] := by
    have sub1 : [PA_eq_null] ⊆ [PA_eq_null,PA_eq_null] := by
      simp
    apply Derivation.wk der1 sub1
  apply Derivation.or der2

-- def provabl6 : theory2 ⊢ PA_eq_exists := by
--   have der1 : PA_eq_null ∈ theory2 := by
--     rw [theory2]
--     simp
--   apply Derivation.root at der1
--   have der2 : Derivation theory2 [(Semiformula.rel LPA_Rel.eq ![PA_bound_variable, PA_bound_variable])/[Rew.emb LPA_null]] := by
--     simp
--     exact der1
--   apply Derivation.ex LPA_null der2

def free : SyntacticTerm LPA := Semiterm.fvar 1
def freef : SyntacticFormula LPA := Semiformula.rel LPA_Rel.eq ![free,free]
def theory_free : Theory LPA := {freef}
def mem4 : freef ∈ theory_free := by
  rw [theory_free]
  simp
def bound : Semiterm LPA ℕ 1 := Semiterm.bvar 1
def boundf : SyntacticFormula LPA := ∀' Semiformula.rel LPA_Rel.eq ![bound,bound]
def rewrite_function : ℕ → Semiterm LPA ℕ 0 := fun n : ℕ => Semiterm.fvar n
#check LO.FirstOrder.Rew.rewrite rewrite_function
def freet1 : Semiterm LPA ℕ 1 :=
  Semiterm.bvar 1
def free1 : Semiformula LPA ℕ 1 :=
  Semiformula.rel LPA_Rel.eq ![freet1,freet1]
def der30 : Derivation theory_free [freef] := by
  have der1 : freef ∈ theory_free := by
    rw [theory_free]
    simp
  apply Derivation.root at der1
  exact der1
-- def der31 : theory_free ⊢ boundf := by
--   have der1 : freef ∈ theory_free := by
--     rw [theory_free]
--     simp
--   apply Derivation.root at der1

-- Trying to prove ∀P(0)∧H(0) from ∀P(0) and ∀H(0)
inductive PH_rel : ℕ → Type where
  | person : PH_rel 1
  | hashead : PH_rel 1

inductive PH_func : ℕ → Type where
  | b : PH_func 0

def PH_lang : Language where
  Func := PH_func
  Rel := PH_rel

-- Printing formulas
def PH_funToStr {n}: PH_func n → String
  | .b => "b"
instance : ToString (PH_func n) := ⟨PH_funToStr⟩

def PH_relToStr {n} : PH_rel n → String
| .person => "P"
| .hashead => "H"
instance : ToString (PH_rel n) := ⟨PH_relToStr⟩

-- Objective: have a Derivation of ∀P(0) from P(0)
-- Question: can one rw to something by definition? Answer: yes
-- But it does not matter: we should show HOW(/WHY) they
-- are the same.
def a_1 : Nat := 1
def b_1 : Nat := a_1

lemma test : a_1 = b_1 := by
  rw[b_1,a_1]


def forall_p : Semiformula PH_lang ℕ 0 :=
  Semiformula.all (Semiformula.rel PH_rel.person ![Semiterm.bvar 1])
def forall_p_bound_free : Semiformula PH_lang ℕ 1 :=
  Semiformula.rel PH_rel.person ![Semiterm.bvar 1]
def free_var : Semiformula PH_lang ℕ 0 :=
  Rewriting.free forall_p_bound_free
def th_p_free : Theory PH_lang := {free_var}
def derivation_forall_p : Derivation th_p_free [forall_p] := by
  have h1 : free_var ∈ th_p_free := by
    rw [th_p_free]
    simp
  apply Derivation.root at h1
  rw[free_var,forall_p_bound_free] at h1
  rw[forall_p]
  have h2 : Derivation th_p_free [forall_p] := Derivation.all h1
  rw [forall_p] at h2
  exact h2
-- okay, this works but it feels like cheating, because the fact that
-- free_var is the same as Rewriting.free forall_b_bound_free is 'hard coded'
-- I'll try to see what happens if we'd want to prove stuff from the
-- peano arithmetic theory.

--

open Theory
-- sets are defined in the following fashion
inductive weekday : Set Nat
  | monday : weekday 1
  | tuesday : weekday 2

def monday : weekday 1 := weekday.monday
def tuesday : weekday 1 := weekday.monday
-- therefore axiom membership for the theory of PAMinus is
-- defined as it is and proven as follows.
lemma lem : PAMinus (“x | x + 0 = x”) := PAMinus.addZero
-- however, (i) how do we get from this notion of membership to
-- the one necessary to get “x | x + 0 = x” into our derivation?
-- Furthermore (ii), how do we get proofs about specific terms
-- from such general formulas?
-- subquestion: how to get “3 + 0 = 3” from “x | x + 0 = x”?
-- subsubquestion: how to get the specific installment of a
-- term in a spot taken by a free variable? Normally under some
-- assignment. Is that possible to get here?
-- Perhaps we have more access to the meaning of the formulas when we
-- use semantic concepts.
-- An other alternative might be to still define our theory syntactically
-- and use derivation₂.
open Semantics
-- def lemmm : PAMinus ⊢ “x | x + 0 = x” := by

def first_PA_ax : Semiformula LPA ℕ 0 :=
  Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ
  ![&0],Semiterm.func LPA_Func.zero ![]]
def instance_first_PA_ax : Semiformula LPA ℕ 0 :=
  Semiformula.nrel LPA_Rel.eq ![(LPA_numeral 3),LPA_null]

#eval first_PA_ax
#eval (Rewriting.fix first_PA_ax)/[LPA_numeral 3]
#check Rewriting.fix (Rewriting.fix first_PA_ax)

def PA : Theory LPA := {first_PA_ax}

-- def lem50 : PA ⊢ instance_first_PA_ax := by
--   have h1 : first_PA_ax ∈ PA := by
--     rw[PA]
--     simp
--   have h2: first_PA_ax ∈ [first_PA_ax] := by
--     simp
--   have h3 : Derivation2 PA {first_PA_ax} := by

--   apply Derivation2.root at h1
--   apply h1

--   -- have h2 (a : Semiformula LPA ℕ 0) : Semiformula LPA ℕ 0 :=
--   --   (Rewriting.fix a)/[LPA_numeral 3]

-- MISLUKT EXPERIMENT:
--def Contains_terms {arity : ℕ} {func : LPA_Func arity} {f : Fin arity → Semiterm LPA ℕ 0}
-- (Semiterm.func func f: Semiterm LPA ℕ 0) : Set Semiterm LPA ℕ 0
--   | .fvar => {Semiterm.func func f}
--   | .bvar => {Semiterm.func func f}
--   | .func => {f}

-- def Substit (φ : Semiterm LPA ℕ 0)(t : Semiterm LPA ℕ 0): Semiterm LPA ℕ 0
--   | .fvar => t
--   | .bvar => φ
--   | .func => Semiterm.func

-- def Substit (φ : Semiformula LPA ℕ 0)(t : Semiterm LPA ℕ 0): Semiformula LPA ℕ 0
--   | φ.all => (Substit φ t).all
--   |





-- #check “x | x + 0 = x”/[LPA_null]

-- #check PAMinus ⊢ “x | x + 0 = x”
-- def lem1 : PAMinus ⊢ “3 + 0 = 3” := by
--   have h : “x | x + 0 = x” ∈ PAMinus := PAMinus.addZero
--   apply Derivation.root at h
--   have h2 : PAMinus “3 + 0 = 3” := by
--     apply “x | x + 0 = 0”/[3]
-- #check PAMinus “x | x + 0 = x”
-- #check “x | x + 0 = x”








-- def forall_h : Semiformula PH_lang ℕ 0 :=
--   Semiformula.all (Semiformula.rel PH_rel.hashead ![Semiterm.bvar 1])
-- def forall_p_h : Semiformula PH_lang ℕ 0 :=
--   Semiformula.all (Semiformula.and
--     (Semiformula.rel PH_rel.person ![Semiterm.bvar 1])
--     (Semiformula.rel PH_rel.hashead ![Semiterm.bvar 1]))

-- #eval forall_p_bound_free/[b]
-- #eval Rewriting.free forall_p_bound_free
-- #check Rewriting.free forall_p_bound_free
-- #eval forall_free_var
-- #eval Rewriting.fix forall_free_var
-- #eval Rewriting.fix (Rewriting.fix forall_free_var)
-- #eval Rewriting.fix (Rewriting.fix (Rewriting.fix forall_free_var))
#eval ∀' forall_p_bound_free
#eval forall_p
#eval Rewriting.fix forall_p
#check Rewriting.free (Rewriting.fix forall_p)
#eval Rewriting.free (Rewriting.fix forall_p)
-- #check (Rewriting.fix forall_p)/[b]
-- #eval (Rewriting.fix forall_p)/[b]
-- #check Rewriting.shift forall_p
-- #check Rewriting.shift forall_p_bound_free
-- #check [forall_p_bound_free]⁺
-- -- #check Derivation.all Derivation.root [Rewriting.free forall_p_bound_free, [forall_p]⁺]
-- #check Rewriting.free forall_p_bound_free
-- #eval Rewriting.free forall_p_bound_free
-- def thing : Semiformula PH_lang ℕ 1 := Semiformula.rel PH_rel.person ![#1]
-- #check Rewriting.free (thing)
-- def PH_theory : Theory PH_lang := {forall_p,forall_h}
-- def derivation_forall_p_h : Derivation PH_theory [forall_p_h] := by
--   have der1 : forall_p ∈ PH_theory := by
--     rw [PH_theory]
--     simp
--   apply Derivation.root at der1
--   apply Derivation.and at der1
--   have der2 : forall_h ∈ PH_theory := by
--     rw [PH_theory]
--     simp
--   apply Derivation.root at der2
--   apply der1 at der2
--   apply Derivation.all










variable {φ : SyntacticSemiformula LPA 1}
#eval free1/[LPA_null]
-- def rewr_func : ∀ h : Semiterm LPA ℕ 0, free1/[h]
-- #check fun h : Semiterm LPA ℕ 0 => free1/[h]
-- #check fun h : Semiterm LPA ℕ 0 => free1/[h]
-- #check Rewriting.free free1 = freef
-- #check Rewriting.free free1
-- #eval Rewriting.free free1
-- #check @Rew.free LPA 0
-- #check @Rew.free LPA 0 ▹ free1
-- #eval @Rew.free LPA 0 ▹ free1
-- def der32 : Rewriting.free := @Rew.free LPA 0 ▹ free1
-- variable {T:Theory LPA}
-- #check @Rew.free LPA 0
-- #check Derivation.all der30
-- #check Derivation.all Derivation.root (mem)

-- -- def der21 : Derivation T [boundf, freef] := Derivation.all


-- def provable7 : theory_free ⊢ boundf := by
--   have der1 : freef ∈ theory_free := by
--     rw [theory_free]
--     simp
--   apply Derivation.root at der1
--   have t1 : Semiterm LPA ℕ 1 := Semiterm.bvar 1
--   have f1 : SyntacticSemiformula LPA 1 := Semiformula.rel LPA_Rel.eq ![t1,t1]
--   have freef : Rewriting.free f1 :=
--   apply Derivation.all at der1


--   have der2 : Derivation theory2 [(Semiformula.rel LPA_Rel.eq ![PA_bound_variable, PA_bound_variable])/[Rew.emb LPA_null]] := by
--     simp
--     exact der1
--   apply Derivation.ex LPA_null der2





-- #check Rewriting.free [freef]
-- def rew_free : Rewriting.free freef

-- def der20 : Derivation T ((boundf) :: [freef]) := Derivation.all (Derivation.root mem4)




-- but how does a formula get in the theory?

-- Inhabited.mk (fun h₁ : LPA.Func 0 => (fun h₂ : Fin 0 → Semiterm LPA ℕ 0 => h₁)) PA_Func.zero

-- open Arith
-- open Theory
-- open Semiformula

-- variable
--   {L : Language}
--   {ξ : Type*}
--   {n : ℕ}

-- lemma sentence {k} (r : LPA.Rel k)(v : Fin k → Semiterm LPA ξ n): ∼(rel r v) = nrel r v := rfl
-- #check sentence

-- open LO
-- open Arith
-- open Language

-- -- variable {M : Type*} [ORingStruc M]
-- -- variable [M ⊧ₘ* 𝐏𝐀⁻]

-- lemma PA_add_zero (x : M) : x + 0 = x := by
--   simpa[models_iff]

-- lemma PA_univ_add_zero: ∀x, x + 0 = x := by
--   simpa[models_iff] using ModelsTheory.models M Theory.PAMinus.mulAssoc (fun _ ↦ x)

-- lemma PA_stuff (h : M): 11 * 2 = 22 := by
--     simpa[models_iff]

-- lemma test_two : 11 * 11 = 121 := by
--   simpa[models_iff]

-- lemma test_three : 100 - 4 = 96 := by
--   simpa[models_iff]

-- lemma test_four (y : M) (h : x = 100) : 2*x = 200 := by
--   rw [h]

-- lemma ind_schema: ∀ x, (x + 2 = x + 2) := by
--   simpa[models_iff]

-- import Mathlib.Data.Set.Basic
-- open Set

-- structure Signature where
--   Const : Type
--   Func : Type
--   Rel : Type
--   ArRel : Rel → Nat
--   ArFunc : Func → Nat

-- inductive PA_Const where
--   | zero

-- inductive PA_Func where
--   | succ
--   | add
--   | mul

-- inductive PA_Rel where
--   | eq : PA_Rel

-- def PA_Ar_Func : PA_Func → Nat
--   | .succ => 1
--   | .add => 2
--   | .mul => 2

-- def PA_Ar_Rel : PA_Rel → Nat
--   | .eq  => 2

-- def PA_Signature : Signature where
--   Const := PA_Const
--   Func :=  PA_Func
--   Rel := PA_Rel
--   ArRel := PA_Ar_Rel
--   ArFunc := PA_Ar_Func

-- inductive var where
--   | one : var
--   | succ : var → var

-- variable (S : Signature)



-- -- def get_terms : Signature → var → term
-- --   | .Const => .Const
-- --   | .Const => var
-- --   | func {f : Signature.Func} {ar : Signature.Func → Nat} => (Fin (ar f) → term) → term

-- -- def PA_term := term PA_Signature

-- -- #check PA_Const.zero
-- -- #check term.const
-- -- #check term.const PA_Signature

-- -- example : Inhabited PA_term := Inhabited.mk (term.const PA_Signature)
-- -- #check Fin 10

-- example : Inhabited (PA_Signature.Func → Nat) := Inhabited.mk PA_Signature.ArFunc
-- -- example : Inhabited Nat := Inhabited.mk 1
-- -- example : Inhabited var := Inhabited.mk (var.succ (var.succ var.one))
-- -- example : Inhabited (Primitive_Term PA_Signature) := Inhabited.mk var.one

-- -- #check Inhabited.mk (var.succ var.one)

-- -- example : PA_Ar_Func .succ = 1 := rfl

-- -- #print Nat
-- -- #print Inhabited

-- -- example : Inhabited Nat := Inhabited.mk 1
-- #check Fin 10
-- #check Fin.isLt

-- example : Inhabited (Fin 1) := Inhabited.mk 0
