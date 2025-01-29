import Foundation.Logic.Predicate.Language
import FormalizingAxiomaticTheoriesOfTruth.Basic
import Mathlib.Lean.Meta



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

/-
A to and fro coding of an LPA and LTr formula.
Firstly, a coding for the function and relations symbols
must be defined (see Basic.lean).
Then we can code a given formula
-/
def code_PA_eq_null : ℕ := PA_eq_null.toNat
def code_LTr_f1 : ℕ := LTr_f1.toNat
#eval code_PA_eq_null
#eval code_LTr_f1

/-
Next we can decode these codes, but since the decoding is
a partial function from ℕ to Semiformula L ξ n, we need
a default formula that answers to all ℕ's that do not
map to any formula in the intended language.
-/
def default_LPA : Semiformula LPA ℕ 0 := ⊥
def default_LTr : Semiformula LTr ℕ 0 := ⊥
def decoded_code_PA_eq_null : Semiformula LPA ℕ 0 :=
  (Semiformula.ofNat 0 code_PA_eq_null).getD default_LPA
def decoded_code_LTr_f1 : Semiformula LTr ℕ 0 :=
  (Semiformula.ofNat 0 code_LTr_f1).getD default_LTr
#eval decoded_code_PA_eq_null
#eval decoded_code_LTr_f1

/-
# SCRATCH WORK FROM HERE ON OUT
## Scratch work with our own LPA and LTr
-/
-- Goal: have ¬=(S(S(S(0))),0) from PA axiom 1.
infixr:60 " imp " => Arrow.arrow
prefix:60 "p_succ" => Semiterm.func LPA_Func.succ
prefix:60 "p_eq" => Semiformula.rel LPA_Rel.eq
prefix:60 "p_zero" => Semiterm.func LPA_Func.zero
prefix:60 "p_add" => Semiterm.func LPA_Func.add
prefix:60 "p_mult" => Semiterm.func LPA_Func.mult

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

  -- .all (.all ((Semiformula.rel LPA_Rel.eq ![(psucc ![#1]),(psucc ![#0])]) imp (.rel .eq ![#1,#0])))
def instance_first_PA_ax : Semiformula LPA ℕ 0 :=
  Semiformula.nrel LPA_Rel.eq ![(LPA_numeral 3),LPA_null]

#eval first_PA_ax_b_free/[LPA_numeral 3]
#eval (Rewriting.fix first_PA_ax)/[LPA_numeral 3]
#check (Rewriting.fix (Rewriting.fix first_PA_ax))

def finset1 : Finset ℕ := {1,2,3}
#check finset1

def PA : Theory LPA := {first_PA_ax}

def full_PA : Theory LPA := {first_PA_ax,
                        second_PA_ax,
                        third_PA_ax,
                        fourth_PA_ax,
                        fifth_PA_ax,
                        sixth_PA_ax}

#eval (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![#0], Semiterm.func LPA_Func.zero ![]])/[LPA_numeral 2]

open Semiterm

example : (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![#0], Semiterm.func LPA_Func.zero ![]])/[LPA_numeral 2] = (Rew.substs ![LPA_numeral 2]) ▹ (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![#0], Semiterm.func LPA_Func.zero ![] ]) :=
  Eq.refl ((Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![#0], Semiterm.func LPA_Func.zero ![]])/[LPA_numeral 2])

example : (Rew.substs ![LPA_numeral 2]) ▹ (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![#0], Semiterm.func LPA_Func.zero ![] ]) = Rewriting.app (Rew.substs ![LPA_numeral 2]) (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![#0], Semiterm.func LPA_Func.zero ![] ]):=
  Eq.refl ((Rew.substs ![LPA_numeral 2]) ▹ (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![#0], Semiterm.func LPA_Func.zero ![] ]))

-- example : Rewriting.app (Rew.substs ![LPA_numeral 2]) (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![#0], Semiterm.func LPA_Func.zero ![] ]) = Rewriting.app (bind ![LPA_numeral 2] fvar) (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![#0], Semiterm.func LPA_Func.zero ![] ]) :=
  -- Eq.refl (Rewriting.app (Rew.substs ![LPA_numeral 2]) (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![#0], Semiterm.func LPA_Func.zero ![] ]))

#check ((fun (eq1 : (LPA_numeral 3) = .func .succ ![LPA_numeral 2]) (h2 : PA ⟹ [first_PA_ax]) => (Derivation.specialize (LPA_numeral 2) h2))
    (Eq.refl (LPA_numeral 3)))

theorem thm23 : (PA ⟹ [instance_first_PA_ax]) = (PA ⟹ [(Semiformula.nrel LPA_Rel.eq ![func LPA_Func.succ ![#0], func LPA_Func.zero ![]])/[LPA_numeral 2]]) :=
  Eq.mpr
  (id
    (congrArg (fun x ↦ (PA ⟹ [instance_first_PA_ax]) = (PA ⟹ [x]))
      (Eq.trans (Semiformula.rew_nrel2 (Rew.substs ![LPA_numeral 2]))
        (congrArg (Semiformula.nrel LPA_Rel.eq)
          (congr
            (congrArg Matrix.vecCons
              (Eq.trans (Rew.func1 (Rew.substs ![LPA_numeral 2]) LPA_Func.succ #0)
                (congrArg (fun x ↦ func LPA_Func.succ ![x])
                  (Eq.trans (Rew.substs_bvar ![LPA_numeral 2] 0) (Matrix.cons_val_fin_one (LPA_numeral 2) ![] 0)))))
            (congrArg (fun x ↦ ![x]) (Rew.func0 (Rew.substs ![LPA_numeral 2]) LPA_Func.zero ![])))))))
  (Eq.refl (PA ⟹ [instance_first_PA_ax]))

#print thm23

def provable_instance_4 : PA ⊢ instance_first_PA_ax :=
(fun h1 : PA ⟹ [instance_first_PA_ax] => Derivation.provableOfDerivable h1)
  ((fun h2 : PA ⟹ [(Semiformula.nrel LPA_Rel.eq ![func LPA_Func.succ ![#0], func LPA_Func.zero ![]])/[LPA_numeral 2]] =>
    thm23.mpr h2)
    ((fun h3 : PA ⟹ [first_PA_ax] => Derivation.specialize (LPA_numeral 2) h3)
      ((fun h4 : first_PA_ax ∈ PA => Derivation.root h4)
        ((fun h5 : first_PA_ax ∈ {first_PA_ax} => (congrArg (fun _a => first_PA_ax ∈ _a) (PA.eq_1)).mpr h5)
            (Set.mem_singleton_iff.mpr (Eq.refl first_PA_ax))))))

/-
* So, this goes well, but thm23 is just very complicated, i.e. #print thm23 yields

theorem thm23 : (PA ⟹ [instance_first_PA_ax]) =
  (PA ⟹ [(Semiformula.nrel LPA_Rel.eq ![func LPA_Func.succ ![#0], func LPA_Func.zero ![]])/[LPA_numeral 2]]) :=
Eq.mpr
  (id
    (congrArg (fun x ↦ (PA ⟹ [instance_first_PA_ax]) = (PA ⟹ [x]))
      (Eq.trans (Semiformula.rew_nrel2 (Rew.substs ![LPA_numeral 2]))
        (congrArg (Semiformula.nrel LPA_Rel.eq)
          (congr
            (congrArg Matrix.vecCons
              (Eq.trans (Rew.func1 (Rew.substs ![LPA_numeral 2]) LPA_Func.succ #0)
                (congrArg (fun x ↦ func LPA_Func.succ ![x])
                  (Eq.trans (Rew.substs_bvar ![LPA_numeral 2] 0) (Matrix.cons_val_fin_one (LPA_numeral 2) ![] 0)))))
            (congrArg (fun x ↦ ![x]) (Rew.func0 (Rew.substs ![LPA_numeral 2]) LPA_Func.zero ![])))))))
  (Eq.refl (PA ⟹ [instance_first_PA_ax]))

-/



def step01 : Eq PA {first_PA_ax} :=
  Eq.refl PA
#check first_PA_ax ∈ PA
#check Eq.refl PA
#print PA.eq_1
#check Eq.refl first_PA_ax
#check Set.mem_singleton_iff.mpr (Eq.refl first_PA_ax)
#check Eq.mpr (id (congrArg (fun _a ↦ first_PA_ax ∈ _a) PA.eq_1)) (Set.mem_singleton_iff.mpr (Eq.refl first_PA_ax))

def provable_instance_3 : PA ⊢ instance_first_PA_ax :=
  (fun step1 : first_PA_ax ∈ PA =>
    (fun step2 : PA ⟹ [first_PA_ax] =>
      (fun step3 : (PA ⟹. instance_first_PA_ax) = (PA ⟹. .nrel .eq ![LPA_numeral 3, LPA_null]) =>
        (fun step4 : (PA ⟹. .nrel .eq ![LPA_numeral 3, LPA_null]) = (PA ⟹. .nrel .eq ![.func .succ ![LPA_numeral 2], LPA_null]) =>
          (fun step5 : (PA ⟹. .nrel .eq ![.func .succ ![LPA_numeral 2], LPA_null]) = (PA ⟹..nrel LPA_Rel.eq ![.func .succ ![LPA_numeral 2], .func .zero ![]]) =>
            (fun step6 : (PA ⟹ [(Rewriting.app (Rew.substs ![LPA_numeral 2])) (Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![#0], Semiterm.func LPA_Func.zero ![]])]) = (PA ⟹ [Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![LPA_numeral 2], Semiterm.func LPA_Func.zero ![]]]) =>
              (fun step7 : PA ⊢ instance_first_PA_ax =>
                Derivation.provableOfDerivable step7)
            (step3.mpr (step4.mpr (step5.mpr (step6.mp (Derivation.specialize (LPA_numeral 2) step2))))))
          (congrArg (fun x ↦ PA ⟹ [x]) (Eq.trans (Semiformula.rew_nrel2 (Rew.substs ![LPA_numeral 2])) (congrArg (Semiformula.nrel LPA_Rel.eq) (congr (congrArg Matrix.vecCons (Eq.trans (Rew.func1 (Rew.substs ![LPA_numeral 2]) LPA_Func.succ #0) (congrArg (fun x ↦ Semiterm.func LPA_Func.succ ![x]) (Eq.trans (Rew.substs_bvar ![LPA_numeral 2] 0) (Matrix.cons_val_fin_one (LPA_numeral 2) ![] 0))))) (congrArg (fun x ↦ ![x]) (Rew.func0 (Rew.substs ![LPA_numeral 2]) LPA_Func.zero ![])))))))
        (id (congrArg (fun _a ↦ PA ⟹. Semiformula.nrel LPA_Rel.eq ![Semiterm.func LPA_Func.succ ![LPA_numeral 2], _a]) LPA_null.eq_1)))
      (congrArg (fun _a ↦ PA ⟹. .nrel .eq ![_a, LPA_null]) (LPA_numeral.eq_2 2)))
    (congrArg (fun _a ↦ PA ⟹. _a) instance_first_PA_ax.eq_1))
   (Derivation.root step1))
  (Eq.mpr ((congrArg (fun _a ↦ first_PA_ax ∈ _a) PA.eq_1)) (Set.mem_singleton_iff.mpr (Eq.refl first_PA_ax)))

example : Semiformula.rel LPA_Rel.eq ![LPA_null,LPA_null] = Semiformula.rel LPA_Rel.eq ![Semiterm.func LPA_Func.zero ![],LPA_null] :=
  congrArg (fun _a => Semiformula.rel LPA_Rel.eq ![LPA_null, LPA_null]) (LPA_null.eq_1)

/- NOTES:
* PA.eq_1 produces the proposition that PA is equal to
what it is defined as being equal to, i.e. {first_PA_axiom}.
* This proof seems unnecessarily lengthy; that might be solved
by starting out with the real things.
* Rewriting parts of the equation can be done with congrArg (see above).
* Some under the hood weirdness is happening with "_auxLemma.nn" terms.
* let can be used in
-/

def provable_instance : PA ⊢ instance_first_PA_ax := by
  have step1 : first_PA_ax ∈ PA := by
    rw [PA]
    simp
  have step2 : PA ⟹ [first_PA_ax] := by
    apply Derivation.root at step1
    exact step1
  have step3 : PA ⟹. instance_first_PA_ax := by
    apply Derivation.specialize (LPA_numeral 2) at step2
    rw[instance_first_PA_ax]
    simp at step2
    rw[LPA_numeral,LPA_null]
    exact step2
  apply Derivation.provableOfDerivable
  exact step3


#print provable_instance


def provable_instance_2 : PA ⊢ instance_first_PA_ax :=
let_fun step1 := provable_instance.proof_2;
let_fun step2 := Derivation.root step1;
let_fun step3 :=
  provable_instance.proof_3.mpr
    (provable_instance.proof_4.mpr
      (provable_instance.proof_5.mpr (provable_instance.proof_6.mp (Derivation.specialize (LPA_numeral 2) step2))));
Derivation.provableOfDerivable step3


/-
∀ {α : Type} {a b : α}, (a ∈ {b}) = (a = b)
-/

#print provable_instance.proof_3


def t2 : Semiterm LPA ℕ 1 := Semiterm.func LPA_Func.zero ![]
def t3 : Semiterm LPA ℕ 1 := #0
def f1 : Semiformula LPA ℕ 2 := Semiformula.rel LPA_Rel.eq
![#0, #1]
-- def t4 : Semiterm LPA ℕ 1 := Semiterm.func LPA_Func.add ![t2,t3]
#eval f1
#eval (∀' f1) -- TODO: search for relation with theoretical level
#eval (∀' f1)/[t3]
-- #eval t4/[LPA_numeral 2]

-- can you construct a semiformula from semiterms with a
-- different numbers of free bound variables? Answer: no (see below)
def tk0 : Semiterm LPA ℕ 2 := &0
def tk1 : Semiterm LPA ℕ 2 := &1
def tl : Semiterm LPA ℕ 1 := #0
-- def f2 : Semiformula LPA ℕ 2 := Semiformula.rel LPA_Rel.eq ![tk,tk]

-- can you subsitute in semiformulas with a number of free
-- bound variables different than 1? Answer: no (see below)
def f3 : Semiformula LPA ℕ 2 :=
  ∀' .rel .eq ![#0,&1]
#eval f3/[tk0,tk1]
#check f3/[tk0,tk1]

-- variable [(k : ℕ) → Encodable (LPA.Func k)]



#eval f3
#eval (Rewriting.free f3)
#eval ∀' f3 -- d.b. : ∀=(2,0)
#eval ∀' ∀' f3
#check Semiformula.toNat (∀' ∀' f3)
#eval Semiformula.toNat (∀' ∀' f3)
#check Semiformula.ofNat (23460333233568182948710079090855127361868625011856248581350574429543027046250562210549328935436759433571486259413131829967353055270420113831862126666494661623578231846968) 0
universe u

def thing4 : Semiformula LPA ℕ 0 :=
  (Semiformula.ofNat 0 23460333233568182948710079090855127361868625011856248581350574429543027046250562210549328935436759433571486259413131829967353055270420113831862126666494661623578231846968).getD PA_f3
#eval thing4

-- def thing : ℕ := Semiformula.toNat (f3)
-- def thing2 : Semiformula LPA ℕ 0 := Semiformula.ofNat thing
-- #eval Semiformula.ofNat (Semiformula.toNat (f3))
-- Note: the i-th bound variable is bound by the i-th quantifier that
-- is added to the left of the expression (see notebook 22/1/'25 for
-- notational details)

/-
# Sratch work with FFL's PA
-/
open Theory
open Set

def formula : Semiformula ℒₒᵣ ℕ 0 := “x | x + 0 = x”
open Language
-- #check Rewriting.free (Rewriting.shift formula)
-- #eval Rewriting.free (Rewriting.shift formula)
def one : Semiterm ℒₒᵣ ℕ 0 :=
  Semiterm.func ORing.Func.one ![]
#check (Rewriting.fix formula)/[one]
#eval (Rewriting.fix formula)/[one]

def ffl_provable_instance : 𝐏𝐀 ⊢ “3 + 0 = 3” := by
  have step1 : “x | x + 0 = x” ∈ 𝐏𝐀⁻ := PAMinus.addZero
  have step2 : 𝐏𝐀 = 𝐏𝐀⁻ + indScheme ℒₒᵣ Set.univ := Eq.refl 𝐏𝐀
  have step3 : 𝐏𝐀⁻ + indScheme ℒₒᵣ Set.univ ⊆ 𝐏𝐀 :=
    Eq.subset step2
  have step4 : 𝐏𝐀⁻ + indScheme ℒₒᵣ Set.univ = 𝐏𝐀⁻ ∪ indScheme ℒₒᵣ Set.univ :=
    Eq.refl (𝐏𝐀⁻ + indScheme ℒₒᵣ Set.univ)
  have step5 : 𝐏𝐀⁻ ⊆ 𝐏𝐀⁻ ∪ indScheme ℒₒᵣ Set.univ :=
    fun _ => Or.inl
  have step6 : 𝐏𝐀⁻ ⊆ 𝐏𝐀:=
    Subset.trans (step5) (step3)
  have step7 : “x | x + 0 = x” ∈ 𝐏𝐀 :=
    (mem_of_subset_of_mem step6) step1
  sorry



  -- have step3 : “x | x + 0 = x” ∈ 𝐏𝐀⁻ → “x | x + 0 = x” ∈ 𝐏𝐀 :=
  --   fun h : “x | x + 0 = x” ∈ 𝐏𝐀⁻ =>
  -- -- have step2 : PA ⟹ [first_PA_ax] := by
  -- --   apply Derivation.root at step1
  -- --   exact step1
  -- -- have step3 : PA ⟹. instance_first_PA_ax := by
  -- --   apply Derivation.specialize (LPA_numeral 2) at step2
  -- --   rw[instance_first_PA_ax]
  -- --   simp at step2
  -- --   rw[LPA_numeral,LPA_null]
  -- --   exact step2
  -- -- apply Derivation.provableOfDerivable
  -- -- exact step3
