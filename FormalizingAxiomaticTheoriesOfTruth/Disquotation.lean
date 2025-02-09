import FormalizingAxiomaticTheoriesOfTruth.Prelims

open LO
open FirstOrder

/-
# The definition of TB
-/
open L_T
open PAT
namespace TB
def disquotation_schema (φ : Semiformula PA.lpa ℕ 0) : Semiformula lt ℕ 0 :=
  .rel .t ![numeral (Semiformula.toNat (φ))] pt_bi_imp φ
def disquotation_set (Γ : Semiformula lt ℕ 0 → Prop) : Theory lt :=
  { ψ | ∃ φ : Semiformula PA.lpa ℕ 0, Γ φ ∧ ψ = (disquotation_schema φ)}
def tb : Theory lt := {φ | t_pat φ ∨ (disquotation_set Set.univ) φ}
end TB

/-
Proof that T⌜=(0,0)⌝ ↔ =(0,0) ∈ tb
-/
open L_T
open TB
def formula_eq_null : Semiformula PA.lpa ℕ 0 :=
  .rel .eq ![PA.null,PA.null]
def disquotation : Semiformula lt ℕ 0 :=
  .rel .t ![numeral (formula_eq_null.toNat)] pt_bi_imp formula_eq_null
example : tb disquotation := by
  have step1 : (tb disquotation) = (t_pat disquotation ∨ {ψ | ∃ φ, Set.univ φ ∧ ψ = disquotation_schema φ} disquotation) := by
    rfl
  have step2 : formula_eq_null ∈ Set.univ := by simp
  have step3 : Set.univ formula_eq_null := by
    apply step2
  have step4 : disquotation = disquotation_schema formula_eq_null := by
    rw[disquotation_schema,disquotation]
  have step5 : Set.univ formula_eq_null ∧ disquotation = disquotation_schema formula_eq_null := by
    apply And.intro
    exact step3
    exact step4
  have step6 : ∃ φ, Set.univ φ ∧ disquotation = disquotation_schema φ := by
    apply Exists.intro formula_eq_null step5
  have step7 : {ψ | ∃ φ, Set.univ φ ∧ ψ = disquotation_schema φ} disquotation := by
    exact step6
  have step8 : {ψ | ∃ φ, Set.univ φ ∧ ψ = disquotation_schema φ} disquotation → t_pat disquotation ∨ {ψ | ∃ φ, Set.univ φ ∧ ψ = disquotation_schema φ} disquotation := by
    apply Or.intro_right
  have step9 : t_pat disquotation ∨ {ψ | ∃ φ, Set.univ φ ∧ ψ = disquotation_schema φ} disquotation := by
    apply step8 step7
  have step10 : tb disquotation := by
    apply step1.mpr step9
  exact step10

open Sandbox
open PA
/-
# Trying to formalize the steps of Halbach's theorem 7.2 on the conservativity of TB
-/
lemma to_lt_phi_eq_phi_to_lt (φ : Semiformula lpa ℕ 1): to_lt_f (φ/[PA.zero_term].and (∀' (φ pt_imp φ/[PA.succ_var_term])) pt_imp ∀' φ) =
  (to_lt_f φ)/[PAT.zero_term].and (∀' (to_lt_f φ pt_imp (to_lt_f φ)/[PAT.succ_var_term])) pt_imp ∀' to_lt_f φ := by
    cases φ with
      | verum =>
        have step1 : PA.zero_term = PAT.zero_term := by rfl
        have step2 : PA.succ_var_term = PAT.succ_var_term := by rfl
        have step3 {n : ℕ}(t : Semiterm lpa ℕ n) : Semiformula.verum/[t] = Semiformula.verum := by
          rfl
        rw[step3,step3]
        have step4 {n : ℕ}(t : Semiterm lt ℕ n) : (to_lt_f Semiformula.verum)/[t] = (to_lt_f Semiformula.verum) := by
          rfl
        rw[step4,step4]
        sorry
      | falsum => sorry
      | rel => sorry
      | nrel => sorry
      | and => sorry
      | or => sorry
      | all => sorry
      | ex => sorry

lemma pa_ind_eq_pat_ind (φ : Semiformula lpa ℕ 1) : (PA.induction_schema φ) = (PAT.induction_schema φ) := by
  rw[PA.induction_schema,PAT.induction_schema]
  apply to_lt_phi_eq_phi_to_lt

lemma pa_ind_to_pat_ind (φ : Semiformula lpa ℕ 0) : (PA.induction_set Set.univ) φ → (PAT.induction_set Set.univ) φ := by
  rw[PA.induction_set,PAT.induction_set]
  intro h
  have step1 (φ_1 : Semiformula lpa ℕ 1): (PA.induction_schema φ_1) = (PAT.induction_schema φ_1) := by
    apply pa_ind_eq_pat_ind
  sorry

lemma all_pa_ind_pat_ind : ∀φ : Semiformula lpa ℕ 0,(PA.induction_set Set.univ) φ → (PAT.induction_set Set.univ) φ := by
sorry

lemma lem2 (φ : Semiformula lpa ℕ 0) : t_pa φ → tb φ := by
  rw[t_pa,tb,t_pat]
  intro h1
  cases h1 with
  | inl t =>
    apply Or.intro_left
    apply Or.intro_left
    apply all_pa_ax_pat_ax
    exact t
  | inr t =>
    apply Or.intro_left
    apply Or.intro_right
    sorry

def derivation_tb_to_derivation_t_pa (φ : Semiformula lpa ℕ 0) : tb ⟹. to_lt_f φ → t_pa ⟹. φ := by
  sorry

def derivation_to_entails (L : Language)(T : Theory L)(φ : Semiformula L ℕ 0) : T ⟹. φ → T ⊢! φ := by
  intro h
  apply Derivation.provableOfDerivable at h
  sorry
  -- have step1 {F : Type} {S : Type} [System F S] (𝓢 : S) (f : F) : System.Provable φ := Nonempty (h)

lemma lem3 : Nonempty (Nat) :=
  Nonempty.intro Nat.zero

-- variable (a : formula_eq_null ∈ tb)
-- lemma lem5 : Nonempty (tb ⊢ (formula_eq_null)) := by
--   have h1 : formula_eq_null ∈ tb := sorry
--   have h2 : System (Semiformula lt ℕ 0) (Derivation tb [formula_eq_null]) :=
--     System.Prf (Derivation.root h1) formula_eq_null
--   apply Nonempty.intro (Derivation.root h1)

-- #check System.Prf (Derivation.root a) (formula_eq_null)

-- lemma lem2 : System.Provable PA.first_axiom tb :=


-- theorem conservativity_of_tb : ∀φ:Semiformula lpa ℕ 0, (tb ⊢! to_lt_f φ) → (t_pa ⊢! φ) := by
--   intro h1
--   intro h2
--   apply derivation_to_entails at h2
--   apply derivation_tb_to_derivation_t_pa at h

--   sorry

example : ∀φ : Semiformula PA.lpa ℕ 0, PA.t_pa φ → tb φ :=
  fun φ : Semiformula PA.lpa ℕ 0 => sorry


/-
Perhaps making our own definition of a proof in a system works.
-/
-- inductive A : (Semiformula L ℕ 0) → (Derivation T [f]) → Type
--   Prf : A f d

  -- theorem ax_pa_sub_ax_tb :

-- /-
-- We should first prove that the theory of PA is a subset of TB from the
-- -/

-- /-
-- Halbach's theorem 7.5 (conservativity of tb)
-- -/
theorem conservativity_tb : ∀φ : Semiformula PA.lpa ℕ 0, ∀ψ: Semiformula lt ℕ 0, (φ = ψ) → (tb ⊢! ψ → PA.t_pa ⊢! φ) := by
sorry

-- intro φ
-- intro ψ
-- intro h
-- intro h2



-- intro h
-- |.root
-- sorry


-- def to_lpa_func {arity : ℕ} : (lt.Func arity) → (lpa.Func arity)
--   | .zero => .zero
--   | .succ => .succ
--   | .add => .add
--   | .mult => .mult

-- def to_lpa_rel {n : ℕ} : (lt.Rel n) → Option (lpa.Rel n)
--   | .t => none
--   | .eq => some .eq

-- def to_lpa_t {n : ℕ}: Semiterm lt ℕ n → Semiterm lpa ℕ n
--   | #x => #x
--   | &x => &x
--   | .func f v => .func (to_lpa_func f) (fun i => to_lpa_t (v i))

-- def to_lpa_vt {k n: ℕ} (v : Fin k → Semiterm lt ℕ n) : Fin k → Semiterm lpa ℕ n :=
--   fun i => to_lpa_t (v i)

-- def dflt {n : ℕ}: Semiformula lpa ℕ n := ⊥ -- working with defaults is iffy but I dont see a way around it

-- def not_contains_T {n : ℕ} : Semiformula lt ℕ n → Bool
--   | .verum => true
--   | .falsum => true
--   | .rel .eq _ => true
--   | .rel .t _ => false
--   | .nrel .eq _ => true
--   | .nrel .t _ => false
--   | .and φ ψ => (not_contains_T φ) ∧ (not_contains_T ψ)
--   | .or φ ψ => (not_contains_T φ) ∧ (not_contains_T ψ)
--   | .all φ => (not_contains_T φ)
--   | .ex φ => (not_contains_T φ)

-- -- some sanity checks
-- def formula_t_null : Semiformula lt ℕ 0 := .rel .t ![null]
-- def formula_and : Semiformula lt ℕ 0 := .and formula_eq_null formula_t_null
-- def formula_all_1 : Semiformula lt ℕ 0 := ∀' (.rel .t ![#0])
-- def formula_ex_1 : Semiformula lt ℕ 0 := ∃' (.rel .eq ![#0,#0])
-- #eval not_contains_T formula_eq_null -- true
-- #eval not_contains_T formula_t_null -- false
-- #eval not_contains_T formula_and -- false
-- #eval not_contains_T formula_all_1 -- false
-- #eval not_contains_T formula_ex_1 -- true

-- /-
-- We can now construct the set containing only lt formulas that do not have a T
-- -/

-- def no_t_lt {n : ℕ}: Set (Semiformula lt ℕ n) := fun φ => ¬ not_contains_T φ
-- #eval ¬ not_contains_T formula_eq_null
-- #eval ¬ not_contains_T formula_t_null

-- def to_lpa_f {n : ℕ} : Semiformula lt ℕ n → Semiformula lpa ℕ n
-- | .verum => .verum
-- | .falsum => .falsum
-- | .rel .eq v => (.rel (.eq) (to_lpa_vt v))
-- | .rel .t v => (.rel)
-- | .nrel .eq v => (.nrel (.eq) (to_lpa_vt v))
-- | .and φ ψ => (.and ((to_lpa_f φ)) ((to_lpa_f ψ)))
-- | .or φ ψ => .or (to_lpa_f φ) (to_lpa_f ψ)
-- | .all φ => Semiformula.all ((to_lpa_f φ))
-- | .ex φ => Semiformula.ex ((to_lpa_f φ))

-- def to_lpa_seq : Sequent lt → Sequent lpa
-- | .nil => .nil
-- | .cons a Γ => .cons ((to_lpa_f a).getD dflt) (to_lpa_seq Γ)


-- /-
-- Function for translating derivations from tb to derivations from t_pa
-- -/
-- open TB
-- | .root h => .root (φ ∈ t_pa)
-- | .axL Γ .eq v => .axL (to_lpa_seq Γ) (to_lpa_rel r)
