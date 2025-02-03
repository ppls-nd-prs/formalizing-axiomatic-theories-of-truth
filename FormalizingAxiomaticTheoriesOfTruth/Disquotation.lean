import FormalizingAxiomaticTheoriesOfTruth.Prelims

open LO
open FirstOrder

/-
# The definition of TB
-/
open L_T
open PAT
namespace TB
def disquotation_schema (φ : Semiformula lt ℕ 0) : SyntacticFormula lt :=
  .rel .t ![numeral (Semiformula.toNat (φ))] pt_bi_imp φ
def disquotation_set (Γ : Semiformula lt ℕ 0 → Prop) : Theory lt :=
  { ψ | ∃ φ : Semiformula lt ℕ 0, Γ φ ∧ ψ = (disquotation_schema φ)}
def tb : Theory lt := axiom_set + disquotation_set Set.univ

end TB

/-
Proof that T⌜=(0,0)⌝ ↔ =(0,0) ∈ tb
-/
open L_T
open TB
def formula_eq_null : Semiformula lt ℕ 0 :=
  .rel .eq ![null,null]
def disquotation : Semiformula lt ℕ 0 :=
  .rel .t ![numeral (formula_eq_null.toNat)] pt_bi_imp formula_eq_null
example : disquotation ∈ tb := by
  have step1 : (disquotation ∈ tb) = (disquotation ∈ axiom_set + {ψ | ∃ φ, Set.univ φ ∧ ψ = disquotation_schema φ}) := by
    rw[tb,disquotation_set]
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
  have step7 : disquotation ∈ {ψ | ∃ φ, Set.univ φ ∧ ψ = disquotation_schema φ} := by
    exact step6
  have step8 : disquotation ∈ {ψ | ∃ φ, Set.univ φ ∧ ψ = disquotation_schema φ} → disquotation ∈ axiom_set + {ψ | ∃ φ, Set.univ φ ∧ ψ = disquotation_schema φ} := by
    apply Set.mem_union_right
  have step9 : disquotation ∈ axiom_set + {ψ | ∃ φ, Set.univ φ ∧ ψ = disquotation_schema φ} := by
    apply step8 step7
  have step10 : disquotation ∈ tb := by
    apply step1.mpr step9
  exact step10

/-
A function for translating PA.lpa formulas to L_T.lt formulas
-/
open PA
def to_lt_func {arity : ℕ} : (lt.Func arity) → (lt.Func arity)
  | .zero => .zero
  | .succ => .succ
  | .add => .add
  | .mult => .mult

def to_lt_rel {n : ℕ} : (lpa.Rel n) → (lt.Rel n)
  | .eq => .eq

def to_lt_t {n : ℕ}: Semiterm lpa ℕ n → Semiterm lt ℕ n
  | #x => #x
  | &x => &x
  | .func f v => .func (to_lt_func f) (fun i => to_lt_t (v i))

def to_lt_vt {k n: ℕ} (v : Fin k → Semiterm lpa ℕ n) : Fin k → Semiterm lt ℕ n :=
  fun i => to_lt_t (v i)

def to_lt_f {n : ℕ} : Semiformula lpa ℕ n → Semiformula lt ℕ n
| .verum => .verum
| .falsum => .falsum
| .rel r v => .rel (to_lt_rel r) (to_lt_vt v)
| .nrel r v => .nrel (to_lt_rel r) (to_lt_vt v)
| .and φ ψ => .and (to_lt_f φ) (to_lt_f ψ)
| .or φ ψ => .or (to_lt_f φ) (to_lt_f ψ)
| .all φ => .all (to_lt_f φ)
| .ex φ => .ex (to_lt_f φ)

example {n : ℕ}: ∀φ:Semiformula lpa ℕ n, ∃ψ:Semiformula lt ℕ n, ψ = to_lt_f φ :=
  fun a : Semiformula lpa ℕ n => Exists.intro (to_lt_f a) (Eq.refl (to_lt_f a))

/-
Function for translating derivations from tb to derivations from t_pa
-/
open TB
-- def to_pa_der {n : ℕ} (φ : Semiformula lt ℕ 0) (ψ : Semiformula lpa ℕ 0) (h : φ = to_lt_f ψ): Derivation tb (φ :: Γ) → Derivation t_pa (ψ :: Δ)
-- | .root φ => .root ψ
-- | .axL (φ :: Γ) r v => .axL (ψ :: Δ) r v
