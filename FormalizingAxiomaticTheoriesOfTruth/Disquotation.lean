import FormalizingAxiomaticTheoriesOfTruth.Prelims

open LO
open FirstOrder

/-
# The definition of TB
-/
namespace TB
open L_T
open PAT
def disquotation_schema (φ : Semiformula lt ℕ 0) : SyntacticFormula lt :=
  .rel .t ![numeral (Semiformula.toNat (φ))] pt_bi_imp φ
def disquotation_set (Γ : Semiformula lt ℕ 0 → Prop) : Theory lt :=
  { ψ | ∃ φ : Semiformula lt ℕ 0, Γ φ ∧ ψ = (disquotation_schema φ)}
def tb : Theory lt := axiom_set + disquotation_set Set.univ
