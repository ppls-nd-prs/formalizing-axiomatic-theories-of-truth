import FormalizingAxiomaticTheoriesOfTruth.Prelims

open LO
open FirstOrder
open L_T
open PAT

namespace TB
def disquotation_schema (φ : Semiformula signature ℕ 0) : Semiformula signature ℕ 0 :=
  .rel .t ![numeral (Semiformula.toNat (φ))] pt_bi_imp φ
def disquotation_set (Γ : Semiformula signature ℕ 0 → Prop) : Theory signature :=
  { ψ | ∃ φ : Semiformula signature ℕ 0, Γ φ ∧ ψ = (disquotation_schema φ)}
def tb : Theory signature := {φ | t_pat φ ∨ (disquotation_set Set.univ) φ}
end TB


example : ∀φ ∈ lpa, TB.tb ⊢! φ → t_pa ⊢! φ := by
  sorry
