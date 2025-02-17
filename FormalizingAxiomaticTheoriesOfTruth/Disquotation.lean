import FormalizingAxiomaticTheoriesOfTruth.Prelims

open LO
open FirstOrder
open L_T
open PAT

namespace TB
def disquotation_schema (φ : Semiformula signature ℕ 0) : Semiformula signature ℕ 0 :=
  (T ![numeral (Semiformula.toNat (φ))]) ↔  φ
def disquotation_set (Γ : Semiformula signature ℕ 0 → Prop) : Theory signature :=
  { ψ | ∃ φ : Semiformula signature ℕ 0, Γ φ ∧ ψ = (disquotation_schema φ)}
def tb : Theory signature := {φ | t_pat φ ∨ (disquotation_set Set.univ) φ}

notation "𝐓𝐁" => tb

end TB

example : ∀φ ∈ ℒₚₐ, 𝐓𝐁 ⊢! φ → 𝐏𝐀 ⊢! φ := by
  sorry
