import FormalizingAxiomaticTheoriesOfTruth.Prelims
import Foundation.FirstOrder.Basic.Coding
import Foundation.FirstOrder.Basic.Calculus

open LO
open FirstOrder
open L_T
open PAT

namespace TB

notation:25 "⌜" φ:25 "⌝" => numeral (Semiformula.toNat φ)

def disquotation_schema (φ : SyntacticFormula signature) : SyntacticFormula signature :=
  (T ![⌜φ⌝]) ⇔  φ
def disquotation_set (Γ : SyntacticFormula signature → Prop) : Theory signature :=
  { ψ | ∃ φ ∈ ℒₚₐ, Γ φ ∧ ψ = (disquotation_schema φ)}
def tb : Theory signature := {φ | φ ∈ 𝐏𝐀𝐓 ∨ φ ∈ (disquotation_set Set.univ)}

notation "𝐓𝐁" => tb

end TB

example : ∀φ ∈ ℒₚₐ, 𝐓𝐁 ⊢! φ → 𝐏𝐀 ⊢! φ := by
  sorry
