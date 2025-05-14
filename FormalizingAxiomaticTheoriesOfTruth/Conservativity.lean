import FormalizingAxiomaticTheoriesOfTruth.ProofTheory

namespace PA
  open FirstOrder
  open Language
  open L_T
    /-- Peano arithemtic -/
  inductive peano_arithmetic : Set (BoundedFormula ℒ ℕ n) where
    | first : peano_arithmetic (∀' ∼(LPA.null =' S(&0)))
    | second :peano_arithmetic (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
    | third : peano_arithmetic (∀' ((&0 add LPA.null) =' &0))
    | fourth : peano_arithmetic (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
    | fifth : peano_arithmetic (∀' ((&0 times LPA.null) =' LPA.null))
    | sixth : peano_arithmetic (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
    | induction (φ) : peano_arithmetic (induction φ)

  abbrev 𝐏𝐀 := peano_arithmetic

end PA

namespace Conservativity

  theorem conservativity_of_tb : ∀φ ∈ ℒ, 𝐓𝐁 ⊢ φ → 𝐏𝐀 ⊢ φ := by
    sorry

end Conservativity
