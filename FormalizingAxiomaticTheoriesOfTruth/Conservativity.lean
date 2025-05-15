import FormalizingAxiomaticTheoriesOfTruth.ProofTheory

namespace PA
  open FirstOrder
  open Language
  open L_T

  variable {n : ℕ}
  def g (t : L_T.signature.Term (ℕ ⊕ (Fin n))): Fin (n + 1) → (Fin n)
    | n + 1 => sorry
    | _ => sorry
  def induction_subst : {n : ℕ} → (t : L_T.signature.Term (ℕ ⊕ Fin n)) → ℕ ⊕ Fin (n + 1) → L_T.signature.Term (ℕ ⊕ (Fin n))
    | _, _, .inl v => Term.var (.inl v)
    | n, t, .inr v =>
      ite (v = (n + 1)) t (Term.var (.inr v))

  def induction (φ : L_T.signature.BoundedFormula ℕ (n + 1)) (t : L_T.signature.Term (ℕ ⊕ Fin n)) : L_T.signature.BoundedFormula ℕ n :=
    BoundedFormula.relabel id (BoundedFormula.subst φ.toFormula (fun i : ℕ ⊕ Fin (n + 1) => ite (i = (.inr 1)) t (Term.var (.inr (i - 1)))))

    /-- Peano arithemtic -/
  inductive peano_arithmetic : Set (L_T.signature.BoundedFormula ℕ n) where
    | first : peano_arithmetic (∀' ∼(zero =' S(&0)))
    | second :peano_arithmetic (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
    | third : peano_arithmetic (∀' ((&0 add zero) =' &0))
    | fourth : peano_arithmetic (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
    | fifth : peano_arithmetic (∀' ((&0 times zero) =' zero))
    | sixth : peano_arithmetic (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
    | induction (φ) : peano_arithmetic (induction φ)

  scoped notation "𝐏𝐀" => peano_arithmetic

end PA

namespace Conservativity

  theorem conservativity_of_tb : ∀φ ∈ ℒ, 𝐓𝐁 ⊢ φ → 𝐏𝐀 ⊢ φ := by
    sorry

end Conservativity
