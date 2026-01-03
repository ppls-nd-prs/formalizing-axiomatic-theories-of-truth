import FormalizingAxiomaticTheoriesOfTruth.Syntax
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Semantics

open FirstOrder
open Language
open Languages L_T

-- def term_encoding_1 {α n} : ℒₜ.BoundedFormula α n → (ℒₜ.Term (Empty ⊕ Fin 0)) := numeral ∘ Encodable.encode
-- def term_encoding_2 {α n} : ℒₜ.Term (α ⊕ Fin n) → (ℒₜ.Term (Empty ⊕ Fin 0)) := numeral ∘ Encodable.encode


-- namespace SyntaxAxioms
-- open Languages L_T LPA BoundedFormula

-- variable {L : Language}[SyntaxTheoretical L][Arithmetical L][∀α n, Encodable (L.Term (α ⊕ Fin n))][∀α n, Encodable (L.BoundedFormula α n)]

-- variable {α : Type*}
-- def neg_repres (φ : Formula ℒₜ α) : L.Sentence :=
--   (⬝∼ ⌜φ⌝) =' (⌜∼φ⌝)
-- def conj_repres (φ ψ : Formula L α): L.Sentence :=
--   (⌜φ⌝ ⬝∧ ⌜ψ⌝) =' (⌜φ ⊔ ψ⌝)
-- def disj_repres (φ ψ : Formula L α) : L.Sentence :=
--   (⌜φ⌝ ⬝∨ ⌜ψ⌝) =' (⌜φ ⊓ ψ⌝)
-- def cond_repres (φ ψ : Formula L α) : L.Sentence :=
--   (⌜φ⌝ ⬝⟹ ⌜ψ⌝) =' (⌜φ ⟹ ψ⌝)
-- def forall_repres (φ : BoundedFormula L α 1) : L.Sentence :=
--   (⬝∀ ⌜φ⌝) =' (⌜∀'φ⌝)
-- def exists_repres (φ : BoundedFormula L α 1) : L.Sentence :=
--   (⬝∃ ⌜φ⌝) =' (⌜∃'φ⌝)
-- def subs_repres (φ : L.Term (α ⊕ Fin 0) → BoundedFormula L α 0) (fv : α) (t : Term L (α ⊕ Fin 0)) : L.Sentence :=
--   Subs(⌜φ (#fv)⌝, ⌜(@Term.var L (α ⊕ Fin 0) (.inl fv))⌝, ⌜t⌝) =' ⌜φ t⌝
-- def term_repres (φ : Formula L α) : L.Sentence :=
--   Trm( ⌜φ⌝ )
-- def formulaL_repres (φ : Formula L α) : L.Sentence :=
--   FormL( ⌜φ⌝ )
-- def formulaL_T_repres (φ : Formula L α) : L.Sentence :=
--   FormLT( ⌜φ⌝ )
-- def sentenceL_repres (φ : Formula L α) : L.Sentence :=
--   SentenceL( ⌜φ⌝ )
-- def sentenceL_T_respres (φ : Formula L α) : L.Sentence :=
--   SentenceLT( ⌜φ⌝ )
-- def closed_term_repres (t : L.Term (α ⊕ Fin 0)) : L.Sentence :=
--   ClosedTerm(⌜t⌝)
-- def var_repres (φ : Formula L α) : L.Sentence :=
--   Var( ⌜φ⌝ )
-- def const_repres (φ : Formula L α) : L.Sentence :=
--   Const( ⌜φ⌝ )
-- def denote_repres (t : L.Term (Empty ⊕ Fin 0)) : L.Sentence :=
--   ClosedTerm(⌜t⌝) ⟹ ((⬝°(⌜t⌝)) =' t)

-- end SyntaxAxioms

-- namespace SyntaxTheory
-- open Languages
-- open LPA
-- open SyntaxAxioms

-- variable {L : Language}[SyntaxTheoretical L][Arithmetical L][∀α n, Encodable (L.Term (α ⊕ Fin n))][∀α n, Encodable (L.BoundedFormula α n)]
-- inductive syntax_theory : L.Theory where
--   | negation_representation {φ} : syntax_theory (neg_repres φ)
--   | conjunction_representation {φ ψ} : syntax_theory (conj_repres φ ψ)
--   | disjunction_representation {φ ψ} : syntax_theory (disj_repres φ ψ)
--   | conditional_representation {φ ψ} : syntax_theory (cond_repres φ ψ)
--   | forall_representation {φ} : syntax_theory (forall_repres φ)
--   | exists_representation {φ} : syntax_theory (exists_repres φ)
--   | term_representation {φ} : syntax_theory (term_repres φ)
--   | formula_L_representation {φ} : syntax_theory (formulaL_repres φ)
--   | formula_L_T_representation {φ} : syntax_theory (formulaL_T_repres φ)
--   | sentence_L_representation {φ} : syntax_theory (sentenceL_repres φ)
--   | sentence_L_T_representation {φ} : syntax_theory (sentenceL_T_respres φ)
--   | closed_term_representation {φ} : syntax_theory (closed_term_repres φ)
--   | variable_representation {φ} : syntax_theory (var_repres φ)
--   | constant_representation {φ} : syntax_theory (const_repres φ)
--   | denote_representation {t} : syntax_theory (denote_repres t)

-- open L_T
-- end SyntaxTheory

namespace Induction
variable {L : Language}
[∀α n, Encodable (ℒₜ.Term (α ⊕ Fin n))][∀α n, Encodable (ℒₜ.BoundedFormula α n)]
notation "⌜"t"⌝" => numeral (Encodable.encode t)

open BoundedFormula

end Induction

namespace TB
  open Languages L_T Induction BoundedFormula

  instance : Coe (ℒₜ.BoundedFormula α (n + m)) (ℒₜ.BoundedFormula α (m + n)) where
  coe := by
    intro h
    rw[Nat.add_comm] at h
    exact h

  def ind {α n} (φ : {α : Type} → {n : Nat} → ℒₜ.Term (α ⊕ Fin n) → ℒₜ.BoundedFormula α n) : ℒₜ.BoundedFormula α n :=
  (φ null) ⊓ ∀'((φ (&0)) ⟹ (φ (S(&0)))) ⟹ ∀'(φ (&0))

end TB

-- namespace FirstOrder.Language.Term
-- @[simp]
-- def zero_subst {n} : ℒₜ.Term ((Fin 1) ⊕ Fin n) → ℒₜ.Term (Empty ⊕ Fin n)
-- | .var (.inl _) => null
-- | .var (.inr f) => .var (.inr f)
-- | .func f ts => .func f (fun i => (zero_subst (ts i)))

-- @[simp]
-- def bf_subst {n} : ℒₜ.Term ((Fin 1) ⊕ Fin n) → ℒₜ.Term (Empty ⊕ (Fin (n + 1)))
-- | .var (.inl _) => .var (.inr (.mk 0 (by simp)))
-- | .var (.inr f) => .var (.inr (f.addNat 1))
-- | .func f ts => .func f (fun i => (ts i).bf_subst)

-- @[simp]
-- def bf_succ_subst {n} : ℒₜ.Term ((Fin 1) ⊕ Fin n) → ℒₜ.Term (Empty ⊕ (Fin (n + 1)))
-- | .var (.inl _) => .func .succ_symbol ![.var (.inr (.mk 0 (by simp)))]
-- | .var (.inr f) => .var (.inr (f.addNat 1))
-- | .func f ts => .func f (fun i => (ts i).bf_subst)
-- end FirstOrder.Language.Term

-- namespace FirstOrder.Language.BoundedFormula
-- @[simp]
-- def zero_subst : {n : Nat} → (ℒₜ.BoundedFormula (Fin 1) n) → ℒₜ.BoundedFormula Empty n
--   | _, .falsum => .falsum
--   | _, .equal t₁ t₂ => .equal t₁.zero_subst t₂.zero_subst
--   | _, .rel R ts => .rel R (fun i => (ts i).zero_subst)
--   | _, .imp f₁ f₂ => .imp f₁.zero_subst f₂.zero_subst
--   | _, .all f₁ => .all f₁.zero_subst

-- @[simp]
-- def bf_subst : {n : Nat} → (ℒₜ.BoundedFormula (Fin 1) n) → ℒₜ.BoundedFormula Empty (n + 1)
-- | _, .falsum => .falsum
-- | _, .equal t₁ t₂ => .equal t₁.bf_subst t₂.bf_subst
-- | _, .rel R ts => .rel R (fun i => (ts i).bf_subst)
-- | _, .imp f₁ f₂ => .imp f₁.bf_subst f₂.bf_subst
-- | _, .all f₁ => .all f₁.bf_subst

-- @[simp]
-- def bf_succ_subst : {n : Nat} → (ℒₜ.BoundedFormula (Fin 1) n) → ℒₜ.BoundedFormula Empty (n + 1)
-- | _, .falsum => .falsum
-- | _, .equal t₁ t₂ => .equal t₁.bf_succ_subst t₂.bf_succ_subst
-- | _, .rel R ts => .rel R (fun i => (ts i).bf_succ_subst)
-- | _, .imp f₁ f₂ => .imp f₁.bf_succ_subst f₂.bf_succ_subst
-- | _, .all f₁ => .all f₁.bf_succ_subst
-- end FirstOrder.Language.BoundedFormula

namespace TB
  -- def ind₂ {n : Nat} (φ : ℒₜ.BoundedFormula (Fin 1) n) : ℒₜ.BoundedFormula Empty n :=
  --   (φ.zero_subst ⊓ ∀'(φ.bf_subst ⟹ φ.bf_succ_subst)) ⟹ ∀'φ.bf_subst

  variable [∀n,∀α, Encodable (ℒₜ.BoundedFormula α n)]
  def tarski_biconditional {α} {n} (ψ : ℒₜ.BoundedFormula α n) (_ : ¬ contains_T ψ) : ℒₜ.BoundedFormula α n := .rel L_T.Rel.t_symbol ![⌜ψ⌝] ⇔ ψ
  inductive tb {α n} : Set (ℒₜ.BoundedFormula α n) where
    | first : tb (∀' ∼(null =' S(&0)))
    | second :tb (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
    | third : tb (∀' ((&0 add null) =' &0))
    | fourth : tb (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
    | fifth : tb (∀' ((&0 mult null) =' null))
    | sixth : tb (∀' ∀' ((&1 mult S(&0)) =' ((&1 mult &0)) add &1))
    | induction (ψ : {α : Type} → {n : Nat} → ℒₜ.Term (α ⊕ Fin n) → ℒₜ.BoundedFormula α n) : tb (ind ψ)
    | bicon (φ : ℒₜ.BoundedFormula α n) (h : ¬ contains_T φ) : tb (tarski_biconditional φ h)

    notation "𝐓𝐁" => tb
end TB

namespace PA
  open TB Languages L_T
  variable [∀n,∀α, Encodable (ℒₜ.BoundedFormula α n)]
  def pa : ℒₜ.Theory := {φ | φ ∈ tb ∧ ¬contains_T φ}

  notation "𝐏𝐀" => pa

  open Theory BoundedFormula

  lemma all_nums : ∀n m : Nat, n ≠ m → 𝐏𝐀 ⊨ᵇ (∼(numeral (n) =' (numeral m)) : ℒₜ.Sentence) := by
    intro n m h₁
    match n, m with
    | .zero, .zero =>
      simp at h₁
    | .zero, .succ n₁ =>
      apply models_sentence_iff.mpr
      intro M
      apply realize_not.mpr
      simp

      -- unfold PA.pa at M
      -- unfold TB.tb at M
      -- unfold PAT.pat at M


      have first : ↑M ⊨ ((∀' ∼(null =' S(&0))) : ℒₜ.Sentence) := by
        apply models_sentence_of_mem
        unfold PA.pa
        simp
        apply And.intro
        apply TB.tb.first
        simp[Term.bdEqual]
        -- apply Theory.models_sentence_of_mem
        -- simp
        -- apply And.intro
        -- apply Or.intro_left
        -- apply Or.intro_left
        -- apply peano_axioms.first
        -- intro h
        -- simp only [Term.bdEqual,contains_T] at h

      apply realize_all.mp at first
      have step := first (Term.realize (Sum.elim default default : (Empty ⊕ Fin 0 → ↑M)) (numeral n₁ : ℒₜ.Term (Empty ⊕ Fin 0)))
      simp[Fin.snoc,Matrix.empty_eq] at step
      simp[Matrix.empty_eq]
      exact step

    | .succ n₁, .zero =>
      apply models_sentence_iff.mpr
      intro M
      apply realize_not.mpr
      simp

      have first : ↑M ⊨ ((∀' ∼(null =' S(&0))) : ℒₜ.Sentence) := by
        apply models_sentence_of_mem
        unfold PA.pa
        simp
        apply And.intro
        apply TB.tb.first
        simp[Term.bdEqual]

      apply realize_all.mp at first
      have step := first (Term.realize (Sum.elim default default : (Empty ⊕ Fin 0 → ↑M)) (numeral n₁ : ℒₜ.Term (Empty ⊕ Fin 0)))
      simp[Fin.snoc,Matrix.empty_eq] at step
      simp[Matrix.empty_eq]
      intro h₂
      exact step h₂.symm

    | .succ n₁, .succ n₂ =>
      have step1 : n₁ ≠ n₂ := by
        revert h₁
        simp
      apply models_sentence_iff.mpr
      intro M
      have second : ↑M ⊨ ((∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0))): ℒₜ.Sentence) := by
        apply models_sentence_of_mem
        unfold PA.pa
        apply And.intro
        apply TB.tb.second
        simp[Term.bdEqual]

      apply realize_not.mpr
      simp[(realize_bdEqual _ _),Matrix.empty_eq]
      have step2 : ↑M ⊨ (∼(numeral n₁ =' numeral n₂) : ℒₜ.Sentence) := by
        apply all_nums n₁ n₂ step1
      apply realize_all.mp at second
      have second_a₁ := second (Term.realize (Sum.elim default ![]) (numeral n₂ : ℒₜ.Term (Empty ⊕ Fin 0)))
      apply realize_all.mp at second_a₁
      have second_a₁a₂ := second_a₁ (Term.realize (Sum.elim default ![]) (numeral n₁ : ℒₜ.Term (Empty ⊕ Fin 0)))
      simp[Fin.snoc] at second_a₁a₂
      intro h₂
      apply second_a₁a₂ at h₂
      apply realize_not.mp at step2
      simp[realize_bdEqual _ _,Matrix.empty_eq] at step2
      contradiction


  lemma all_fs : ∀φ₁ φ₂ : ℒₜ.Sentence, φ₁ ≠ φ₂ → 𝐏𝐀 ⊨ᵇ (∼(⌜φ₁⌝ =' ⌜φ₂⌝): ℒₜ.Sentence) := by
    intro φ₁ φ₂ h₁
    apply models_sentence_iff.mpr
    intro M
    apply realize_not.mpr
    intro h₂
    apply (realize_bdEqual _ _).mp at h₂

    have step1 : ↑M ⊨ (∼((numeral (Encodable.encode φ₁)) =' (numeral (Encodable.encode φ₂))): ℒₜ.Sentence) := by
      apply all_nums (Encodable.encode φ₁) (Encodable.encode φ₂)
      simp[h₁,Encodable.encode_inj]

    apply realize_not.mp at step1
    simp[realize_bdEqual _ _] at step1
    contradiction

end PA

-- namespace PA
--   open Languages LPA L_T BoundedFormula SyntaxTheory Induction
--   variable {L : Language}[Arithmetical L]
--   /-- Peano arithemtic -/
--   inductive tb : ℒₜ.Theory where
--     | first : tb (∀' ∼(null =' S(&0)))
--     | second :tb (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
--     | third : tb (∀' ((&0 add null) =' &0))
--     | fourth : tb (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
--     | fifth : tb (∀' ((&0 mult null) =' null))
--     | sixth : tb (∀' ∀' ((&1 mult S(&0)) =' ((&1 mult &0)) add &1))
--     | induction (ψ : L.Formula (Fin 1)) : tb (ind ψ)



--   open Theory BoundedFormula
-- end PA

-- namespace PAT
-- open Languages PA L_T SyntaxTheory BoundedFormula Induction

-- def pat : ℒₜ.Theory := tb ∪ {φ | ∃ψ, φ = ind ψ}
-- notation "𝐏𝐀𝐓" => pat

-- end PAT

-- namespace TB
-- open Languages L_T LPA PAT SyntaxTheory

-- variable [Encodable (ℒ.Sentence)]
-- def tarski_biconditional (ψ : ℒ.Sentence) : ℒₜ.Sentence := .rel L_T.Rel.t_symbol ![⌜ψ⌝] ⇔ ψ
-- def tb : ℒₜ.Theory := 𝐏𝐀𝐓 ∪ {φ | ∃ψ : ℒ.Sentence, φ = (tarski_biconditional ψ)}

-- def alt_PA : ℒₜ.Theory := {φ | φ ∈ tb ∧ ¬contains_T φ}

-- notation "𝐓𝐁" => tb
-- notation "𝐏𝐀" => alt_PA

open Theory BoundedFormula PA Languages L_T
  variable [∀n,∀α, Encodable (ℒₜ.BoundedFormula α n)]
  lemma eq_symm : ∀{t₁ t₂ : ℒₜ.Term (Empty ⊕ Fin 0)}, 𝐏𝐀 ⊨ᵇ (t₁ =' t₂) ↔ 𝐏𝐀 ⊨ᵇ (t₂ =' t₁) := by
    intro t₁ t₂
    apply Iff.intro
    --mp
    simp[models_sentence_iff]
    intro h₁
    intro M
    apply (realize_bdEqual _ _).mpr
    symm
    apply h₁ at M
    exact (realize_bdEqual _ _).mp M
    --mpr
    simp[models_sentence_iff]
    intro h₁
    intro M
    apply (realize_bdEqual _ _).mpr
    symm
    apply h₁ at M
    exact (realize_bdEqual _ _).mp M


  variable [Encodable ℒₜ.Sentence]

  lemma PA.succ_ne_zero : ∀{t : ℒₜ.Term (Empty ⊕ Fin 0)}, 𝐏𝐀 ⊨ᵇ ∼(S(t) =' null : ℒₜ.Sentence) := by
    intro t
    have pa_first : 𝐏𝐀 ⊨ᵇ ((∀' ∼(null =' S(&0))) : ℒₜ.Sentence) := by
      apply models_sentence_of_mem
      unfold PA.pa
      apply And.intro
      apply TB.tb.first
      simp[Term.bdEqual]

    match t with
    | .var (.inl v) => contradiction
    | .var (.inr (.mk val isLt)) => contradiction
    | .func f ts =>
      apply models_sentence_iff.mpr
      intro M
      apply realize_not.mpr
      simp [Matrix.empty_eq]
      apply models_sentence_iff.mp at pa_first
      have realization := pa_first M
      apply realize_all.mp at realization
      simp [Matrix.empty_eq,Fin.snoc] at M
      have ex : ∃a : ↑M, (Structure.funMap f fun i ↦ Term.realize (Sum.elim default ![]) (ts i)) = a := by
        simp
      have a_realization := realization ex.choose
      simp [Matrix.empty_eq,Fin.snoc] at a_realization
      intro h₂
      apply a_realization
      exact h₂.symm

  lemma merp : ∀{t : ℒₜ.Term (Empty ⊕ Fin 0)}, 𝐏𝐀 ⊨ᵇ ∼(null =' S(t) : ℒₜ.Sentence) := by
    intro t
    apply PA.succ_ne_zero at t
    #check (eq_symm).mp
    sorry
