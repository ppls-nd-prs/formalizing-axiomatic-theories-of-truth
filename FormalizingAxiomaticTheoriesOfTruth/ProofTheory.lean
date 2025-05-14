import FormalizingAxiomaticTheoriesOfTruth.Syntax

open FirstOrder
open Language
open Languages

namespace Calculus
  open BoundedFormula
  variable {L : Language}{n : ℕ}{α : Type}
  /- Some notation -/
  notation f " ↑' " n " at "  m => liftAt n m f
  notation f "↑" n => f ↑' n at 0

  /-- Shifts all variable references one down so one is pushed into
  the to-be-bound category -/
  def shift_one_down : ℕ → ℕ ⊕ Fin 1
    | .zero => .inr Nat.zero
    | .succ n => .inl n

  /-- Shifts all free variables (that are not to be bound) up by one-/
  def shift_free_up : ℕ → ℕ ⊕ Fin n
    | .zero => .inl (.succ .zero)
    | .succ k => .inl (.succ (k + 1))

  /-- Proof that addition is also transitive in BoundedFormula types -/
  def m_add_eq_add_m {m} : BoundedFormula L ℕ (m + n) → BoundedFormula L ℕ (n + m) := by
    rw[add_comm]
    intro h
    exact h
  instance {m} : Coe (BoundedFormula L ℕ (m + n)) (BoundedFormula L ℕ (n + m)) where
    coe := m_add_eq_add_m

  /-- Proof that adding zero als does nothing in BoundedFormula types -/
  def add_zero_does_nothing : BoundedFormula L ℕ (0 + n) → BoundedFormula L ℕ n := by
    intro h
    rw[zero_add] at h
    exact h
  instance : Coe (BoundedFormula L ℕ (0 + n)) (BoundedFormula L ℕ n) where
    coe := add_zero_does_nothing
  instance : Coe (BoundedFormula L ℕ (n + 0)) (BoundedFormula L ℕ (0 + n)) where
    coe := m_add_eq_add_m

  def sent_term_to_formula_term : Term L (Empty ⊕ Fin n) → Term L (ℕ ⊕ Fin n)
      | .var n => match n with
        | .inl _ => .var (.inl Nat.zero)
        | .inr k => .var (.inr k)
      | .func f ts => .func f (fun i => sent_term_to_formula_term (ts i))
  instance : Coe (Term L (Empty ⊕ Fin n)) (Term L (ℕ ⊕ Fin n)) where
    coe := sent_term_to_formula_term
  def bf_empty_to_bf_N : ∀{n}, BoundedFormula L Empty n → BoundedFormula L ℕ n
      | _, .falsum => .falsum
      | _, .equal t₁ t₂ => .equal t₁ t₂
      | _, .rel R ts => .rel R (fun i => ts i)
      | _, .imp f₁ f₂ => .imp (bf_empty_to_bf_N f₁) (bf_empty_to_bf_N f₂)
      | _, .all f => .all (bf_empty_to_bf_N f)
  instance : Coe (Sentence L) (Formula L ℕ) where
    coe := bf_empty_to_bf_N
  def th_to_set_form : Theory L → (Set (Formula L ℕ)) :=
    fun Th : Theory L => bf_empty_to_bf_N '' Th
  instance : Coe (Theory L) (Set (Formula L ℕ)) where
    coe := th_to_set_form

  variable [∀ n, DecidableEq (L.Functions n)][∀p, DecidableEq (L.Relations p)][∀m, DecidableEq (α ⊕ Fin m)]
  /-- Source for parts : https://github.com/FormalizedFormalLogic/Foundation/blob/94d18217bf9b11d3a0b1944424b1e028e50710a3/Foundation/FirstOrder/Basic/Syntax/Formula.lean -/
  def hasDecEq : {n : ℕ} → (f₁ f₂ : BoundedFormula L α n) → Decidable (f₁ = f₂)
    | _, .falsum, f => by
      cases f <;> try { simp; exact isFalse not_false }
      case falsum => apply Decidable.isTrue rfl
    | _, .equal t₁ t₂, .equal t₃ t₄ => decidable_of_iff (t₁ = t₃ ∧ t₂ = t₄) <| by simp
    | _, .equal _ _, .falsum | _, .equal t₁ t₂, .rel _ _ | _, .equal _ _, .imp _ _ | _, .equal _ _, .all _ => .isFalse <| by simp
    | _, @BoundedFormula.rel _ _ _ m f xs, @BoundedFormula.rel _ _ _ n g ys =>
        if h : m = n then
          decidable_of_iff (f = h ▸ g ∧ ∀ i : Fin m, xs i = ys (Fin.cast h i)) <| by
            subst h
            simp [funext_iff]
        else
          .isFalse <| by simp [h]
    | _, .rel _ _, .falsum | _, .rel _ _, .equal _ _ | _, .rel _ _, .imp _ _ | _, .rel _ _, .all _ => .isFalse <| by simp
    | _, .all f₁, f => by
      cases f <;> try { simp; exact isFalse not_false }
      case all f' => simp; exact hasDecEq f₁ f'
    | _, .imp f₁ f₂, f => by
      cases f <;> try { simp; exact isFalse not_false }
      case imp f₁' f₂' =>
        exact match hasDecEq f₁ f₁' with
        | isTrue hp =>
          match hasDecEq f₂ f₂' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])

  instance : DecidableEq (L.BoundedFormula α n) := hasDecEq
  instance : DecidableEq (L.Formula ℕ) := hasDecEq

  def shift_finset_up (Δ : Finset (L.BoundedFormula ℕ n)) : Finset (L.BoundedFormula ℕ (0 + n)) :=
    Finset.image (@relabel L ℕ ℕ 0 shift_free_up n) Δ
  instance : Coe (Finset (L.BoundedFormula ℕ (0 + n))) (Finset (L.BoundedFormula ℕ (n))) where
    coe := by
      rw[Nat.zero_add]
      intro h
      exact h


  notation Δ"↑"  => shift_finset_up Δ
  notation A"↓" => relabel shift_one_down A

  variable [BEq (Formula L ℕ)][DecidableEq (Formula L ℕ)]

  example : ∀φ : L.BoundedFormula ℕ n, φ = φ := by
    intro φ
    induction φ with
    | falsum =>
      rfl
    | equal _ _ =>
      rfl
    | rel _ _ =>
      rfl
    | imp _ _ ih₁ ih₂ =>
      rfl
    | all _ ih =>
      rfl

  /-- G3c sequent calculus -/
  inductive Derivation : (Set (BoundedFormula L ℕ n)) → (Finset (BoundedFormula L ℕ n)) → (Finset (BoundedFormula L ℕ n)) → Type _ where
    | tax {Th Γ Δ} (h : ∃f : BoundedFormula L ℕ n, f ∈ Th ∧ f ∈ Δ) : Derivation Th Γ Δ
    | tlax {Th Γ Δ} (h : ∃f, f ∈ Th ∧ f ∈ Γ ∧ f ∈ Δ) : Derivation Th Γ Δ
    | left_conjunction (A B S) {Th Γ Δ} (h₁ : Derivation Th S Δ) (h₂ : A ∈ S) (h₃ : B ∈ S) (h₄ : Γ = (((S \ {A}) \ {B}) ∪ {A ∧' B})): Derivation Th Γ Δ
    | left_disjunction (A B S₁ S₂ S₃) {Th Γ Δ} (h₁ : Derivation Th S₁ Δ) (h₂ : S₁ = S₃ ∪ {A}) (h₃ : Derivation Th S₂ Δ) (h₄ : S₂ = S₃ ∪ {B}) (h₅ : Γ = S₃ ∪ {A ∨' B}) : Derivation Th Γ Δ
    | left_implication (A B S₁ S₂ S₃) {Th Γ Δ} (d₁ : Derivation Th S₁ S₂) (h₁ : S₂ = Δ ∪ {A}) (d₂ : Derivation Th S₃ Δ) (h₂ : S₃ = {B} ∪ S₁) (h₃ : Γ = S₁ ∪ {A ⟹ B}): Derivation Th Γ Δ
    | left_bot {Th Γ Δ} (h : ⊥ ∈ Γ) : Derivation Th Γ Δ
    | right_conjunction {Th Γ Δ} (A B S₁ S₂ S₃) (d₁ : Derivation Th Γ S₁) (h₁ : S₁ = S₃ ∪ {A}) (d₂ : Derivation Th Γ S₂) (h₂ : S₂ = S₃ ∪ {B}) (h₃ : Δ = S₃ ∪ {A ∧' B}) : Derivation Th Γ Δ
    | right_disjunction {Th Γ Δ} (A B S) (h₁ : A ∈ S) (h₂ : B ∈ S) (d₁ : Derivation Th Γ S) (h₃ : Δ = (S \ {A, B}) ∪ {A ∨' B}): Derivation Th Γ Δ
    | right_implication {Th Γ Δ} (A B S₁ S₂ S₃) (d₁ : Derivation Th S₁ S₂) (h₁ : S₁ = {A} ∪ Γ) (h₂ : S₂ = S₃ ∪ {B}) (h₃ : Δ = S₃ ∪ {A ⟹ B}): Derivation Th Γ Δ
    | left_forall {Th Γ Δ}  (A : BoundedFormula L ℕ n) (B) (h₁ : B = A↓) (t S) (d : Derivation Th S Δ) (h₂ : (A/[t]) ∈ S ∧ (∀'B) ∈ S) (h₃ : Γ = S \ {(A/[t])}) : Derivation Th Γ Δ
    | left_exists {Th Γ} {Δ : Finset (BoundedFormula L ℕ n)} (A B) (S₁ : Finset (BoundedFormula L ℕ n)) (p : B = A↓) (d₁ : Derivation Th ((S₁↑) ∪ {A}) (Δ↑)) (h₁ : Γ = S₁ ∪ {∃' B}) : Derivation Th Γ Δ
    | right_forall {Th Γ Δ} (A B S) (p : B = A↓) (d₁ : Derivation Th (Γ↑) ((S↑) ∪ {A})) (h₁ : Δ = S ∪ {∀'B}) : Derivation Th Γ Δ
    | right_exists {Th Γ Δ} (A : BoundedFormula L ℕ n) (B t S) (p : B = A↓) (d₁ : Derivation Th Γ (S ∪ {∃'B, A/[t]})) (h₁ : Δ = S ∪ {∃'B}) : Derivation Th Γ Δ
    | cut {Th Γ Δ} (A S₁ S₂ S₃ S₄) (d₁ : Derivation Th S₁ (S₂ ∪ {A})) (d₂ : Derivation Th ({A} ∪ S₃) S₄) (h₁ : Γ = S₁ ∪ S₃) (h₂ : Δ = S₂ ∪ S₄) : Derivation Th Γ Δ

  @[simp]
  def emptyFormList : Finset (BoundedFormula L ℕ n) := ∅
  def sequent_provable (Th : Set (BoundedFormula L ℕ n)) (Γ Δ : Finset (BoundedFormula L ℕ n)) : Prop :=
    Nonempty (Derivation Th Γ Δ)
  notation Th " ⊢ " Γ Δ => sequent_provable Th Γ Δ
  def formula_provable (Th : Set (BoundedFormula L ℕ n)) (f : BoundedFormula L ℕ n) : Prop :=
    sequent_provable Th emptyFormList {f}
  notation Th " ⊢ " f => formula_provable Th f

  -- open Set
  -- variable {Th : Set (L.Formula ℕ)} {f₁ f₂ : (L.Formula ℕ)}
  -- lemma dinges : (Th ⊢ (f₁ ∨' f₂)) ↔ ((Th ⊢ f₁) ∨ (Th ⊢ f₂)) := by
  --   simp[formula_provable,sequent_provable]

  --   apply Iff.intro
  --   intro hₐ

  -- #check f₃ f₄

  --   apply Classical.choice at hₐ
  --   cases hₐ with
  --   | right_disjunction A B S h₁ h₂ d₁ h₃ =>

  --     have step1 : S = {f₁,f₂} := by

  --       sorry




  --     sorry
  --   | left_conjunction A B S h₁ h₂ h₃ h₄ =>
  --     have step1 : ((S \ {A}) \ {B} ∪ {A∧'B}) ≠ ∅ := by
  --       simp
  --     symm at h₄
  --     apply step1 at h₄
  --     apply False.elim h₄

  --   | left_disjunction A B S₁ S₂ S₃ h₁ h₂ h₃ h₄ h₅ =>
  --     have step1 : S₃ ∪ {A∨'B} ≠ ∅ := by
  --       simp
  --     symm at h₅
  --     apply step1 at h₅
  --     apply False.elim h₅

  --   | left_implication A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ =>
  --     have step1 : S₁ ∪ {A ⟹ B} ≠ ∅ := by
  --       simp
  --     symm at h₃
  --     apply step1 at h₃
  --     apply False.elim h₃

  --   | left_bot h =>
  --     simp at h

  --   | right_conjunction A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ =>
  --     have step1 : (A∧'B) ∈ (S₃ ∪ {A∧'B}) := by
  --       simp
  --     let S₄ : Finset (L.Formula ℕ) := {f₁∨'f₂}
  --     have step2 : ∼(A ⟹ ∼B) ≠ ∼f₁ ⟹ f₂ := by
  --       simp[BoundedFormula.not]
  --     have step3 : (A∧'B) ∉ S₄ := by
  --       intro h₄
  --       simp[S₄] at h₄
  --       simp[BoundedFormula.lor,BoundedFormula.land] at h₄
  --       apply step2 at h₄
  --       apply False.elim h₄
  --     have step4 : ¬((S₃ ∪ {A∧'B}) ⊆ {f₁∨'f₂}) := by
  --       apply Finset.not_subset.mpr
  --       apply Exists.intro (A∧'B)
  --       apply And.intro
  --       exact step1
  --       simp
  --       exact step2
  --     have step5 : ¬(((S₃ ∪ {A∧'B}) ⊆ {f₁∨'f₂}) ∧ ({f₁∨'f₂} ⊆ (S₃ ∪ {A∧'B}))) := by
  --       simp[step4]
  --     have step6 : S₃ ∪ {A∧'B} ≠ {f₁∨'f₂} := by
  --       intro h₄
  --       apply Finset.Subset.antisymm_iff.mp at h₄
  --       apply step5 at h₄
  --       apply False.elim h₄
  --     symm at h₃
  --     apply step6 at h₃
  --     apply False.elim h₃

  --   | _ =>
  --     sorry

end Calculus
