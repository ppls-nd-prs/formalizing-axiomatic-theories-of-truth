import FormalizingAxiomaticTheoriesOfTruth.Syntax
import Mathlib.ModelTheory.Complexity
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Tree.Get
import Mathlib.Data.Set.Basic

namespace FirstOrder.Language
variable {α β: Type} {L : Language} {n : Nat}

open Sentence

abbrev Fml := L.BoundedFormula α n ⊕ L.BoundedFormula β n
structure ProofSystem : Type where
  unary : Set (Fml (L := L) (α := α) (β := β) (n := n) → Fml (L := L) (α := α) (β := β) (n := n))
  binary : Set (Fml (L := L) (α := α) (β := β) (n := n) → Fml (L := L) (α := α) (β := β) (n := n) → Fml (L := L) (α := α) (β := β) (n := n))

-- @[simp]
-- def Term.to_alpha : L.Term (Empty ⊕ Fin n) → L.Term (α ⊕ Fin n)
-- | .var (.inl v) => by contradiction
-- | .var (.inr v) => .var (.inr v)
-- | .func f ts => .func f (fun i => .to_alpha (ts i))

-- @[simp]
-- def BoundedFormula.to_alpha : {n : Nat} → L.BoundedFormula Empty n → L.BoundedFormula α n
-- | _, .falsum => .falsum
-- | _, .equal t₁ t₂ => .equal t₁.to_alpha t₂.to_alpha
-- | _, .rel r ts => .rel r (fun i => (ts i).to_alpha)
-- | _, .imp φ₁ φ₂ => .imp φ₁.to_alpha φ₂.to_alpha
-- | _, .all φ => .all φ.to_alpha

open BoundedFormula
inductive Proof : (Th : Set (L.BoundedFormula α n)) → (s : ProofSystem) → Fml (L := L) (α := α) (β := β) → Type _
| ax {Th s} (φ : L.BoundedFormula α n) (h : φ ∈ Th) : Proof Th s (.inl φ)
| un {Th s ψ φ} {r : Fml → Fml} (p : Proof Th s ψ) (h₁ : r ∈ s.unary) (h₂ : r ψ = φ) : Proof Th s φ
| bi {Th s ψ₁ ψ₂ φ} {r : Fml → Fml → Fml} (p₁ : Proof Th s ψ₁) (p₂ : Proof Th s ψ₂) (h₁ : r ∈ s.binary) (h₂ : r ψ₁ ψ₂ = φ) : Proof Th s φ

-- variable {L : Language}{α : Type}{n : Nat}{s : @ProofSystem L α n}{Th : Set (L.BoundedFormula α n)}
-- def Proof.nr_axioms {φ : L.BoundedFormula α n} : Proof Th s φ → Nat
-- | .ax _ _ => 1
-- | .un p _ _ => p.nr_axioms
-- | .bi p₁ p₂ _ _ => p₁.nr_axioms + p₂.nr_axioms

namespace ProofSystem
variable {α : Type}
def Provable (Th : Set (L.BoundedFormula α n)) (s : @ProofSystem α β L n) (φ : @Fml α β L n) : Prop :=
  Nonempty (Proof Th s φ)
notation Th " ⊢("s") " φ => Provable Th s φ

def Sound (s : @ProofSystem Empty β L 0) : Prop :=
  ∀φ : L.Sentence,∀ψ : L.Formula β, ∀Th, ((Th ⊢(s) .inl φ) → (Th ⊨ᵇ φ)) ∧ ((Th ⊢(s) .inr ψ) → (Th ⊨ᵇ ψ))
def Complete (s : @ProofSystem Empty β L 0) : Prop :=
  ∀φ : L.Sentence, ∀ψ : L.Formula β, ∀Th, ((Th ⊨ᵇ φ) → ((Th) ⊢(s) .inl φ)) ∧ ((Th ⊨ᵇ ψ) → (Th ⊢(s) .inr ψ))

open Theory BoundedFormula

-- lemma sound_system_taut_axiom : ∀s : @ProofSystem L α 0, s.Sound → (∀φ ∈ s.la, {} ⊨ᵇ φ) := by
--   intro s
--   contrapose
--   intro h₁
--   simp at h₁
--   let φ : L.Formula α := h₁.choose
--   unfold Sound
--   simp
--   apply Exists.intro φ
--   apply Exists.intro {}
--   apply And.intro
--   -- left
--   apply Nonempty.intro
--   apply Proof.ax
--   apply Or.intro_left
--   apply h₁.choose_spec.left
--   -- right
--   apply h₁.choose_spec.right

-- lemma sound_system_sound_un : ∀Th : L.Theory, ∀s : @ProofSystem L α 0, s.Sound → (∀r ∈ s.unary,∀φ ψ, ((to_alpha '' Th) ⊢(s) φ) → r φ = ψ → Th ⊨ᵇ ψ) := by
--   intro Th s
--   contrapose
--   intro h₁
--   simp at h₁
--   let r : L.Formula α → L.Formula α := h₁.choose
--   let φ : L.Formula α := h₁.choose_spec.right.choose
--   have provable_φ : (to_alpha '' Th) ⊢(s) φ := by
--     apply h₁.choose_spec.right.choose_spec.left
--   unfold Provable at provable_φ
--   apply Classical.ofNonempty at provable_φ
--   have r_in_unary : r ∈ s.unary := by
--     apply h₁.choose_spec.left
--   have provable : (to_alpha '' Th) ⊢(s) r φ := by
--     unfold Provable
--     apply Nonempty.intro
--     apply Proof.un
--     apply provable_φ
--     apply r_in_unary
--     rfl
--   unfold Sound
--   simp
--   apply Exists.intro (r φ)
--   apply Exists.intro Th
--   apply And.intro
--   -- left
--   exact provable
--   -- right
--   apply h₁.choose_spec.right.choose_spec.right

-- lemma sound_system_sound_bi : ∀Th : L.Theory, ∀s : @ProofSystem L α 0, s.Sound → (∀r ∈ s.binary,∀φ₁ φ₂ ψ, ((to_alpha '' Th) ⊢(s) φ₁) → ((to_alpha '' Th) ⊢(s) φ₂) → r φ₁ φ₂ = ψ → Th ⊨ᵇ ψ) := by
--   intro Th s
--   contrapose
--   intro h₁
--   simp at h₁
--   unfold Sound
--   simp
--   let r : L.Formula α → L.Formula α → L.Formula α := h₁.choose
--   #check h₁.choose_spec.right.choose
--   let φ₁ : L.Formula α := h₁.choose_spec.right.choose
--   #check h₁.choose_spec.right.choose_spec.right.choose
--   let φ₂ : L.Formula α := h₁.choose_spec.right.choose_spec.right.choose
--   apply Exists.intro
--   apply Exists.intro
--   apply And.intro
--   -- left
--   have φ₁_provable : (to_alpha '' Th) ⊢(s) φ₁ := by
--     apply h₁.choose_spec.right.choose_spec.left
--   apply Classical.ofNonempty at φ₁_provable
--   have φ₂_provable : (to_alpha '' Th) ⊢(s) φ₂ := by
--     #check h₁.choose_spec.right.choose_spec.right.choose_spec.left
--     apply h₁.choose_spec.right.choose_spec.right.choose_spec.left
--   apply Classical.ofNonempty at φ₂_provable
--   have r_in_bi : r ∈ s.binary := by
--     #check h₁.choose_spec.left
--     apply h₁.choose_spec.left
--   have φ_φ_provable : (to_alpha '' Th) ⊢(s) r φ₁ φ₂ := by
--     unfold Provable
--     apply Nonempty.intro
--     apply Proof.bi
--     apply φ₁_provable
--     apply φ₂_provable
--     exact r_in_bi
--     rfl
--   exact φ_φ_provable
--   -- right
--   apply h₁.choose_spec.right.choose_spec.right.choose_spec.right

-- -- lemma complete_system_taut_ax : ∀s : @ProofSystem L α 0, s.Complete ∧ s.Sound → (∀φ, {} ⊨ᵇ φ → φ ∈ s.la) := by
-- --   intro s h₁ φ
-- --   unfold Complete at h₁
-- --   have step1 : ∅ ⊨ᵇ φ → (to_alpha '' ∅) ⊢(s) φ := by
-- --     exact h₁.left φ ∅
-- --   intro h₂
-- --   have proof : Proof (to_alpha '' ∅) s φ := by
-- --     apply step1 at h₂
-- --     exact Classical.choice h₂
-- --   induction proof with
-- --   | ax φ₁ h₃ =>
-- --     cases h₃ with
-- --     | inl h₃ =>
-- --       exact h₃
-- --     | inr h₃ =>
-- --       simp at h₃
-- --   | @un ψ φ r p h₃ h₄ p_ih =>
-- --     have step2 := sound_system_sound_un ∅ _ h₁.right
-- --     have step3 := step2 r h₃ ψ φ
-- --     apply Nonempty.intro at p
-- --     apply step3 at p
-- --     apply p at h₄
-- --     apply h₁.left φ at h₄
-- --     apply Classical.choice at h₄
-- --     cases h₄ with
-- --     | ax φ₁ h =>
-- --       cases h with
-- --       | inl h =>
-- --         exact h
-- --       | inr h =>
-- --         simp at h
-- --     | un =>


-- --       sorry
-- --     | _ => sorry
-- --   | _ => sorry

end ProofSystem

end FirstOrder.Language

-- namespace Derivations
-- open Calculus
-- open BoundedFormula

-- variable {L : Language}
-- [∀ n, DecidableEq (L.Functions n)]
-- [∀ n, DecidableEq (L.Relations n)]
-- [DecidableEq (Formula L ℕ)]

-- def mp_derivation
--   (Th : L.Theory) (A B : Formula L ℕ) :
--   Derivation Th {A, A ⟹ B} {B} := by
--   have d₁ : Derivation Th {A} {B, A} := by
--     apply Derivation.lax
--     exact ⟨A, by simp⟩
--   have d₂ : Derivation Th {B, A} {B} := by
--     apply Derivation.lax
--     exact ⟨B, by simp⟩
--   apply Derivation.left_implication A B {A} {B, A} {B, A}
--   exact d₁
--   apply Finset.insert_eq
--   exact d₂
--   apply Finset.insert_eq
--   apply Finset.insert_eq

-- def disj_intro_left_derivation
--   (Th : L.Theory) (A B : Formula L ℕ) :
--   Derivation Th {A} {A ∨' B} := by
--   apply Derivation.right_disjunction A B {A, B} {} _ (by simp) (by simp)
--   exact Derivation.lax ⟨A, by simp⟩

-- def disj_intro_right_derivation
--   (Th : L.Theory) (A B : Formula L ℕ) :
--   Derivation Th {B} {A ∨' B} := by
--   apply Derivation.right_disjunction A B {A, B} {} _ (by simp) (by simp)
--   exact Derivation.lax ⟨B, by simp⟩

-- def conj_elim_left_derivation
--   (Th : L.Theory) (A B : Formula L ℕ) :
--   Derivation Th {A ∧' B} {A} := by
--   apply Derivation.left_conjunction A B {A, B} {}
--   apply Derivation.lax
--   simp
--   simp
--   simp

-- def conj_elim_right_derivation
--   (Th : L.Theory) (A B : Formula L ℕ) :
--   Derivation Th {A ∧' B} {B} := by
--   apply Derivation.left_conjunction A B {A, B} {}
--   apply Derivation.lax
--   simp
--   simp
--   simp

-- def double_neg_left_derivation
--   (Th: L.Theory) (A : Formula L ℕ) :
--   Derivation Th {∼∼A} {A} := by
--   apply Calculus.left_negation ∼A ∅ {A, ∼A}
--   apply Calculus.right_negation A {A} {A}
--   apply Derivation.lax
--   simp
--   rw [Finset.insert_eq]
--   rw [Finset.empty_union]


-- def double_neg_right_derivation
--   (Th: L.Theory) (A : Formula L ℕ) :
--   Derivation Th {A} {∼∼A} := by
--   apply Calculus.right_negation ∼A {A,∼A} ∅
--   apply Calculus.left_negation A {A} {A}
--   apply Derivation.lax
--   simp
--   rw [Finset.insert_eq]
--   rw [Finset.empty_union]

-- def demorganslaw_first_derivation
--   (Th : L.Theory) (A B : Formula L ℕ) :
--   Derivation Th {∼(A ∧' B)} {∼A ∨' ∼B} := by
--   apply Calculus.left_negation (A ∧'B) {} {A ∧'B, ∼A∨'∼B}
--   apply Derivation.right_disjunction ∼A ∼B {A ∧'B, ∼A, ∼B} {A ∧' B}
--   apply Calculus.right_negation A {A} {A ∧'B, ∼B}
--   apply Calculus.right_negation B {A, B} {A ∧'B}
--   apply Derivation.right_conjunction A B {A} {B} ∅
--   apply Derivation.lax
--   simp
--   rw [Finset.empty_union]
--   apply Derivation.lax
--   simp
--   rw [Finset.empty_union]
--   rw [Finset.empty_union]
--   rw [Finset.insert_eq]
--   rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--   rw [Finset.union_assoc]
--   rw [Finset.union_comm {∼A} {∼B}]
--   rw [Finset.insert_eq]
--   rw [Finset.insert_eq]
--   simp

-- def demorganslaw_second_derivation
--   (Th : L.Theory) (A B : Formula L ℕ) :
--   Derivation Th {∼(A ∨' B)} {∼A ∧' ∼B} := by
--   apply Calculus.left_negation (A ∨'B) ∅ {A ∨' B, ∼A ∧' ∼B}
--   apply Derivation.right_disjunction A B {∼A ∧' ∼B, A, B} {∼A ∧' ∼B}
--   apply Derivation.right_conjunction ∼A ∼B {A, B, ∼A} {A, B, ∼B} {A, B}
--   apply Calculus.right_negation A {A} {A, B}
--   apply Derivation.lax
--   simp
--   rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--   rw [Finset.union_assoc]
--   rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--   rw [Finset.union_assoc]
--   apply Calculus.right_negation B {B} {A, B}
--   apply Derivation.lax
--   simp
--   rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--   rw [Finset.union_assoc]
--   rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--   rw [Finset.union_assoc]
--   rw [Finset.insert_eq, Finset.insert_eq]
--   rw [Finset.union_comm]
--   rw [Finset.insert_eq]
--   rw [Finset.insert_eq]
--   rw [Finset.union_comm]
--   rw [Finset.empty_union]

-- def right_implication_derivation
--   (Th : L.Theory) (A B Γ : Formula L ℕ)
--   (d₁: Derivation Th {Γ, A} {B}) :
--   Derivation Th {Γ} {A ⟹ B} := by
--   apply Derivation.right_implication A B {Γ, A} {B} ∅
--   exact d₁
--   rw [Finset.insert_eq]
--   rw [Finset.union_comm]
--   rw [Finset.empty_union]
--   rw [Finset.empty_union]

-- def disj_elim_derivation
--   (Th : L.Theory) (A B C: Formula L ℕ)
--   (d₁ : Derivation Th {A} {C}) (d₂ : Derivation Th {B} {C}) :
--   Derivation Th {A ∨' B} {C} := by
--   apply Derivation.left_disjunction A B {A} {B} ∅
--   exact d₁
--   simp
--   exact d₂
--   simp
--   simp

-- lemma mp : ∀th : L.Theory, ∀(A B : L.Formula ℕ), Nonempty (Derivation th {A, A ⟹ B} {B}) := by
--   let mp_derivation
--     (Th : L.Theory) (A B : Formula L ℕ) :
--     Derivation Th {A, A ⟹ B} {B} := by
--     have d₁ : Derivation Th {A} {B, A} := by
--       apply Derivation.lax
--       exact ⟨A, by simp⟩
--     have d₂ : Derivation Th {B, A} {B} := by
--       apply Derivation.lax
--       exact ⟨B, by simp⟩
--     apply Derivation.left_implication A B {A} {B, A} {B, A}
--     exact d₁
--     apply Finset.insert_eq
--     exact d₂
--     apply Finset.insert_eq
--     apply Finset.insert_eq
--   intro th A B
--   apply mp_derivation at th
--   apply th at A
--   apply A at B
--   apply Nonempty.intro B

-- lemma conj_intro : ∀th : L.Theory, ∀(A B : L.Formula ℕ), Nonempty (Derivation th {A, B} {A ∧' B}) := by
--   let conj_intro_derivation
--     (Th :L.Theory) (A B : Formula L ℕ) :
--     Derivation Th {A, B} {A ∧' B} := by
--     apply Derivation.right_conjunction A B {A} {B} ∅
--     apply Derivation.lax ⟨A, by simp⟩
--     simp
--     apply Derivation.lax ⟨B, by simp⟩
--     simp
--     simp
--   intro th A B
--   apply conj_intro_derivation at th
--   apply th at A
--   apply A at B
--   apply Nonempty.intro B

-- lemma conj_elim : ∀th : L.Theory, ∀(A B : L.Formula ℕ), Nonempty (Derivation th {A ∧' B} {A, B}) := by
--   let conj_elim_derivation
--     (Th : L.Theory) (A B : Formula L ℕ) :
--     Derivation Th {A ∧' B} {A, B} := by
--     apply Derivation.left_conjunction A B {A, B} {}
--     apply Derivation.lax
--     simp
--     simp
--     simp
--   intro th A B
--   apply conj_elim_derivation at th
--   apply th at A
--   apply A at B
--   apply Nonempty.intro B

-- lemma excl_mid : ∀th : L.Theory, ∀(A : L.Formula ℕ), ∀(Δ : Finset (Formula L ℕ)), Nonempty (Derivation th Δ {A ∨'∼A}) := by
--   let excl_mid_derivation
--     (Th : L.Theory) (A : Formula L ℕ) (Δ : Finset (Formula L ℕ)) :
--     Derivation Th Δ {A ∨'∼A} := by
--     apply Derivation.right_disjunction A ∼A {A, ∼A} {}
--     apply Calculus.right_negation A (Δ ∪ {A}) {A}
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     simp
--     rfl
--   sorry

-- lemma eqv_trans : ∀Th : L.Theory, ∀(A B C : L.Formula ℕ), Nonempty (Derivation Th {A ⇔ B, C ⇔ B} {A ⇔ C}) := by
--   let eqv_trans_derivation
--     (Th : L.Theory) (A B C : Formula L ℕ) :
--     Derivation Th {A ⇔ B, C ⇔ B} {A ⇔ C} := by
--     dsimp [FirstOrder.Language.BoundedFormula.iff]
--     dsimp [instMin]
--     apply Derivation.right_conjunction (A ⟹ C) (C ⟹ A) {A ⟹ C} {C ⟹ A} ∅
--     apply Derivation.right_implication A C {A, (A ⟹ B) ⊓ (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {C} ∅
--     apply Derivation.left_conjunction (A ⟹ B) (B ⟹ A) {A, (A ⟹ B), (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {A, (C ⟹ B) ⊓ (B ⟹ C)}
--     apply Derivation.left_conjunction (C ⟹ B) (B ⟹ C) {A, (A ⟹ B), (B ⟹ A), (C ⟹ B), (B ⟹ C)} {A, A ⟹ B, B ⟹ A}
--     apply Calculus.cut B {A, (A ⟹ B)} ∅ {(B ⟹ A), (C ⟹ B), (B ⟹ C)} {C}
--     apply mp_derivation
--     rw [← Finset.insert_eq]
--     apply Derivation.left_implication B C {B, (B ⟹ A), (C ⟹ B)} {C, B} {C, B, (B ⟹ A), (C ⟹ B)}
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     rw [← Finset.union_assoc]
--     rw [Finset.empty_union]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     dsimp [instMin]
--     dsimp [land]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     rw [Finset.union_right_comm]
--     dsimp [instMin]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     rw [Finset.union_right_comm]
--     dsimp [instMin]
--     dsimp [land]
--     rw [← Finset.union_assoc]
--     rw [← Finset.insert_eq]
--     dsimp [instMin]
--     rw [Finset.empty_union]
--     rw [Finset.empty_union]
--     rw [Finset.empty_union]
--     apply Derivation.right_implication C A {C, (A ⟹ B) ⊓ (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {A} ∅
--     apply Derivation.left_conjunction (A ⟹ B) (B ⟹ A) {C, (A ⟹ B), (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {C, (C ⟹ B) ⊓ (B ⟹ C)}
--     apply Derivation.left_conjunction (C ⟹ B) (B ⟹ C) {C, (C ⟹ B), (A ⟹ B), (B ⟹ A),  (B ⟹ C)} {C, A ⟹ B, B ⟹ A}
--     apply Calculus.cut B {C, (C ⟹ B)} ∅ {(A ⟹ B), (B ⟹ A), (B ⟹ C)} {A}
--     apply mp_derivation
--     rw [← Finset.insert_eq]
--     apply Derivation.left_implication B A {B, (A ⟹ B), (B ⟹ C)} {A, B} {A, B, (A ⟹ B), (B ⟹ C)}
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [Finset.union_right_comm]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     rw [← Finset.union_assoc]
--     rw [Finset.empty_union]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     rw [← Finset.union_assoc]
--     rw [Finset.union_right_comm]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [Finset.union_right_comm]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     dsimp [instMin]
--     dsimp [land]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [Finset.union_comm]
--     rw [Finset.union_left_comm]
--     rw [Finset.union_comm]
--     rw [Finset.union_left_comm]
--     rw [← Finset.union_assoc]
--     rw [← Finset.union_assoc]
--     rw [Finset.union_right_comm]
--     rw [Finset.union_assoc]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     rw [← Finset.union_assoc]
--     rw [Finset.union_right_comm]
--     dsimp [instMin]
--     dsimp [land]
--     rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
--     dsimp [instMin]
--     simp
--     simp
--     simp
--     simp
--     dsimp [land]
--   intro Th A B C
--   apply eqv_trans_derivation at Th
--   apply Th at A
--   apply A at B
--   apply B at C
--   apply Nonempty.intro C

-- lemma inconsistency : ∀Th : L.Theory, ∀(A : L.Formula ℕ), Nonempty (Derivation Th {A ⇔ ∼A} {⊥}) := by
--   let inconsistency_derivation
--     (Th : L.Theory) (A : Formula L ℕ) :
--     Derivation Th {A ⇔ ∼A} {⊥} := by
--     dsimp [FirstOrder.Language.BoundedFormula.iff]
--     apply Derivation.left_conjunction (A ⟹ ∼A) (∼A ⟹ A) {(A ⟹ ∼A), (∼A ⟹ A)} {}
--     apply Derivation.left_implication ∼A A {(A ⟹ ∼A)} {⊥, ∼A} {A, (A ⟹ ∼A)}
--     apply Calculus.right_negation A {(A ⟹ ∼A), A} {⊥}
--     apply Derivation.left_implication A ∼A {A} {A, ⊥} {∼A, A}
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     apply Calculus.left_negation A {A} {A, ⊥}
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     apply Derivation.left_implication A ∼A {A} {A, ⊥} {∼A, A}
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     apply Calculus.left_negation A {A} {A, ⊥}
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     simp
--     simp
--     dsimp [instMin]
--     dsimp [land]
--   intro Th A
--   apply inconsistency_derivation at Th
--   apply Th at A
--   apply Nonempty.intro A

-- -- lemma inconsistency : ∀Th : Set (Formula L ℕ), ∀(A : L.Formula ℕ), Nonempty (Derivation Th {A ⇔ ∼A} {⊥}) := by
-- --   let inconsistency_derivation
-- --     (Th : Set (Formula L ℕ)) (A : Formula L ℕ) (h₂ : ∼A ≠ A) (h₃ : ⊥ ≠ A) (h₆ : A ⟹ ∼A ≠ ∼A ⟹ A):
-- --     Derivation Th {A ⇔ ∼A} {⊥} := by
-- --     dsimp [FirstOrder.Language.BoundedFormula.iff]
-- --     apply Derivation.left_conjunction (A ⟹ ∼A) (∼A ⟹ A) {(A ⟹ ∼A), (∼A ⟹ A)}
-- --     apply Derivation.left_implication A ∼A {(∼A ⟹ A)} {⊥, A} {∼A, (∼A ⟹ A)}
-- --     apply Derivation.left_implication ∼A A ∅ {⊥, A, ∼A} {A}
-- --     apply Derivation.right_negation A {A} {⊥, A}
-- --     apply Derivation.lax
-- --     simp
-- --     rw [Finset.sdiff_self]
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.union_comm]
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.union_comm]
-- --     rw [Finset.union_assoc]
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.union_comm]
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.union_comm]
-- --     rw [Finset.union_assoc]
-- --     apply Derivation.lax
-- --     simp
-- --     rw [Finset.union_empty]
-- --     rw [Finset.empty_union]
-- --     rw [Finset.insert_eq]
-- --     apply Derivation.left_implication ∼A A {∼A} {⊥, ∼A} {A, ∼A}
-- --     apply Derivation.right_negation A {∼A, A} {⊥}
-- --     apply Derivation.left_negation A {A} {⊥, A}
-- --     apply Derivation.lax
-- --     simp
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.union_comm]
-- --     rw [Finset.insert_sdiff_cancel]
-- --     rw [Finset.not_mem_singleton]
-- --     sorry
-- --     rw [Finset.insert_sdiff_cancel]
-- --     rw [Finset.not_mem_singleton]
-- --     have h : ∼A ≠ A := by
-- --       sorry
-- --     exact h
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.insert_eq]
-- --     apply Derivation.left_negation A {A} {⊥, A}
-- --     apply Derivation.lax
-- --     simp
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.insert_sdiff_cancel]
-- --     rw [Finset.not_mem_singleton]
-- --     sorry
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.union_comm]
-- --     rw [Finset.mem_insert]
-- --     simp
-- --     rw [Finset.mem_insert]
-- --     simp
-- --     rw [Finset.insert_eq]
-- --     rw [Finset.union_sdiff_cancel_left]
-- --     rw [Finset.sdiff_self]
-- --     rw [Finset.empty_union]
-- --     dsimp [land, instMin]
-- --     rw [Finset.disjoint_singleton]
-- --     sorry
-- --   intro Th A
-- --   apply inconsistency_derivation at Th
-- --   apply Th at A
-- --   apply Nonempty.intro
-- --   sorry

-- end Derivations
