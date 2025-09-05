import FormalizingAxiomaticTheoriesOfTruth.Syntax
import Mathlib.ModelTheory.Complexity
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Tree.Get
import Mathlib.Data.Set.Basic

namespace FirstOrder.Language
variable {α : Type} {L : Language} {n : Nat}

namespace Term
def empty_to_alpha : L.Term (Empty ⊕ Fin n) → L.Term (α ⊕ Fin n)
| .var (.inl v) => by cases v
| .var (.inr v) => .var (.inr v)
| .func f ts => .func f (fun i => empty_to_alpha (ts i))

instance : Coe (L.Term (Empty ⊕ Fin n)) (L.Term (α ⊕ Fin n)) where
coe := empty_to_alpha
end Term

namespace Sentence
open Term
def to_alpha : {n : Nat} → L.BoundedFormula Empty n → L.BoundedFormula α n
| _, .falsum => .falsum
| _, .equal t₁ t₂ => .equal t₁ t₂
| _, .rel r ts => .rel r (fun i => ts i)
| _, .imp φ ψ => .imp (to_alpha φ) (to_alpha ψ)
| _, .all φ => .all (to_alpha φ)

scoped instance : Coe (L.Sentence) (L.Formula α) where
coe := to_alpha
end Sentence

open Sentence
structure ProofSystem (L : Language) : Type where
  la : Set (L.Sentence)
  unary : Set (L.Formula α → L.Formula α)
  binary : Set (L.Formula α → L.Formula α → L.Formula α)

inductive Proof : (Th : L.Theory) → (s : @ProofSystem α L) →  L.Formula α → Type _
| ax {Th s} : (φ : L.Sentence) → φ ∈ s.la ∪ Th → Proof Th s φ
| un {Th s ψ φ} {r : L.Formula α → L.Formula α} : Proof Th s ψ → (r ∈ s.unary) → (r ψ = φ) → Proof Th s φ
| bi {Th s ψ₁ ψ₂ φ} {r : L.Formula α → L.Formula α → L.Formula α} : Proof Th s ψ₁ → Proof Th s ψ₂ → (r ∈ s.binary) → (r ψ₁ ψ₂ = φ) → Proof Th s φ

namespace ProofSystem
variable {α : Type}
def Provable (Th : L.Theory) (s : @ProofSystem α L) (φ : L.Formula α) : Prop :=
  Nonempty (Proof Th s φ)
notation Th " ⊢("s") " φ => Provable Th s φ

def Sound (s : @ProofSystem α L) : Prop :=
 ∀φ : L.Formula α, ∀Th, (Th ⊢(s) φ) → (Th ⊨ᵇ φ)
def Complete (s : @ProofSystem α L) : Prop :=
  ∀φ : L.Formula α, ∀Th, (Th ⊨ᵇ φ) → (Th ⊢(s) φ)

open Theory BoundedFormula

#check Formula.equivSentence

--  FirstOrder.Language.Theory.ModelsBoundedFormula.realize_sentence
open Term
variable {L : Language}{M : Type}[L.Structure M]
lemma empty_to_alpha_realize {v₁ : Empty → M} {v₂ : α → M} {xs : Fin n → M}: (t₁ : L.Term (Empty ⊕ Fin n)) → Term.realize (Sum.elim v₁ xs) t₁ = Term.realize (Sum.elim v₂ xs) (Term.empty_to_alpha t₁)
| .var (.inl v) => by cases v
| .var (.inr (.mk val isLt)) => by
  unfold Term.empty_to_alpha
  simp
| .func f ts => by
  simp[empty_to_alpha_realize,empty_to_alpha]
  have step1 : ∀i, realize (Sum.elim v₁ xs) (ts i) = realize (Sum.elim v₂ xs) (ts i).empty_to_alpha := by
    intro i
    apply empty_to_alpha_realize
  simp[step1]

lemma to_alpha_realizable {M : Type} [L.Structure M]{α : Type}{v₁ : Empty → M}{v₂ : α → M} : {n : ℕ} → (φ : L.BoundedFormula Empty n) → {xs : Fin n → M} → BoundedFormula.Realize φ v₁ xs = @BoundedFormula.Realize _ M _ _ _ (to_alpha φ) v₂ xs
| _, .falsum, xs => by
    unfold BoundedFormula.Realize
    trivial
| _, .equal t₁ t₂, xs => by
    unfold BoundedFormula.Realize to_alpha
    -- mp
    rw[empty_to_alpha_realize t₁]
    rw[empty_to_alpha_realize t₂]
| _, .rel r ts, xs => by
    unfold BoundedFormula.Realize to_alpha
    have step1 : ∀i, @realize L _ _ _ (Sum.elim v₁ xs) (ts i) = realize (Sum.elim v₂ xs) (ts i).empty_to_alpha := by
      intro i
      rw[empty_to_alpha_realize (ts i)]
    simp[step1]
| _, .imp φ ψ, xs => by
    simp[BoundedFormula.Realize,to_alpha]
    rw[(to_alpha_realizable φ)]
    rw[(to_alpha_realizable ψ)]
| _, .all φ, xs => by
    simp[BoundedFormula.Realize, to_alpha]
    apply Iff.intro
    -- mp
    intro h a
    rw[(@to_alpha_realizable _ _ _ _ _ _ φ (Fin.snoc xs a)).symm]
    exact (h a)
    -- mpr
    intro h a
    rw[(@to_alpha_realizable _ _ _ _ _ _ φ (Fin.snoc xs a))]
    exact (h a)

lemma sound_system_taut_axioms : ∀s : @ProofSystem α L, s.Sound → (∀φ ∈ (@to_alpha α _ _ '' s.la), {} ⊨ᵇ φ) := by
  intro s
  contrapose
  intro h₁
  simp at h₁
  let φ : L.Formula α := to_alpha h₁.choose
  have not_taut : ¬{} ⊨ᵇ φ := by
    apply h₁.choose_spec.right
  unfold Sound
  simp
  apply Exists.intro φ
  apply Exists.intro {}
  apply And.intro
  -- left
  apply Nonempty.intro
  apply Proof.ax
  apply Or.intro_left
  apply h₁.choose_spec.left
  -- right
  exact not_taut

lemma sound_system_sound_un : ∀Th : L.Theory, ∀s : @ProofSystem α L, s.Sound → (∀r ∈ s.unary,∀φ ψ, (Th ⊢(s) φ) → r φ = ψ → Th ⊨ᵇ ψ) := by
intro Th s
contrapose
intro h₁
simp at h₁
let r : L.Formula α → L.Formula α := h₁.choose
let φ : L.Formula α := h₁.choose_spec.right.choose
have provable_φ : Th ⊢(s) φ := by
  apply h₁.choose_spec.right.choose_spec.left
unfold Provable at provable_φ
apply Classical.ofNonempty at provable_φ
have r_in_unary : r ∈ s.unary := by
  apply h₁.choose_spec.left
have provable : Th ⊢(s) r φ := by
  unfold Provable
  apply Nonempty.intro
  apply Proof.un
  apply provable_φ
  apply r_in_unary
  rfl
unfold Sound
simp
apply Exists.intro (r φ)
apply Exists.intro Th
apply And.intro
-- left
exact provable
-- right
apply h₁.choose_spec.right.choose_spec.right

lemma sound_system_sound_bi : ∀Th : L.Theory, ∀s : @ProofSystem α L, s.Sound → (∀r ∈ s.binary,∀φ₁ φ₂ ψ, (Th ⊢(s) φ₁) → (Th ⊢(s) φ₂) → r φ₁ φ₂ = ψ → Th ⊨ᵇ ψ) := by
sorry

theorem sound_system_sound_rules : ∀Th : L.Theory, ∀s : @ProofSystem α L, s.Sound → (∀φ ∈ (@to_alpha α _ _ '' s.la), {} ⊨ᵇ φ) ∧ (∀r ∈ s.unary,∀φ ψ, (Th ⊢(s) φ) → r φ = ψ → Th ⊨ᵇ ψ) := by
intro Th s
contrapose
intro h₁
simp at h₁
by_cases h₂ : ∀φ ∈ (@to_alpha α _ _ '' s.la), {} ⊨ᵇ φ
-- pos
simp at h₂
apply h₁ at h₂
let r : L.Formula α → L.Formula α := h₂.choose
let φ : L.Formula α := h₂.choose_spec.right.choose
have provable_φ : Th ⊢(s) φ := by
  apply h₂.choose_spec.right.choose_spec.left
unfold Provable at provable_φ
apply Classical.ofNonempty at provable_φ
have r_in_unary : r ∈ s.unary := by
  apply h₂.choose_spec.left
have provable : Th ⊢(s) r φ := by
  unfold Provable
  apply Nonempty.intro
  apply Proof.un
  apply provable_φ
  apply r_in_unary
  rfl
unfold Sound
simp
apply Exists.intro (r φ)
apply Exists.intro Th
apply And.intro
-- left
exact provable
-- right
apply h₂.choose_spec.right.choose_spec.right
-- neg
simp at h₂
let φ : L.Formula α := to_alpha h₂.choose
have not_taut : ¬{} ⊨ᵇ φ := by
  apply h₂.choose_spec.right
unfold Sound
simp
apply Exists.intro φ
apply Exists.intro {}
apply And.intro
-- left
apply Nonempty.intro
apply Proof.ax
apply Or.intro_left
apply h₂.choose_spec.left
-- right
exact not_taut

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
