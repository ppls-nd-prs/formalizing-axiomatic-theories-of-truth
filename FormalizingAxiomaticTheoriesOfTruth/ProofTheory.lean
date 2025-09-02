import FormalizingAxiomaticTheoriesOfTruth.Syntax
import Mathlib.ModelTheory.Complexity
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Tree.Get
import Mathlib.Data.Set.Basic

namespace FirstOrder.Language
variable {α : Type}{n : Nat}

class System where
  l : Language
  axioms : Set (l.BoundedFormula α n)
  unary : Set (l.BoundedFormula α n → l.BoundedFormula α n)
  binary : Set (l.BoundedFormula α n → l.BoundedFormula α n → l.BoundedFormula α n)

def follows_system_rules : (ls : @System α n) → Tree (ls.l.BoundedFormula α n) → Prop
| _, .nil => True
| _, .node _ .nil .nil => True
| ls, .node a .nil (.node b t₁ t₂) => ∃r ∈ ls.unary, (r b) = a ∧ follows_system_rules ls t₁ ∧ follows_system_rules ls t₂
| ls, .node a (.node b t₁ t₂) .nil => ∃r ∈ ls.unary, (r b) = a ∧ follows_system_rules ls t₁ ∧ follows_system_rules ls t₂
| ls, .node a (.node b t₁ t₂) (.node c t₃ t₄) => ∃r ∈ ls.binary, (r b c) = a ∧ follows_system_rules ls t₁ ∧ follows_system_rules ls t₂ ∧ follows_system_rules ls t₃ ∧ follows_system_rules ls t₄

def leaves {β : Type} : Tree β → Set β
| .nil => {}
| .node a .nil .nil => {a}
| .node _ t₁ t₂ => (leaves t₁) ∪ (leaves t₂)

def leaves_are_axioms (ls : @System α n) (Th : Set (ls.l.BoundedFormula α n)) (tr : Tree (ls.l.BoundedFormula α n)) : Prop :=
  ∀lf ∈ leaves tr, lf ∈ ls.axioms ∨ lf ∈ Th

class Proof {α : Type} {n : Nat} (ls : System) (Th : Set (ls.l.BoundedFormula α n)) (φ : ls.l.BoundedFormula α n) where
  mk ::
  tree : Tree (ls.l.BoundedFormula α n)
  root : tree.get PosNum.one = φ
  rules : follows_system_rules ls tree
  ax : leaves_are_axioms ls Th tree

namespace System
variable {α : Type}{n : Nat}
def provable (s : System α n) (φ : s.l.BoundedFormula α n) : Prop :=
  Nonempty (@Proof α n s )
end System

end FirstOrder.Language

namespace Calculus

end Calculus

namespace Derivations
open Calculus
open BoundedFormula

variable {L : Language}
[∀ n, DecidableEq (L.Functions n)]
[∀ n, DecidableEq (L.Relations n)]
[DecidableEq (Formula L ℕ)]

def mp_derivation
  (Th : L.Theory) (A B : Formula L ℕ) :
  Derivation Th {A, A ⟹ B} {B} := by
  have d₁ : Derivation Th {A} {B, A} := by
    apply Derivation.lax
    exact ⟨A, by simp⟩
  have d₂ : Derivation Th {B, A} {B} := by
    apply Derivation.lax
    exact ⟨B, by simp⟩
  apply Derivation.left_implication A B {A} {B, A} {B, A}
  exact d₁
  apply Finset.insert_eq
  exact d₂
  apply Finset.insert_eq
  apply Finset.insert_eq

def disj_intro_left_derivation
  (Th : L.Theory) (A B : Formula L ℕ) :
  Derivation Th {A} {A ∨' B} := by
  apply Derivation.right_disjunction A B {A, B} {} _ (by simp) (by simp)
  exact Derivation.lax ⟨A, by simp⟩

def disj_intro_right_derivation
  (Th : L.Theory) (A B : Formula L ℕ) :
  Derivation Th {B} {A ∨' B} := by
  apply Derivation.right_disjunction A B {A, B} {} _ (by simp) (by simp)
  exact Derivation.lax ⟨B, by simp⟩

def conj_elim_left_derivation
  (Th : L.Theory) (A B : Formula L ℕ) :
  Derivation Th {A ∧' B} {A} := by
  apply Derivation.left_conjunction A B {A, B} {}
  apply Derivation.lax
  simp
  simp
  simp

def conj_elim_right_derivation
  (Th : L.Theory) (A B : Formula L ℕ) :
  Derivation Th {A ∧' B} {B} := by
  apply Derivation.left_conjunction A B {A, B} {}
  apply Derivation.lax
  simp
  simp
  simp

def double_neg_left_derivation
  (Th: L.Theory) (A : Formula L ℕ) :
  Derivation Th {∼∼A} {A} := by
  apply Calculus.left_negation ∼A ∅ {A, ∼A}
  apply Calculus.right_negation A {A} {A}
  apply Derivation.lax
  simp
  rw [Finset.insert_eq]
  rw [Finset.empty_union]


def double_neg_right_derivation
  (Th: L.Theory) (A : Formula L ℕ) :
  Derivation Th {A} {∼∼A} := by
  apply Calculus.right_negation ∼A {A,∼A} ∅
  apply Calculus.left_negation A {A} {A}
  apply Derivation.lax
  simp
  rw [Finset.insert_eq]
  rw [Finset.empty_union]

def demorganslaw_first_derivation
  (Th : L.Theory) (A B : Formula L ℕ) :
  Derivation Th {∼(A ∧' B)} {∼A ∨' ∼B} := by
  apply Calculus.left_negation (A ∧'B) {} {A ∧'B, ∼A∨'∼B}
  apply Derivation.right_disjunction ∼A ∼B {A ∧'B, ∼A, ∼B} {A ∧' B}
  apply Calculus.right_negation A {A} {A ∧'B, ∼B}
  apply Calculus.right_negation B {A, B} {A ∧'B}
  apply Derivation.right_conjunction A B {A} {B} ∅
  apply Derivation.lax
  simp
  rw [Finset.empty_union]
  apply Derivation.lax
  simp
  rw [Finset.empty_union]
  rw [Finset.empty_union]
  rw [Finset.insert_eq]
  rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
  rw [Finset.union_assoc]
  rw [Finset.union_comm {∼A} {∼B}]
  rw [Finset.insert_eq]
  rw [Finset.insert_eq]
  simp

def demorganslaw_second_derivation
  (Th : L.Theory) (A B : Formula L ℕ) :
  Derivation Th {∼(A ∨' B)} {∼A ∧' ∼B} := by
  apply Calculus.left_negation (A ∨'B) ∅ {A ∨' B, ∼A ∧' ∼B}
  apply Derivation.right_disjunction A B {∼A ∧' ∼B, A, B} {∼A ∧' ∼B}
  apply Derivation.right_conjunction ∼A ∼B {A, B, ∼A} {A, B, ∼B} {A, B}
  apply Calculus.right_negation A {A} {A, B}
  apply Derivation.lax
  simp
  rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
  rw [Finset.union_assoc]
  rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
  rw [Finset.union_assoc]
  apply Calculus.right_negation B {B} {A, B}
  apply Derivation.lax
  simp
  rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
  rw [Finset.union_assoc]
  rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
  rw [Finset.union_assoc]
  rw [Finset.insert_eq, Finset.insert_eq]
  rw [Finset.union_comm]
  rw [Finset.insert_eq]
  rw [Finset.insert_eq]
  rw [Finset.union_comm]
  rw [Finset.empty_union]

def right_implication_derivation
  (Th : L.Theory) (A B Γ : Formula L ℕ)
  (d₁: Derivation Th {Γ, A} {B}) :
  Derivation Th {Γ} {A ⟹ B} := by
  apply Derivation.right_implication A B {Γ, A} {B} ∅
  exact d₁
  rw [Finset.insert_eq]
  rw [Finset.union_comm]
  rw [Finset.empty_union]
  rw [Finset.empty_union]

def disj_elim_derivation
  (Th : L.Theory) (A B C: Formula L ℕ)
  (d₁ : Derivation Th {A} {C}) (d₂ : Derivation Th {B} {C}) :
  Derivation Th {A ∨' B} {C} := by
  apply Derivation.left_disjunction A B {A} {B} ∅
  exact d₁
  simp
  exact d₂
  simp
  simp

lemma mp : ∀th : L.Theory, ∀(A B : L.Formula ℕ), Nonempty (Derivation th {A, A ⟹ B} {B}) := by
  let mp_derivation
    (Th : L.Theory) (A B : Formula L ℕ) :
    Derivation Th {A, A ⟹ B} {B} := by
    have d₁ : Derivation Th {A} {B, A} := by
      apply Derivation.lax
      exact ⟨A, by simp⟩
    have d₂ : Derivation Th {B, A} {B} := by
      apply Derivation.lax
      exact ⟨B, by simp⟩
    apply Derivation.left_implication A B {A} {B, A} {B, A}
    exact d₁
    apply Finset.insert_eq
    exact d₂
    apply Finset.insert_eq
    apply Finset.insert_eq
  intro th A B
  apply mp_derivation at th
  apply th at A
  apply A at B
  apply Nonempty.intro B

lemma conj_intro : ∀th : L.Theory, ∀(A B : L.Formula ℕ), Nonempty (Derivation th {A, B} {A ∧' B}) := by
  let conj_intro_derivation
    (Th :L.Theory) (A B : Formula L ℕ) :
    Derivation Th {A, B} {A ∧' B} := by
    apply Derivation.right_conjunction A B {A} {B} ∅
    apply Derivation.lax ⟨A, by simp⟩
    simp
    apply Derivation.lax ⟨B, by simp⟩
    simp
    simp
  intro th A B
  apply conj_intro_derivation at th
  apply th at A
  apply A at B
  apply Nonempty.intro B

lemma conj_elim : ∀th : L.Theory, ∀(A B : L.Formula ℕ), Nonempty (Derivation th {A ∧' B} {A, B}) := by
  let conj_elim_derivation
    (Th : L.Theory) (A B : Formula L ℕ) :
    Derivation Th {A ∧' B} {A, B} := by
    apply Derivation.left_conjunction A B {A, B} {}
    apply Derivation.lax
    simp
    simp
    simp
  intro th A B
  apply conj_elim_derivation at th
  apply th at A
  apply A at B
  apply Nonempty.intro B

lemma excl_mid : ∀th : L.Theory, ∀(A : L.Formula ℕ), ∀(Δ : Finset (Formula L ℕ)), Nonempty (Derivation th Δ {A ∨'∼A}) := by
  let excl_mid_derivation
    (Th : L.Theory) (A : Formula L ℕ) (Δ : Finset (Formula L ℕ)) :
    Derivation Th Δ {A ∨'∼A} := by
    apply Derivation.right_disjunction A ∼A {A, ∼A} {}
    apply Calculus.right_negation A (Δ ∪ {A}) {A}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    simp
    rfl
  sorry

lemma eqv_trans : ∀Th : L.Theory, ∀(A B C : L.Formula ℕ), Nonempty (Derivation Th {A ⇔ B, C ⇔ B} {A ⇔ C}) := by
  let eqv_trans_derivation
    (Th : L.Theory) (A B C : Formula L ℕ) :
    Derivation Th {A ⇔ B, C ⇔ B} {A ⇔ C} := by
    dsimp [FirstOrder.Language.BoundedFormula.iff]
    dsimp [instMin]
    apply Derivation.right_conjunction (A ⟹ C) (C ⟹ A) {A ⟹ C} {C ⟹ A} ∅
    apply Derivation.right_implication A C {A, (A ⟹ B) ⊓ (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {C} ∅
    apply Derivation.left_conjunction (A ⟹ B) (B ⟹ A) {A, (A ⟹ B), (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {A, (C ⟹ B) ⊓ (B ⟹ C)}
    apply Derivation.left_conjunction (C ⟹ B) (B ⟹ C) {A, (A ⟹ B), (B ⟹ A), (C ⟹ B), (B ⟹ C)} {A, A ⟹ B, B ⟹ A}
    apply Calculus.cut B {A, (A ⟹ B)} ∅ {(B ⟹ A), (C ⟹ B), (B ⟹ C)} {C}
    apply mp_derivation
    rw [← Finset.insert_eq]
    apply Derivation.left_implication B C {B, (B ⟹ A), (C ⟹ B)} {C, B} {C, B, (B ⟹ A), (C ⟹ B)}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [Finset.empty_union]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    dsimp [instMin]
    dsimp [land]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [Finset.union_right_comm]
    dsimp [instMin]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [Finset.union_right_comm]
    dsimp [instMin]
    dsimp [land]
    rw [← Finset.union_assoc]
    rw [← Finset.insert_eq]
    dsimp [instMin]
    rw [Finset.empty_union]
    rw [Finset.empty_union]
    rw [Finset.empty_union]
    apply Derivation.right_implication C A {C, (A ⟹ B) ⊓ (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {A} ∅
    apply Derivation.left_conjunction (A ⟹ B) (B ⟹ A) {C, (A ⟹ B), (B ⟹ A), (C ⟹ B) ⊓ (B ⟹ C)} {C, (C ⟹ B) ⊓ (B ⟹ C)}
    apply Derivation.left_conjunction (C ⟹ B) (B ⟹ C) {C, (C ⟹ B), (A ⟹ B), (B ⟹ A),  (B ⟹ C)} {C, A ⟹ B, B ⟹ A}
    apply Calculus.cut B {C, (C ⟹ B)} ∅ {(A ⟹ B), (B ⟹ A), (B ⟹ C)} {A}
    apply mp_derivation
    rw [← Finset.insert_eq]
    apply Derivation.left_implication B A {B, (A ⟹ B), (B ⟹ C)} {A, B} {A, B, (A ⟹ B), (B ⟹ C)}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.union_right_comm]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [Finset.empty_union]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [Finset.union_right_comm]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.union_right_comm]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    dsimp [instMin]
    dsimp [land]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.union_comm]
    rw [Finset.union_left_comm]
    rw [Finset.union_comm]
    rw [Finset.union_left_comm]
    rw [← Finset.union_assoc]
    rw [← Finset.union_assoc]
    rw [Finset.union_right_comm]
    rw [Finset.union_assoc]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    rw [← Finset.union_assoc]
    rw [Finset.union_right_comm]
    dsimp [instMin]
    dsimp [land]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
    dsimp [instMin]
    simp
    simp
    simp
    simp
    dsimp [land]
  intro Th A B C
  apply eqv_trans_derivation at Th
  apply Th at A
  apply A at B
  apply B at C
  apply Nonempty.intro C

lemma inconsistency : ∀Th : L.Theory, ∀(A : L.Formula ℕ), Nonempty (Derivation Th {A ⇔ ∼A} {⊥}) := by
  let inconsistency_derivation
    (Th : L.Theory) (A : Formula L ℕ) :
    Derivation Th {A ⇔ ∼A} {⊥} := by
    dsimp [FirstOrder.Language.BoundedFormula.iff]
    apply Derivation.left_conjunction (A ⟹ ∼A) (∼A ⟹ A) {(A ⟹ ∼A), (∼A ⟹ A)} {}
    apply Derivation.left_implication ∼A A {(A ⟹ ∼A)} {⊥, ∼A} {A, (A ⟹ ∼A)}
    apply Calculus.right_negation A {(A ⟹ ∼A), A} {⊥}
    apply Derivation.left_implication A ∼A {A} {A, ⊥} {∼A, A}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    apply Calculus.left_negation A {A} {A, ⊥}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    apply Derivation.left_implication A ∼A {A} {A, ⊥} {∼A, A}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    apply Calculus.left_negation A {A} {A, ⊥}
    apply Derivation.lax
    simp
    rw [Finset.insert_eq]
    rw [Finset.union_comm]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    rw [Finset.insert_eq]
    simp
    simp
    dsimp [instMin]
    dsimp [land]
  intro Th A
  apply inconsistency_derivation at Th
  apply Th at A
  apply Nonempty.intro A

-- lemma inconsistency : ∀Th : Set (Formula L ℕ), ∀(A : L.Formula ℕ), Nonempty (Derivation Th {A ⇔ ∼A} {⊥}) := by
--   let inconsistency_derivation
--     (Th : Set (Formula L ℕ)) (A : Formula L ℕ) (h₂ : ∼A ≠ A) (h₃ : ⊥ ≠ A) (h₆ : A ⟹ ∼A ≠ ∼A ⟹ A):
--     Derivation Th {A ⇔ ∼A} {⊥} := by
--     dsimp [FirstOrder.Language.BoundedFormula.iff]
--     apply Derivation.left_conjunction (A ⟹ ∼A) (∼A ⟹ A) {(A ⟹ ∼A), (∼A ⟹ A)}
--     apply Derivation.left_implication A ∼A {(∼A ⟹ A)} {⊥, A} {∼A, (∼A ⟹ A)}
--     apply Derivation.left_implication ∼A A ∅ {⊥, A, ∼A} {A}
--     apply Derivation.right_negation A {A} {⊥, A}
--     apply Derivation.lax
--     simp
--     rw [Finset.sdiff_self]
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.union_assoc]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.union_assoc]
--     apply Derivation.lax
--     simp
--     rw [Finset.union_empty]
--     rw [Finset.empty_union]
--     rw [Finset.insert_eq]
--     apply Derivation.left_implication ∼A A {∼A} {⊥, ∼A} {A, ∼A}
--     apply Derivation.right_negation A {∼A, A} {⊥}
--     apply Derivation.left_negation A {A} {⊥, A}
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.insert_sdiff_cancel]
--     rw [Finset.not_mem_singleton]
--     sorry
--     rw [Finset.insert_sdiff_cancel]
--     rw [Finset.not_mem_singleton]
--     have h : ∼A ≠ A := by
--       sorry
--     exact h
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     apply Derivation.left_negation A {A} {⊥, A}
--     apply Derivation.lax
--     simp
--     rw [Finset.insert_eq]
--     rw [Finset.insert_sdiff_cancel]
--     rw [Finset.not_mem_singleton]
--     sorry
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.insert_eq]
--     rw [Finset.union_comm]
--     rw [Finset.mem_insert]
--     simp
--     rw [Finset.mem_insert]
--     simp
--     rw [Finset.insert_eq]
--     rw [Finset.union_sdiff_cancel_left]
--     rw [Finset.sdiff_self]
--     rw [Finset.empty_union]
--     dsimp [land, instMin]
--     rw [Finset.disjoint_singleton]
--     sorry
--   intro Th A
--   apply inconsistency_derivation at Th
--   apply Th at A
--   apply Nonempty.intro
--   sorry

end Derivations
