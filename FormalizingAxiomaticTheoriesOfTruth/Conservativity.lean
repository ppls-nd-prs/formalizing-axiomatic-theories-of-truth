import FormalizingAxiomaticTheoriesOfTruth.ProofTheory

open FirstOrder
open Language

namespace PA
  open Languages
  open LPA
  open L_T
  open BoundedFormula

  variable{L : Language}
  def replace_bv_with_non_var_term (f : BoundedFormula L Empty 1) (t : Term L Empty) : Sentence L :=
    subst f.toFormula (fun _ : Empty ⊕ Fin 1 => t)
  notation A "//[" t "]" => replace_bv_with_non_var_term A t
  def replace_bv_with_bv_term  (f : BoundedFormula L Empty 1) (t : Term L (Empty ⊕ Fin 1)) : BoundedFormula L Empty 1 :=
    (relabel id (subst (f.toFormula) (fun _ : (Empty ⊕ Fin 1) => t)))
  notation A "///[" t "]" => replace_bv_with_bv_term A t

  /-- The induction function for ℒₚₐ -/
  def induction (f : BoundedFormula ℒ Empty 1) : Sentence ℒ :=
    ∼ (f//[LPA.null] ⟹ (∼(∀'(f ⟹ f///[S(&0)])))) ⟹ ∀'f

  /-- Peano arithemtic -/
  inductive peano_arithmetic : Theory ℒ where
    | first : peano_arithmetic (∀' ∼(LPA.null =' S(&0)))
    | second :peano_arithmetic (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
    | third : peano_arithmetic (∀' ((&0 add LPA.null) =' &0))
    | fourth : peano_arithmetic (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
    | fifth : peano_arithmetic (∀' ((&0 times LPA.null) =' LPA.null))
    | sixth : peano_arithmetic (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
    | induction (φ) : peano_arithmetic (induction φ)

  notation "𝐏𝐀" => peano_arithmetic

end PA

namespace PAT
open Languages
  open L_T
 /-- The induction function for ℒₚₐ -/
  def induction (f : BoundedFormula ℒₜ Empty 1) : Sentence ℒₜ :=
    ∼ (f//[L_T.null] ⟹ (∼(∀'(f ⟹ f///[S(&0)])))) ⟹ ∀'f

  /-- Peano arithemtic -/
  inductive peano_arithmetic_t : Theory ℒₜ where
    | first : peano_arithmetic_t (∀' ∼(L_T.null =' S(&0)))
    | second :peano_arithmetic_t (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
    | third : peano_arithmetic_t (∀' ((&0 add L_T.null) =' &0))
    | fourth : peano_arithmetic_t (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
    | fifth : peano_arithmetic_t (∀' ((&0 times L_T.null) =' L_T.null))
    | sixth : peano_arithmetic_t (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
    | induction (φ) : peano_arithmetic_t (induction φ)

  notation "𝐏𝐀𝐓" => peano_arithmetic_t
end PAT

namespace TB
open Languages
open L_T
open LPA
open PAT
open SyntaxTheory
open TermEncoding

inductive tarski_biconditionals : Theory ℒₜ where
  | pat_axioms {φ} : peano_arithmetic_t φ → tarski_biconditionals φ
  | syntax_axioms {φ} : syntax_theory φ → tarski_biconditionals φ
  | disquotation {φ : Sentence ℒ} : tarski_biconditionals (T(⌜φ⌝) ⇔ φ)

notation "𝐓𝐁" => tarski_biconditionals
end TB

namespace Conservativity
  open Languages
  open Calculus
  open TB
  open PA

  -- theorem conservativity_of_tb (f : Formula ℒ ℕ) : (𝐓𝐁 ⊢ f) → (𝐏𝐀 ⊢ f) := by
  --   sorry
end Conservativity

namespace Conservativity
  open Languages
  open L_T
  open Calculus
  open TB
  open PA
  open TermEncoding

  /-- Gives whether a BoundedFormula contains a T predicate-/
  @[simp] def contains_T {n} : BoundedFormula ℒₜ ℕ n → Prop
  | .rel L_T.Rel.t _ => true
  | .imp f₁ f₂ => contains_T f₁ ∨ contains_T f₂
  | .all f => contains_T f
  | _ => false

  /-- Proves that contains_T is a decidable predicate-/
  def decPred_contains_T : {n : ℕ} → (a : BoundedFormula ℒₜ ℕ n) → Decidable (contains_T a)
  | _, .falsum => by
    apply Decidable.isFalse
    simp
  | _, .equal t₁ t₂ => by
    apply Decidable.isFalse
    simp
  | _, .rel R ts => by cases R with
    | t =>
      apply Decidable.isTrue
      simp
    | _ =>
      apply Decidable.isFalse
      simp
  | _, .imp f₁ f₂ => by
    simp[contains_T]
    apply decPred_contains_T at f₁
    apply decPred_contains_T at f₂
    apply instDecidableOr
  | _, .all f => by
    apply decPred_contains_T at f
    simp
    exact f

  instance : DecidablePred (@contains_T 0) := decPred_contains_T

  open Matrix
  /-- Gives whether a formula is a disquotation axiom -/
  @[simp] def is_disq_sent : {n : ℕ} → (f : BoundedFormula ℒₜ ℕ n) → Prop
  | .zero, (((.rel L_T.Rel.t ts₁ ⟹ f₁) ⟹ ((f₂ ⟹ .rel L_T.Rel.t ts₂) ⟹ ⊥)) ⟹ ⊥) =>
    f₁ = f₂ ∧ (ts₁ 0) = ⌜f₁⌝ ∧ (ts₂ 0) = ⌜f₂⌝
  | _,  _ => False


  instance dec_eq_terms : DecidableEq (Term ℒₜ (ℕ ⊕ Fin 0)) := Term.instDecidableEq

  @[simp] def dec_first_elem_disq (ts : (Fin 1) → Term ℒₜ (ℕ ⊕ Fin 0)) (f : BoundedFormula ℒₜ ℕ 0) : Decidable ((ts 0) = ⌜f⌝) :=
    dec_eq_terms (ts 0) ⌜f⌝

  /-- Proof that is_disq_sent is a decidable Predicate -/
  def decPred_is_disq_sent : {n : ℕ} → (f : BoundedFormula ℒₜ ℕ n) → Decidable (is_disq_sent f)
  | .zero, f => by
    cases f <;> try { apply isFalse; simp }
    case imp f₁ f₂ =>
    cases f₂ <;> try { apply isFalse; simp }
    case falsum =>
    cases f₁ <;> try { apply isFalse; simp }
    case imp f₃ f₄ =>
    cases f₃ <;> try { apply isFalse; simp }
    case imp f₅ f₆ =>
    cases f₅ <;> try { apply isFalse; simp }
    case rel R ts₆ =>
    cases R <;> try { apply isFalse; simp }
    case t =>
    cases f₄ <;> try { apply isFalse; simp }
    case imp f₇ f₈ =>
    cases f₈ <;> try { apply isFalse; simp }
    case falsum =>
    cases f₇ <;> try { apply isFalse; simp }
    case imp f₉ f₁₀ =>
    cases f₁₀ <;> try { apply isFalse; simp }
    case rel R ts₉ =>
    cases R <;> try { apply isFalse; simp }
    case t =>
      have step1: Decidable (f₆ = f₉) := by
        apply hasDecEq
      apply dec_first_elem_disq at ts₆
      apply ts₆ at f₆
      apply dec_first_elem_disq at ts₉
      apply ts₉ at f₉
      simp
      apply instDecidableAnd
  | .succ n, _ => by
    apply isFalse
    simp

  instance : DecidablePred (@is_disq_sent 0) := decPred_is_disq_sent

  def contains_T_sent : Sentence ℒₜ → Prop :=
    fun s : Sentence ℒₜ =>
      contains_T (bf_empty_to_bf_N s)

  def real_PA : Set (Formula ℒₜ ℕ) := {f | f ∈ 𝐓𝐁 ∧ (contains_T f)}
  def real_LPA : Set (Formula ℒₜ ℕ) := {f | f ∈ Set.univ ∧ (contains_T f)}
  open LPA
  instance : Coe (Set (Formula ℒ ℕ)) (Set (Formula ℒₜ ℕ)) where
    coe S := ϕ.onFormula '' S
  /- Need to define -/
  /- ALSO TODO define a set translation coercion for sets of formula in ℒ
  to sets of formulas in ℒₜ -/

  variable {L : Language} {Th : Set (Formula L ℕ)}[∀n, DecidableEq (L.Functions n)][∀p, DecidableEq (L.Relations p)]
  /-- Obtains a Finset of all formulas that occur in some derivation -/
  def der_to_finset_fml {Δ Γ} : Derivation Th Δ Γ → Finset (Formula L ℕ)
    | .tax _ => Δ ∪ Γ
    | .lax _ => Δ ∪ Γ
    | .left_conjunction _ _ _ d _ _ _ => (der_to_finset_fml d) ∪ Δ ∪ Γ
    | .left_disjunction _ _ _ _ _ d₁ _ d₂ _ _ => (der_to_finset_fml d₁) ∪ (der_to_finset_fml d₂) ∪ Δ ∪ Γ
    | .left_implication _ _ _ _ _ d₁ _ d₂ _ _ => (der_to_finset_fml d₁) ∪ (der_to_finset_fml d₂) ∪ Δ ∪ Γ
    | .left_bot _ => Δ ∪ Γ
    | .right_conjunction _ _ _ _ _ d₁ _ d₂ _ _ => (der_to_finset_fml d₁) ∪ (der_to_finset_fml d₂) ∪ Δ ∪ Γ
    | .right_disjunction _ _ _ d _ => (der_to_finset_fml d) ∪ Δ ∪ Γ
    | .right_implication _ _ _ _ _ d _ _ _ => (der_to_finset_fml d) ∪ Δ ∪ Γ
    | .left_forall _ _ _ _ _ d _ _ => (der_to_finset_fml d) ∪ Δ ∪ Γ
    | .left_exists _ _ _ _ d _ => (der_to_finset_fml d) ∪ Δ ∪ Γ
    | .right_forall _ _ _ _ d _ => (der_to_finset_fml d) ∪ Δ ∪ Γ
    | .right_exists _ _ _ _ _ d _ => (der_to_finset_fml d) ∪ Δ ∪ Γ
    | .cut _ _ _ _ _ d₁ d₂ _ _ => (der_to_finset_fml d₁) ∪ (der_to_finset_fml d₂) ∪ Δ ∪ Γ

  /-- Obtain a finset that contains only the formula containing a T from a finset -/
  def get_T_fmls (S : Finset (Formula ℒₜ ℕ)) : Finset (Formula ℒₜ ℕ) :=
    {f ∈ S | contains_T f}

  /-- Obtains all disquotation sentences in a finset -/
  def get_disq_sents (S : Finset (Formula ℒₜ ℕ)) : Finset (Formula ℒₜ ℕ) :=
    {f ∈ S | is_disq_sent f}

  /-- Transforms a disquotation axiom to the corresponding tau disjunct -/
  def disq_to_tau : BoundedFormula ℒₜ ℕ 0 → BoundedFormula ℒₜ ℕ 0
  | (((.rel L_T.Rel.t ts₁ ⟹ f₁) ⟹ ((f₂ ⟹ .rel L_T.Rel.t ts₂) ⟹ ⊥)) ⟹ ⊥) =>
    #0 =' ⌜f₁⌝ ⇔ f₁
  | _ => ⊥

  -- def f₅ : Formula ℒₜ ℕ := (((.rel L_T.Rel.t ![⌜⊥⌝] ⟹ ⊥) ⟹ ((f₂ ⟹ .rel L_T.Rel.t ts₂) ⟹ ⊥)) ⟹ ⊥)
  -- #eval disq_to_tau

  /-- transforms all disquotation axioms in a given Finset to their corresponding tau disjunct -/
  def transform_to_tau_disjuncts (S : Finset (Formula ℒₜ ℕ)): (Finset (Formula ℒₜ ℕ)) :=
    S.image disq_to_tau

  /-- mapping necessary for glueing together all disjuncts into one big disjunction -/
  def mapping (s : Finset (BoundedFormula ℒₜ ℕ 0)) : { x : (BoundedFormula ℒₜ ℕ 0) // x ∈ s} → (BoundedFormula ℒₜ ℕ 0) := fun i => i.val

  def f₂ : Formula ℒₜ ℕ := ⊥
  #eval BoundedFormula.Realize f₂ id id
  -- def le : BoundedFormula L α n → BoundedFormula L α n :=
  -- instance : LinearOrder (BoundedFormula L α n) where
  --   le a b :=
#check @Max.left_comm (BoundedFormula ℒₜ ℕ 0)
  def left_comm_max (a b c : BoundedFormula L α n) : max a (max b c) = max b (max a c):= by
    rw[Max.left_comm a b c]



  def structure_fun : {n : ℕ} → L_T.Func n → (Fin n → ℕ) → ℕ
    | _, .zero, _ => 0
    | _, .succ, _ => 1
    | _, L_T.Func.subs, _ => 2
    | _, L_T.Func.denote, _ => 3
    | _, L_T.Func.exists, _ => 4
    | _, L_T.Func.forall, _ => 5
    | _, L_T.Func.cond, _ => 6
    | _, L_T.Func.disj, _ => 7
    | _, L_T.Func.conj, _ => 8
    | _, L_T.Func.neg, _ => 9
    | _, L_T.Func.mult, _ => 10
    | _, L_T.Func.add, _ => 11

  def number : BoundedFormula ℒₜ ℕ 0 → ℕ :=
    fun f => formula_N_tonat f

  def le_bf : BoundedFormula ℒₜ ℕ 0 → BoundedFormula ℒₜ ℕ 0 → Prop :=
    fun f₁ f₂ => (number f₁) ≤ (number f₂)

  def lt_bf : Formula ℒₜ ℕ → Formula ℒₜ ℕ → Prop :=
    fun f₁ f₂ => (number f₁) < (number f₂)

  #check Multiset.card


  #check Formula.realize_top.mp ⊤.Realize

  variable {M : Type _}[L.Structure M]{α : Type _}{v : α → M}
  instance struct : Structure ℒₜ ℕ where
    funMap := structure_fun
    RelMap := sorry
  def f₉ : Formula ℒₜ ℕ := ⊤
  def mapp : ℕ → ℕ := id
  example : f₉.Realize mapp := by

  #check Formula.realize_top.mp (f₉.Realize mapp)
  instance : LinearOrder (BoundedFormula ℒₜ ℕ 0) where
    le := le_bf
    lt := lt_bf
    le_refl := by
      simp[le_bf]
    le_trans := by
      simp[le_bf,number,toString,String.length]
      intro f₁ f₂ f₃
      intro h₁ h₂






  instance : Max (BoundedFormula L α n) := BoundedFormula.instMax
  instance : LeftCommutative (@max (BoundedFormula L ℕ 0) BoundedFormula.instMax) := by sorry
  noncomputable def iSup [Finite β] (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
    let _ := Fintype.ofFinite β
    ((Finset.univ : Finset β).1.map f).foldr (· ⊔ ·) ⊥

  /-- takes a set of disjuncts to their disjunction -/
  noncomputable def disjuncts_to_disjunction (S : Finset (Formula ℒₜ ℕ)) : Formula ℒₜ ℕ :=
    BoundedFormula.iSup (mapping S)

  variable {th : Set (Formula ℒₜ ℕ)}
  /-- takes a derivation and builds the corresponding tau formula -/
  noncomputable def build_tau {Γ Δ} (d : Derivation th Γ Δ) : Formula ℒₜ ℕ :=
    disjuncts_to_disjunction (transform_to_tau_disjuncts (get_disq_sents (der_to_finset_fml d)))

  def s₁ : Finset (BoundedFormula ℒₜ ℕ 0) := {f₁, f₁}
  #check s₁.image
  #check Finite (Finset (Formula ℒₜ ℕ))
  -- instance : Finite (Finset (Formula ℒₜ ℕ))

  -- instance : Finite s₁ := by exact Finset.finite_toSet s₁
  -- instance : InfSet ({ x // x ∈ s₁}) := by sorry
  #check BoundedFormula.iInf (mapping s₁)

  -- def length : Finset (Formula ℒₜ ℕ) → ℕ
  -- | {} => 0
  -- | s ∪ {a} => (length s) + 1

  lemma one : ∀s : Finset (Formula ℒₜ ℕ), ∀n, s.card = n → ⊥ ∈ (s ∪ {⊥}) := by
    intro s
    intro n
    induction n with
    | zero =>
      intro h
      simp at h
      simp[h]
    | succ n ih =>
      intro h
      simp

  def two (h: ∀s : Finset (Formula ℒₜ ℕ), ∀n, s.card = n → ⊥ ∈ (s ∪ {⊥})) : ∀Γ : Finset (Formula ℒₜ ℕ), ⊥ ∈ (Γ ∪ {⊥}) := by
    intro Γ
    let n : ℕ := Γ.card
    apply h at Γ
    apply Γ at n


  example : ∀s : Multiset (Formula ℒₜ ℕ), ⊥ ∈ (s ∪ {⊥}) := by
    intro s
    induction s.card using Nat.strong_induction_on with
    | h n a =>
      induction n with
      | zero =>

        sorry
      | succ n ih => sorry


  def con_slash_disjunction {th : Set (Formula ℒₜ ℕ)} : ∀Γ,∀Δ, Derivation th Γ Δ → Derivation th {(BoundedFormula.iInf (mapping Γ))} {(BoundedFormula.iSup (mapping Δ))} := by

    sorry

  /-- Builds tau from a Finset of formulas -/
  -- def build_tau : Set Fml → Fml := sorry


  def translation {Γ Δ : Finset (Formula ℒₜ ℕ)} (ha : ∀f ∈ Γ, contains_T f) (hb : ∀f ∈ Δ, contains_T f) : Derivation 𝐓𝐁 Γ Δ  → Derivation real_PA Γ Δ
    | .tax (h : ∃f : Formula ℒₜ ℕ, f ∈ 𝐓𝐁 ∧ f ∈ Δ) => by
      have step1 : ∃f : Formula ℒₜ ℕ, f ∈ real_PA ∧ f ∈ Δ := by
        rcases h with ⟨f, a₁, a₂⟩
        have step2 : contains_T f := by
          apply hb at a₂
          exact a₂
        have step3 : f ∈ real_PA := by
          rw[real_PA]
          simp
          apply And.intro a₁ step2
        have step4 : f ∈ real_PA ∧ f ∈ Δ := by
          apply And.intro step3 a₂
        apply Exists.intro f step4
      apply Derivation.tax step1
    | .lax (h : (Γ ∩ Δ) ≠ ∅) => Derivation.lax h
    | .left_conjunction A B S (h₁ : Derivation 𝐓𝐁 S Δ) (h₂ : A ∈ S) (h₃ : B ∈ S) (h₄ : Γ = (((S \ {A}) \ {B}) ∪ {A ∧' B})) => sorry
    | .left_disjunction A B S₁ S₂ S₃ (h₁ : Derivation 𝐓𝐁 S₁ Δ) (h₂ : S₁ = S₃ ∪ {A}) (h₃ : Derivation 𝐓𝐁 S₂ Δ) (h₄ : S₂ = S₃ ∪ {B}) (h₅ : Γ = S₃ ∪ {A ∨' B}) => sorry
    | .left_implication A B S₁ S₂ S₃ (d₁ : Derivation 𝐓𝐁 S₁ S₂) (h₁ : S₂ = Δ ∪ {A}) (d₂ : Derivation 𝐓𝐁 S₃ Δ) (h₂ : S₃ = {B} ∪ S₁) (h₃ : Γ = S₁ ∪ {A ⟹ B}) => sorry
    | .left_bot (h : ⊥ ∈ Γ) => Derivation.left_bot h
    | .right_conjunction A B S₁ S₂ S₃ (d₁ : Derivation 𝐓𝐁 Γ S₁) (h₁ : S₁ = S₃ ∪ {A}) (d₂ : Derivation 𝐓𝐁 Γ S₂) (h₂ : S₂ = S₃ ∪ {B}) (h₃ : Δ = S₃ ∪ {A ∧' B}) => sorry
    | .right_disjunction A B S (d₁ : Derivation 𝐓𝐁 Γ S) (h₁ : Δ = (S \ {A, B}) ∪ {A ∨' B}) => sorry
    | .right_implication A B S₁ S₂ S₃ (d₁ : Derivation 𝐓𝐁 S₁ S₂) (h₁ : S₁ = {A} ∪ Γ) (h₂ : S₂ = S₃ ∪ {B}) (h₃ : Δ = S₃ ∪ {A ⟹ B}) => sorry
    | .left_forall (A : Formula ℒₜ ℕ) (B) (h₁ : B = A↓) t S (d : Derivation 𝐓𝐁 S Δ) (h₂ : (A/[t]) ∈ S ∧ (∀'B) ∈ S) (h₃ : Γ = S \ {(A/[t])}) => sorry
    | .left_exists A B (S₁ : Set (Formula ℒₜ ℕ)) (p : B = A↓) (d₁ : Derivation 𝐓𝐁 ((S₁↑) ∪ {A}) (Δ↑)) (h₁ : Γ = S₁ ∪ {∃' B}) => sorry
    | .right_forall A B S (p : B = A↓) (d₁ : Derivation 𝐓𝐁 (Γ↑) ((S↑) ∪ {A})) (h₁ : Δ = S ∪ {∀'B}) => sorry
    | .right_exists (A : Formula ℒₜ ℕ) B t S (p : B = A↓) (d₁ : Derivation 𝐓𝐁 Γ (S ∪ {∃'B, A/[t]})) (h₁ : Δ = S ∪ {∃'B}) => sorry
    | .cut A S₁ S₂ S₃ S₄ (d₁ : Derivation 𝐓𝐁 S₁ (S₂ ∪ {A})) (d₂ : Derivation 𝐓𝐁 ({A} ∪ S₃) S₄) (h₁ : Γ = S₁ ∪ S₃) (h₂ : Δ = S₂ ∪ S₄) => sorry

  -- theorem conservativity_of_tb : ∀f ∈ real_LPA, (𝐓𝐁 ⊢ f) → (real_PA ⊢ f) := by
  -- intro f
  -- intro mem
  -- intro h
  -- rw[formula_provable,sequent_provable]
  -- apply Nonempty.intro
  -- rw[formula_provable,sequent_provable] at h
  -- apply Classical.choice at h
  -- have step1 : ∀f : Formula ℒₜ ℕ, f ∈ emptyFormSet → not_contains_T f := by
  --   rw[emptyFormSet]
  --   intro h₁
  --   intro h₂
  --   simp at h₂
  -- have step2 : ∀f : Formula ℒₜ ℕ, f ∈ emptyFormSet ∪ {f} → not_contains_T f := by

  -- simp[th_to_set_form] at h
  -- apply Classical.choice

end Conservativity

namespace Hidden
  open Languages
  open L_T
  open Calculus

  def f₁ : Formula ℒₜ ℕ :=
    ∀' (&0 =' &0)
  def f₃ : Formula ℒₜ ℕ := ⊥
  def f₂ : Formula ℒₜ ℕ :=
    (T(⌜f₃⌝) ⇔ f₁)
  def S₁ : Set (Formula ℒₜ ℕ) := {f₁, f₂}
  def S₂ : Finset (Formula ℒₜ ℕ) := ∅
  def S₃ : Finset (Formula ℒₜ ℕ) := {f₁ ∨' f₂}
  def der₁ : Derivation S₁ S₂ S₃ := by
    let S₄ : Finset (Formula ℒₜ ℕ) := {f₁, f₂}
    have step1 : f₁ ∈ S₁ ∧ f₁ ∈ S₄ := by
      simp[S₁,S₄]
    have step2 : ∃f, f ∈ S₁ ∧ f ∈ S₄ := by
      apply Exists.intro f₁ step1
    have step3 : Derivation S₁ S₂ S₄ := by
      simp[S₁,S₂,S₄]
      apply Derivation.tax step2
    have step4 : S₃ = (S₄ \ {f₁, f₂}) ∪ {f₁ ∨' f₂} := by
      simp[S₃,S₄]
    have step5 : Derivation S₁ S₂ S₃ := by
      simp[S₁,S₂,S₃]
      apply Derivation.right_disjunction f₁ f₂ S₄ step3 step4
    exact step5

  open Conservativity
  #eval der_to_finset_fml der₁
  -- #eval (transform_to_tau_disjuncts (get_disq_sents (der_to_finset_fml der₁)))

  inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

def head {α} : {n : Nat} → Vector α (n+1) → α
  | n, Vector.cons a as => a

def tail {α} : {n : Nat} → Vector α (n+1) → Vector α n
  | n, Vector.cons a as => as

  theorem eta {α} : ∀ {n : Nat} (v : Vector α (n+1)), Vector.cons (head v) (tail v) = v
  | n, Vector.cons a as => rfl

  def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]

  #eval northernTrees.append #["yeah"]
end Hidden

variable {L : Language}

@[elab_as_elim]
def cases' {C : ∀ n, BoundedFormula L α n → Sort w}
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hequal  : ∀ {n : ℕ} (t₁ t₂ : Term L (α ⊕ Fin n)), C n (t₁ =' t₂))
  (hrel    : ∀ {n k : ℕ} (r : L.Relations k) (v : Fin k → Term L (α ⊕ Fin n)), C n (.rel r v))
  (hall    : ∀ {n : ℕ} (φ : BoundedFormula L α (n + 1)), C n (∀' φ))
  (himp    : ∀ {n : ℕ} (φ ψ : BoundedFormula L α n), C n (φ ⟹ ψ)) :
    ∀ {n : ℕ} (φ : BoundedFormula L α n), C n φ
  | _, .falsum   => hfalsum
  | _, .rel r v  => hrel r v
  | _, .all φ    => hall φ
  | _, .imp f₁ f₂ => himp f₁ f₂
  | _, .equal t₁ t₂ => hequal t₁ t₂
