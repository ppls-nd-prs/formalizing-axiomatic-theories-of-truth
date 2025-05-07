import FormalizingAxiomaticTheoriesOfTruth.ProofTheory
import Mathlib.Logic.Encodable.Basic
import Mathlib.Computability.Encoding
import Mathlib.Logic.Equiv.List
import Mathlib.ModelTheory.Complexity

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

  -- def real_PA : Set (Formula ℒₜ ℕ) := {f | f ∈ 𝐓𝐁 ∧ (contains_T f)}
  def real_LPA : Set (Formula ℒₜ ℕ) := {f | f ∈ Set.univ ∧ (contains_T f)}
  open LPA
  instance : Coe (Set (Formula ℒ ℕ)) (Set (Formula ℒₜ ℕ)) where
    coe S := ϕ.onFormula '' S
  /- Need to define -/
  /- ALSO TODO define a set translation coercion for sets of formula in ℒ
  to sets of formulas in ℒₜ -/

  variable {L : Language} {Th : Set (Formula L ℕ)}[∀n, DecidableEq (L.Functions n)][∀p, DecidableEq (L.Relations p)]
  /-- Obtains a Finset of all formulas that occur in some derivation -/
  @[simp]
  def fmls {Δ Γ} : Derivation Th Δ Γ → Finset (Formula L ℕ)
    | .tax _ => Δ ∪ Γ
    | .lax _ => Δ ∪ Γ
    | .left_conjunction _ _ _ d _ _ _ => (fmls d) ∪ Δ ∪ Γ
    | .left_disjunction _ _ _ _ _ d₁ _ d₂ _ _ => (fmls d₁) ∪ (fmls d₂) ∪ Δ ∪ Γ
    | .left_implication _ _ _ _ _ d₁ _ d₂ _ _ => (fmls d₁) ∪ (fmls d₂) ∪ Δ ∪ Γ
    | .left_bot _ => Δ ∪ Γ
    | .right_conjunction _ _ _ _ _ d₁ _ d₂ _ _ => (fmls d₁) ∪ (fmls d₂) ∪ Δ ∪ Γ
    | .right_disjunction _ _ _ d _ => (fmls d) ∪ Δ ∪ Γ
    | .right_implication _ _ _ _ _ d _ _ _ => (fmls d) ∪ Δ ∪ Γ
    | .left_forall _ _ _ _ _ d _ _ => (fmls d) ∪ Δ ∪ Γ
    | .left_exists _ _ _ _ d _ => (fmls d) ∪ Δ ∪ Γ
    | .right_forall _ _ _ _ d _ => (fmls d) ∪ Δ ∪ Γ
    | .right_exists _ _ _ _ _ d _ => (fmls d) ∪ Δ ∪ Γ
    | .cut _ _ _ _ _ d₁ d₂ _ _ => (fmls d₁) ∪ (fmls d₂) ∪ Δ ∪ Γ

  /-- Obtain a finset that contains only the formula containing a T from a finset -/
  @[simp]
  def get_T_fmls (S : Finset (Formula ℒₜ ℕ)) : Finset (Formula ℒₜ ℕ) :=
    {f ∈ S | contains_T f}

  /-- Obtains all disquotation sentences in a finset -/
  @[simp]
  def get_disq_sents (S : Finset (Formula ℒₜ ℕ)) : Finset (Formula ℒₜ ℕ) :=
    {f ∈ S | is_disq_sent f}

  @[simp]
  def get_disq_sent_fmls (S: Finset (Formula ℒₜ ℕ)) : Finset (Formula ℒₜ ℕ) :=

    sorry

  /-- Transforms a disquotation axiom to the corresponding tau disjunct -/
  @[simp]
  def disq_to_tau : BoundedFormula ℒₜ ℕ 0 → BoundedFormula ℒₜ ℕ 0
  | (((.rel L_T.Rel.t ts₁ ⟹ f₁) ⟹ ((f₂ ⟹ .rel L_T.Rel.t ts₂) ⟹ ⊥)) ⟹ ⊥) =>
    #0 =' ⌜f₁⌝ ⇔ f₁
  | _ => ⊥

  -- def f₅ : Formula ℒₜ ℕ := (((.rel L_T.Rel.t ![⌜⊥⌝] ⟹ ⊥) ⟹ ((f₂ ⟹ .rel L_T.Rel.t ts₂) ⟹ ⊥)) ⟹ ⊥)
  -- #eval disq_to_tau

  /-- transforms all disquotation axioms in a given Finset to their corresponding tau disjunct -/
  @[simp]
  def transform_to_tau_disjuncts (S : Finset (Formula ℒₜ ℕ)): (Finset (Formula ℒₜ ℕ)) :=
    S.image disq_to_tau

  /-- mapping necessary for glueing together all disjuncts into one big disjunction -/
  @[simp]
  def mapping (s : Finset (BoundedFormula ℒₜ ℕ 0)) : { x : (BoundedFormula ℒₜ ℕ 0) // x ∈ s} → (BoundedFormula ℒₜ ℕ 0) := fun i => i.val

  /-- takes a set of disjuncts to their disjunction -/
  @[simp]
  noncomputable def disjuncts_to_disjunction (S : Finset (Formula ℒₜ ℕ)) : Formula ℒₜ ℕ :=
    BoundedFormula.iSup (mapping S)

  variable {th : Set (Formula ℒₜ ℕ)}
  /-- takes a derivation and builds the corresponding tau formula -/
  @[simp]
  noncomputable def build_tau {Γ Δ} (d : Derivation th Γ Δ) : Formula ℒₜ ℕ :=
    disjuncts_to_disjunction (transform_to_tau_disjuncts (get_disq_sents (fmls d)))

  notation "τ(" d ")" => build_tau d

  open BoundedFormula
  def tau_disj_phi_func (d : Derivation th Γ Δ) (f : ℒₜ.Formula ℕ) (h : f ∈ (fmls d)) : Derivation th ∅ {((τ(d))/[⌜f⌝] ⇔ f)} := by
    simp
    sorry
  lemma tau_disj_phi {th} :∀Γ, ∀Δ, ∀d : Derivation th Γ Δ, ∀f ∈ (fmls d), Nonempty (Derivation th ∅ {((τ(d))/[⌜f⌝] ⇔ f)}) := by
    intro Γ Δ
    induction Γ using Finset.induction_on with
    | empty =>
      intro d f mem

      sorry
    | insert a ih => sorry
    induction d with
    | tax h =>


      sorry
    | lax h => sorry
    | left_conjunction A B S d₁ h₁ h₂ h₃ ih => sorry
    | left_disjunction A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ ih₁ ih₂ => sorry
    | left_implication A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ ih₁ ih₂ => sorry
    | left_bot h => sorry
    | right_conjunction A B S₁ S₂ S₃ d₁ h₁ d₂ h₂ h₃ ih₁ ih₂ => sorry
    | right_disjunction A B S d₁ h₁ ih₁ => sorry
    | right_implication A B S₁ S₂ S₃ d₁ h₁ h₂ h₃ ih₁ => sorry
    | left_forall A B h₁ t S d h₂ h₃ ih₁ => sorry
    | left_exists A B S₁ p d₁ h₁ ih₁ => sorry
    | right_forall A B S p d₁ h₁ ih₁ => sorry
    | right_exists A B t S p d₁ h₁ ih₁ => sorry
    | cut A S₁ S₂ S₃ S₄ d₁ d₂ h₁ h₂ ih₁ ih₂ => sorry


  def f₂ : Formula ℒₜ ℕ := ⊥
  -- #eval BoundedFormula.Realize f₂ id id
  -- def le : BoundedFormula L α n → BoundedFormula L α n :=
  -- instance : LinearOrder (BoundedFormula L α n) where
  --   le a b :=
#check @Max.left_comm (BoundedFormula ℒₜ ℕ 0)

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



  #check Multiset.card

  open Term
  open Computability
  open BoundedFormula
  open TermEncoding
  def Γ_encode : ((k : ℕ) × ℒₜ.Term (ℕ ⊕ Fin k) ⊕ (n : ℕ) × ℒₜ.Relations n ⊕ ℕ) → ℕ
    | .inl (.mk k t) => Nat.pair 0 (Nat.pair k (instEncodableOfSigmaNatFunctions.encode t))
    | .inr (.inl (.mk p R)) => Nat.pair 1 (Nat.pair p (L_T.enc_r.encode R))
    | .inr (.inr n) => Nat.pair 2 n

  def L_T.dflt_Rel : ℒₜ.Relations 1 := L_T.Rel.t
  def dflt_term : ℒₜ.Term (ℕ ⊕ Fin n) := #0

  -- def opt_opt_to_opt {β : Type} : Option (Σk, Option (ℒₜ.Term (ℕ ⊕ Fin k)) ⊕ β) → Option (Σk, (ℒₜ.Term (ℕ ⊕ Fin k)))
  --   | some (Sum.inl (Sigma.mk k (some t))) => some (Sum.inl (Sigma.mk k t))

  def Γ_decode : ℕ → Option ((k : ℕ) × ℒₜ.Term (ℕ ⊕ Fin k) ⊕ (n : ℕ) × ℒₜ.Relations n ⊕ ℕ) :=
    fun n => match n.unpair.1, n.unpair.2.unpair with
    | 0, ⟨k, e⟩ =>
      some ((Sum.inl (Sigma.mk k ((instEncodableOfSigmaNatFunctions.decode e).getD dflt_term))))
    | 1, m =>
      match m with
      | ⟨1, R⟩ => some (Sum.inr (Sum.inl (Sigma.mk 1 ((L_T.enc_r.decode R).getD L_T.dflt_Rel))))
      | ⟨_, _⟩ => none
    | 2, m =>
      some (Sum.inr (Sum.inr (m.1.pair m.2)))
    | _, _ => none

  lemma Γ_encodek : ∀ f : BoundedFormula.encoding.Γ, Γ_decode (Γ_encode f) = (some f) := by
    intro h
    cases h with
    | inl a =>
      cases a with
      | mk k t =>
        simp[Γ_encode,Γ_decode]
    | inr a =>
      cases a with
      | inl s =>
        cases s with
        | mk n R =>
          match n with
            | Nat.zero =>
              cases R
            | Nat.succ Nat.zero =>
              simp[Γ_encode,Γ_decode]
            | Nat.succ (Nat.succ _) =>
              cases R
      | inr n =>
        simp[Γ_encode,Γ_decode]

  /- Encodable ((k : ℕ) × ℒₜ.Term (ℕ ⊕ Fin k) ⊕ (n : ℕ) × ℒₜ.Relations n ⊕ ℕ) -/
  instance : Encodable ((@BoundedFormula.encoding ℒₜ ℕ).Γ) where
    encode := Γ_encode
    decode := Γ_decode
    encodek := Γ_encodek

  def dflt_list : List ((Σk, ℒₜ.Term (ℕ ⊕ Fin k)) ⊕ ((Σ n, ℒₜ.Relations n) ⊕ ℕ)) := []

  instance : Encodable (Σk, BoundedFormula ℒₜ ℕ k) where
    encode := fun p => Encodable.encode (BoundedFormula.encoding.encode p)
    decode := fun n => ((Encodable.decode n).map BoundedFormula.encoding.decode).join
    encodek := by
      intro h
      simp
      apply BoundedFormula.encoding.decode_encode at h
      apply h



  def f₁ : Formula ℒₜ ℕ := ⊥
  #check Encodable.encodeList (BoundedFormula.listEncode f₁)
  #check Max.max f₁ f₁
  def f₅ : Formula ℒₜ ℕ := #0 =' #0
  #eval Max.max f₁ f₅
  example : Max.max f₁ f₅ = f₁ ∨' f₅ := by rfl

  -- #check Formula.realize_top.mp ⊤.Realize

  -- variable {M : Type _}[L.Structure M]{α : Type _}{v : α → M}
  -- instance struct : Structure ℒₜ ℕ where
  --   funMap := structure_fun
  --   RelMap := sorry
  -- def f₉ : Formula ℒₜ ℕ := ⊤
  -- def mapp : ℕ → ℕ := id
  -- example : f₉.Realize mapp := by

  -- #check Formula.realize_top.mp (f₉.Realize mapp)
  -- instance : LinearOrder (BoundedFormula ℒₜ ℕ 0) where
  --   le := le_bf
  --   lt := lt_bf
  --   le_refl := by
  --     simp[le_bf]
  --   le_trans := by
  --     simp[le_bf,number,toString,String.length]
  --     intro f₁ f₂ f₃
  --     intro h₁ h₂

  -- @[simp]
  -- def number : (Σn, BoundedFormula ℒₜ ℕ n) → ℕ :=
  --   fun f => Encodable.encodeList (BoundedFormula.encoding.encode f)

  -- @[simp]
  -- def le_bf : BoundedFormula ℒₜ ℕ 0 → BoundedFormula ℒₜ ℕ 0 → Prop :=
  --   fun f₁ f₂ => (number f₁) ≤ (number f₂)

  -- @[simp]
  -- def lt_bf : Formula ℒₜ ℕ → Formula ℒₜ ℕ → Prop :=
  --   fun f₁ f₂ => (number f₁) < (number f₂)


  -- instance : LE (ℒₜ.Formula ℕ) where
  --   le := le_bf
  -- instance : LT (ℒₜ.Formula ℕ) where
  --   lt := lt_bf

  -- def f₁ : ℒₜ.BoundedFormula ℕ 0 := .falsum
  -- open L_T

  -- variable {α} [Encodable (BoundedFormula.encoding.Γ)]
  #check BoundedFormula.encoding.Γ
  #check Encodable.encodeList (BoundedFormula.encoding.encode ⟨0,f₁⟩)
  #eval Encodable.encodeList (BoundedFormula.encoding.encode ⟨0, f₁⟩)
  open List
  /-- An encoding of bounded formulas as lists. -/
@[simp]
protected def encoding : Encoding (Σ n, L.BoundedFormula α n) where
  Γ := (Σk, L.Term (α ⊕ Fin k)) ⊕ ((Σ n, L.Relations n) ⊕ ℕ)
  encode φ := φ.2.listEncode
  decode l := (listDecode l)[0]?
  decode_encode φ := by
    have h := listDecode_encode_list [φ]
    rw [flatMap_singleton] at h
    simp only
    rw [h]
    rfl
  -- def f₁_sigma : Σn, ℒₜ.BoundedFormula ℕ n :=
  -- #check Encodable.encodeList (BoundedFormula.encoding.encode (Σn, f₁))


  def big_disjunction : (s : Multiset (ℒₜ.Formula ℕ)) → ℒₜ.Formula ℕ :=
    fun S => by
    induction S using Multiset.recOn with
    | C_0 => apply BoundedFormula.falsum
    | C_cons a M b =>
      apply big_disjunction at M
      apply BoundedFormula.lor M
      exact a
    | C_cons_heq a b M c =>
      simp
      sorry


  open BoundedFormula

  lemma three : ∀S₁:Finset (ℒₜ.Formula ℕ),∀S₂:Finset (ℒₜ.Formula ℕ), ⊥ ∈ S₁ → ⊥ ∈ (S₁ ∪ S₂) := by
    intro S₁ S₂ h₁
    induction S₁ using Finset.induction_on with
    | empty =>
      simp at h₁
    | insert a ih =>
      simp
      simp at h₁ ih
      cases h₁ with
      | inl a =>
        simp[a]
      | inr a =>
        simp[a]

  #eval instEncodableSigmaNatBoundedFormulaℒₜ.encode ⟨0, f₁⟩

  variable  {L : Language} {M : Type w} [L.Structure M] {α : Type u'} {l : ℕ} {φ ψ : L.BoundedFormula α l} {v : α → M} {xs : Fin l → M}

  @[simp]
  def number (f : ℒₜ.BoundedFormula ℕ 0) : ℕ :=  instEncodableSigmaNatBoundedFormulaℒₜ.encode ⟨0,f⟩

  def number_alternative (f : ℒₜ.BoundedFormula ℕ 0) : Prop :=  f.Realize v xs

  variable {a b c : Prop}
  example : a → (b → c) = b → (a → c) := by
    simp
    intro h₁ h₂
    sorry

  @[simp]
  instance instLE : LE (ℒₜ.BoundedFormula ℕ 0) where
    le := fun f₁ f₂ => (number f₁) ≤ (number f₂)

  @[simp]
  instance instLT : LT (ℒₜ.BoundedFormula ℕ 0) where
    lt := fun f₁ f₂ => (number f₁) < (number f₂)

  @[simp]
  instance instDecLE : DecidableLE (ℒₜ.BoundedFormula ℕ 0) := by
    simp[DecidableLE,DecidableRel]
    intro f₁ f₂
    apply Nat.decLe

instance instMin : Min (BoundedFormula ℒₜ ℕ 0) where
  min := fun f₁ f₂ => if (number f₁) ≤ (number f₂) then f₁ else f₂
instance instMax : Max (BoundedFormula ℒₜ ℕ 0) where
  max := fun f₁ f₂ => if (number f₁) ≤ (number f₂) then f₂ else f₁

  instance : LinearOrder (BoundedFormula ℒₜ ℕ 0) where
    le := instLE.le
    lt := instLT.lt
    le_refl := by
      simp
    le_trans := by
      simp[number]
      intro f₁ f₂ f₃
      intro h₁ h₂
      apply Nat.le_trans at h₁
      apply h₁ at h₂
      exact h₂
    le_antisymm := by
      intro f₁ f₂ h₁ h₂
      apply Nat.instLinearOrder.le_antisymm at h₁
      apply h₁ at h₂
      simp at h₂
      exact h₂
    le_total := by
      simp[Nat.instLinearOrder.le_total]
    decidableLE := instDecLE
    lt_iff_le_not_le := by
      intro f₁ f₂
      apply Iff.intro
      intro h₁
      apply Nat.lt_iff_le_and_not_ge.mp at h₁
      exact h₁
      intro h₁
      apply Nat.lt_iff_le_and_not_ge.mpr at h₁
      exact h₁
    min_def := by
      intro f₁ f₂
      simp
      rfl
    max_def := by
      intro f₁ f₂
      simp
      rfl

-- def left_comm_max (a b c : BoundedFormula ℒₜ ℕ 0) : max a (max b c) = max b (max a c):= by
--   rw[Max.left_comm a b c]

-- instance : LeftCommutative (@max (BoundedFormula ℒₜ ℕ 0) BoundedFormula.instMax) where
--   left_comm := left_comm_max

noncomputable def iSupp (s : Finset (β)) (f : β → ℒₜ.BoundedFormula ℕ 0) : ℒₜ.BoundedFormula ℕ 0 :=
  (s.toList.map f).foldr (· ⊔ ·) ⊥

def tau

def iSup (f : Finset (ℒₜ.Formula ℕ)) : ℒₜ.BoundedFormula ℕ 0 :=
  f.1.fold (· ⊔ ·) ⊥

def iInf (f : Finset (ℒₜ.Formula ℕ)) : ℒₜ.BoundedFormula ℕ 0 :=
  f.1.fold (· ⊓ ·) ⊥

def f₃ : ℒₜ.Formula ℕ := #0 =' #0
def s₃ : Finset (ℒₜ.Formula ℕ) := {f₃,f₃}
#eval number f₃ -- output : 11
#eval number ⊥ -- output : 73
#eval iSup s₃ -- output: ⊥
#eval iInf s₃ -- output: #0 = #0

def l₁ : List (ℒₜ.Formula ℕ) := [f₃,f₃]
def s₄ : Finset (ℒₜ.Formula ℕ) := Multiset.toFinset l₁
#eval s₄
#check s₄
def m₁ : Multiset (ℒₜ.Formula ℕ) := l₁
#eval m₁
-- def f₆ : ℒₜ.Formula ℕ := m₁.fold ∨' _ _

lemma id_all : ∀ (a b : List (ℒₜ.Formula ℕ)), a ≈ b → id a = id b := by
  intro a b h₁
  simp
  sorry
#check ⊔
variable (a b : List (ℒₜ.Formula ℕ))
#check id a

def l₅ : List Nat := [1,2,3,4]
def m₂ : Multiset Nat := l₅

-- #check Quotient.lift + _ m₂
-- #eval Quotient.lift id _ s₃.1

def func : Finset (ℒₜ.Formula ℕ) → List (ℒₜ.Formula ℕ) :=
  fun s => match s.1 with
  | a => by

    sorry

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

  -- lemma one : ∀s : Finset (Formula ℒₜ ℕ), ∀n, s.card = n → ⊥ ∈ (s ∪ {⊥}) := by
  --   intro s
  --   intro n
  --   induction n with
  --   | zero =>
  --     intro h
  --     simp at h
  --     simp[h]
  --   | succ n ih =>
  --     intro h
  --     simp

  def two (h: ∀s : Finset (Formula ℒₜ ℕ), ∀n, s.card = n → ⊥ ∈ (s ∪ {⊥})) : ∀Γ : Finset (Formula ℒₜ ℕ), ⊥ ∈ (Γ ∪ {⊥}) := by
    intro Γ
    let n : ℕ := Γ.card
    apply h at Γ
    apply Γ at n
    sorry


  -- example : ∀s : Multiset (Formula ℒₜ ℕ), ⊥ ∈ (s ∪ {⊥}) := by
  --   intro s
  --   induction s.card using Nat.strong_induction_on with
  --   | h n a =>
  --     induction n with
  --     | zero => sorry
  --     | succ n ih => sorry


  def con_slash_disjunction {th : Set (Formula ℒₜ ℕ)} : ∀Γ,∀Δ, Derivation th Γ Δ → Derivation th {(BoundedFormula.iInf (mapping Γ))} {(BoundedFormula.iSup (mapping Δ))} := by

    sorry

  /- Builds tau from a Finset of formulas -/
  -- def build_tau : Set Fml → Fml := sorry


  -- def translation {Γ Δ : Finset (Formula ℒₜ ℕ)} (ha : ∀f ∈ Γ, contains_T f) (hb : ∀f ∈ Δ, contains_T f) : Derivation 𝐓𝐁 Γ Δ  → Derivation real_PA Γ Δ
  --   | .tax (h : ∃f : Formula ℒₜ ℕ, f ∈ 𝐓𝐁 ∧ f ∈ Δ) => by
  --     have step1 : ∃f : Formula ℒₜ ℕ, f ∈ real_PA ∧ f ∈ Δ := by
  --       rcases h with ⟨f, a₁, a₂⟩
  --       have step2 : contains_T f := by
  --         apply hb at a₂
  --         exact a₂
  --       have step3 : f ∈ real_PA := by
  --         rw[real_PA]
  --         simp
  --         apply And.intro a₁ step2
  --       have step4 : f ∈ real_PA ∧ f ∈ Δ := by
  --         apply And.intro step3 a₂
  --       apply Exists.intro f step4
  --     apply Derivation.tax step1
  --   | .lax (h : (Γ ∩ Δ) ≠ ∅) => Derivation.lax h
  --   | .left_conjunction A B S (h₁ : Derivation 𝐓𝐁 S Δ) (h₂ : A ∈ S) (h₃ : B ∈ S) (h₄ : Γ = (((S \ {A}) \ {B}) ∪ {A ∧' B})) => sorry
  --   | .left_disjunction A B S₁ S₂ S₃ (h₁ : Derivation 𝐓𝐁 S₁ Δ) (h₂ : S₁ = S₃ ∪ {A}) (h₃ : Derivation 𝐓𝐁 S₂ Δ) (h₄ : S₂ = S₃ ∪ {B}) (h₅ : Γ = S₃ ∪ {A ∨' B}) => sorry
  --   | .left_implication A B S₁ S₂ S₃ (d₁ : Derivation 𝐓𝐁 S₁ S₂) (h₁ : S₂ = Δ ∪ {A}) (d₂ : Derivation 𝐓𝐁 S₃ Δ) (h₂ : S₃ = {B} ∪ S₁) (h₃ : Γ = S₁ ∪ {A ⟹ B}) => sorry
  --   | .left_bot (h : ⊥ ∈ Γ) => Derivation.left_bot h
  --   | .right_conjunction A B S₁ S₂ S₃ (d₁ : Derivation 𝐓𝐁 Γ S₁) (h₁ : S₁ = S₃ ∪ {A}) (d₂ : Derivation 𝐓𝐁 Γ S₂) (h₂ : S₂ = S₃ ∪ {B}) (h₃ : Δ = S₃ ∪ {A ∧' B}) => sorry
  --   | .right_disjunction A B S (d₁ : Derivation 𝐓𝐁 Γ S) (h₁ : Δ = (S \ {A, B}) ∪ {A ∨' B}) => sorry
  --   | .right_implication A B S₁ S₂ S₃ (d₁ : Derivation 𝐓𝐁 S₁ S₂) (h₁ : S₁ = {A} ∪ Γ) (h₂ : S₂ = S₃ ∪ {B}) (h₃ : Δ = S₃ ∪ {A ⟹ B}) => sorry
  --   | .left_forall (A : Formula ℒₜ ℕ) (B) (h₁ : B = A↓) t S (d : Derivation 𝐓𝐁 S Δ) (h₂ : (A/[t]) ∈ S ∧ (∀'B) ∈ S) (h₃ : Γ = S \ {(A/[t])}) => sorry
  --   | .left_exists A B (S₁ : Set (Formula ℒₜ ℕ)) (p : B = A↓) (d₁ : Derivation 𝐓𝐁 ((S₁↑) ∪ {A}) (Δ↑)) (h₁ : Γ = S₁ ∪ {∃' B}) => sorry
  --   | .right_forall A B S (p : B = A↓) (d₁ : Derivation 𝐓𝐁 (Γ↑) ((S↑) ∪ {A})) (h₁ : Δ = S ∪ {∀'B}) => sorry
  --   | .right_exists (A : Formula ℒₜ ℕ) B t S (p : B = A↓) (d₁ : Derivation 𝐓𝐁 Γ (S ∪ {∃'B, A/[t]})) (h₁ : Δ = S ∪ {∃'B}) => sorry
  --   | .cut A S₁ S₂ S₃ S₄ (d₁ : Derivation 𝐓𝐁 S₁ (S₂ ∪ {A})) (d₂ : Derivation 𝐓𝐁 ({A} ∪ S₃) S₄) (h₁ : Γ = S₁ ∪ S₃) (h₂ : Δ = S₂ ∪ S₄) => sorry

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

-- namespace Hidden
--   open Languages
--   open L_T
--   open Calculus

--   def f₁ : Formula ℒₜ ℕ :=
--     ∀' (&0 =' &0)
--   def f₃ : Formula ℒₜ ℕ := ⊥
--   def f₂ : Formula ℒₜ ℕ :=
--     (T(⌜f₃⌝) ⇔ f₁)
--   def S₁ : Set (Formula ℒₜ ℕ) := {f₁, f₂}
--   def S₂ : Finset (Formula ℒₜ ℕ) := ∅
--   def S₃ : Finset (Formula ℒₜ ℕ) := {f₁ ∨' f₂}
--   def der₁ : Derivation S₁ S₂ S₃ := by
--     let S₄ : Finset (Formula ℒₜ ℕ) := {f₁, f₂}
--     have step1 : f₁ ∈ S₁ ∧ f₁ ∈ S₄ := by
--       simp[S₁,S₄]
--     have step2 : ∃f, f ∈ S₁ ∧ f ∈ S₄ := by
--       apply Exists.intro f₁ step1
--     have step3 : Derivation S₁ S₂ S₄ := by
--       simp[S₁,S₂,S₄]
--       apply Derivation.tax step2
--     have step4 : S₃ = (S₄ \ {f₁, f₂}) ∪ {f₁ ∨' f₂} := by
--       simp[S₃,S₄]
--     have step5 : Derivation S₁ S₂ S₃ := by
--       simp[S₁,S₂,S₃]
--       apply Derivation.right_disjunction f₁ f₂ S₄ step3 step4
--     exact step5

--   open Conservativity
--   #eval der_to_finset_fml der₁
--   -- #eval (transform_to_tau_disjuncts (get_disq_sents (der_to_finset_fml der₁)))

--   inductive Vector (α : Type u) : Nat → Type u
--   | nil  : Vector α 0
--   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

-- def head {α} : {n : Nat} → Vector α (n+1) → α
--   | n, Vector.cons a as => a

-- def tail {α} : {n : Nat} → Vector α (n+1) → Vector α n
--   | n, Vector.cons a as => as

--   theorem eta {α} : ∀ {n : Nat} (v : Vector α (n+1)), Vector.cons (head v) (tail v) = v
--   | n, Vector.cons a as => rfl

--   def northernTrees : Array String :=
--   #["sloe", "birch", "elm", "oak"]

--   #eval northernTrees.append #["yeah"]
-- end Hidden

-- variable {L : Language}

-- @[elab_as_elim]
-- def cases' {C : ∀ n, BoundedFormula L α n → Sort w}
--   (hfalsum : ∀ {n : ℕ}, C n ⊥)
--   (hequal  : ∀ {n : ℕ} (t₁ t₂ : Term L (α ⊕ Fin n)), C n (t₁ =' t₂))
--   (hrel    : ∀ {n k : ℕ} (r : L.Relations k) (v : Fin k → Term L (α ⊕ Fin n)), C n (.rel r v))
--   (hall    : ∀ {n : ℕ} (φ : BoundedFormula L α (n + 1)), C n (∀' φ))
--   (himp    : ∀ {n : ℕ} (φ ψ : BoundedFormula L α n), C n (φ ⟹ ψ)) :
--     ∀ {n : ℕ} (φ : BoundedFormula L α n), C n φ
--   | _, .falsum   => hfalsum
--   | _, .rel r v  => hrel r v
--   | _, .all φ    => hall φ
--   | _, .imp f₁ f₂ => himp f₁ f₂
--   | _, .equal t₁ t₂ => hequal t₁ t₂
