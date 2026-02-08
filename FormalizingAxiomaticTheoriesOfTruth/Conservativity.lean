import FormalizingAxiomaticTheoriesOfTruth.BasicTheories
import FormalizingAxiomaticTheoriesOfTruth.ProofTheory
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Semantics

open FirstOrder
open Language
open BoundedFormula
open Languages
open LPA
open Induction

namespace Conservativity
  open Languages LPA L_T FirstOrder.Language.BoundedFormula
  variable {α : Type}{n : Nat}
  @[simp]
  def subs_t : {n : ℕ} →  ({m : Nat} → {β : Type} → ℒₜ.Term (β ⊕ Fin m) → ℒₜ.BoundedFormula β m) → ℒₜ.BoundedFormula α n → ℒₜ.BoundedFormula α n
  | _, _, .falsum  => .falsum
  | _, _, .equal t₁ t₂ => .equal (t₁) (t₂)
  | _, φ, .rel R ts =>
      match R with
      | .t_symbol => (φ (ts 0))
      -- | .var_symbol =>
      --        .rel .var_symbol (fun i => ts i)
      -- | .const_symbol =>
      --        .rel .const_symbol (fun i => ts i)
      -- | .term_symbol =>
      --        .rel .term_symbol (fun i => ts i)
      -- | .clterm_symbol =>
      --        .rel .clterm_symbol (fun i => ts i)
      -- | .forml_symbol =>
      --        .rel .forml_symbol (fun i => ts i)
      -- | .sentencel_symbol =>
      --        .rel .sentencel_symbol (fun i => ts i)
      -- | .formlt_symbol =>
      --        .rel .formlt_symbol (fun i => ts i)
      -- | .sentencelt_symbol =>
      --        .rel .sentencelt_symbol (fun i => ts i)
  | _, φ, .imp ψ π => .imp (subs_t φ ψ) (subs_t φ π)
  | _, φ, .all ψ => .all (subs_t φ ψ)

  notation φ"/ₜ["ψ"]" => subs_t ψ φ

  open BoundedFormula Classical
  variable {L : Language}{m : Nat}

  instance : Coe (ℒₜ.Sentence) (ℒₜ.BoundedFormula (Fin 1) n) where
  coe := relabel (fun _ => (.inl 0))

  variable {Th : ℒₜ.Theory}{s : ProofSystem (L := ℒₜ)}[∀n, Encodable (ℒₜ.BoundedFormula Empty n)]

  example (φ : ℒₜ.Sentence) (h : ¬ contains_T φ) : TB.tarski_biconditional φ h = BoundedFormula.falsum := by
    unfold TB.tarski_biconditional BoundedFormula.iff min instMin
    simp
    unfold BoundedFormula.not

    sorry


-- ((rel Rel.t_symbol ![⌜φ⌝] ⟹ φ) ⟹ (φ ⟹ rel Rel.t_symbol ![⌜φ⌝]) ⟹ ⊥) ⟹ ⊥


  variable [∀φ : ℒₜ.Sentence,∀ψ,∀ts₁,∀ts₂, Decidable (ts₁ = ![(⌜φ⌝ : ℒₜ.Term (Empty ⊕ Fin 0))] ∧ ts₁ = ts₂ ∧ φ = ψ)]

  @[simp]
  noncomputable def get_disq_φs {φ : ℒₜ.Sentence} : (p : Proof Th s φ) → List (ℒₜ.Sentence)
  | .ax (((rel Rel.t_symbol ts₁ ⟹ φ₁) ⟹ (φ₂ ⟹ rel Rel.t_symbol ts₂) ⟹ ⊥) ⟹ ⊥) h₁ =>
    (if ts₁ 0 = ⌜φ₁⌝ ∧ ts₁ 0 = ts₂ 0 ∧ φ₁ = φ₂ then [φ₁] else [⊥] )
  | .ax φ h₁ => [⊥]
  | .un p _ h₁ => get_disq_φs p
  | .bi p₁ p₂ _ h₁ => (get_disq_φs p₁) ∪ (get_disq_φs p₂)

  variable [∀n, ∀α, Encodable (ℒₜ.BoundedFormula α n)]

  @[simp]
  def make_tau_equiv (s : ℒₜ.Sentence) : ℒₜ.Formula (Fin 1) := #0 =' ⌜s⌝ ⊓ s

  @[simp]
  def tau_equiv_list (l : List (ℒₜ.Sentence)) : List (ℒₜ.Formula (Fin 1)) := (l.map make_tau_equiv)

  @[simp]
  noncomputable def proof_tau_equiv_list {φ : ℒₜ.Sentence} (p : Proof Th s φ) : List (ℒₜ.Formula (Fin 1)) := (tau_equiv_list (get_disq_φs p))

  open Proof
  @[simp]
  lemma all_list_fin : ∀l : List α, Finite (Fin l.length) := by
    intro l
    apply Finite.intro _
    apply l.length
    rfl

  @[simp]
  noncomputable def tau {φ : ℒₜ.Sentence} (p : Proof Th s φ) : ℒₜ.Formula (Fin 1) :=
    (proof_tau_equiv_list p).foldr (· ⊔ ·) ⊥

end Conservativity

  open Languages L_T
  variable {M : Type w} [ℒₜ.Structure M]
  lemma num_all_v : ∀{n}, ∀{α : Type}, ∀{β : Type}, ∀v : α → ↑M, ∀z : β → ↑M, @Term.realize ℒₜ _ _ _ v (numeral n) = @Term.realize ℒₜ _ _ _ z (numeral n) := by
    intro n α β v z
    induction n with
    | zero =>
      simp[Matrix.empty_eq]
    | succ n ih =>
      unfold numeral
      simp
      rw[ih]

  namespace Conservativity
  open L_T ProofSystem
  variable {L : Language}{Th : ℒₜ.Theory}{α : Type}{n : Nat}[∀n, Encodable (ℒₜ.BoundedFormula Empty n)]{s : ProofSystem}

  variable {M β γ δ: Type}{n : Nat}[ℒₜ.Structure M]{t : β → ↑M}{v : (β ⊕ δ) → ↑M}[Encodable (ℒₜ.BoundedFormula γ n)]

  lemma lem1 : ∀{φ: ℒₜ.Sentence}, Term.realize v (⌜φ⌝ : ℒₜ.Term _) = Term.realize (default : (Empty ⊕ Fin 0) → ↑M) (⌜φ⌝ : ℒₜ.Term _) := by
    intro φ
    induction (Encodable.encode φ) with
    | zero =>
      simp[Matrix.empty_eq]
    | succ n ih =>
      simp[ih]

  lemma lem2 {v : γ → ↑M} : ∀{φ: ℒₜ.Sentence}, Term.realize v (⌜φ⌝ : ℒₜ.Term _) = Term.realize (default : (Empty ⊕ Fin 0) → ↑M) (⌜φ⌝ : ℒₜ.Term _) := by
    intro φ
    induction (Encodable.encode φ) with
    | zero =>
      simp[Matrix.empty_eq]
    | succ n ih =>
      simp[ih]

  -- lemma lem3 : ∀n : Nat, ∀φ: ℒₜ.BoundedFormula Empty n, 𝐏𝐀 ⊨ᵇ (φ : ℒₜ.BoundedFormula (Fin 1) n) → 𝐏𝐀 ⊨ᵇ φ := by
  --   intro n φ h M v xs
  --   have realization := by
  --     exact h M

  --   induction φ with
  --   | falsum =>





  --     sorry
  --   | _ => sorry

variable [∀α,∀n, Encodable (ℒₜ.BoundedFormula α n)] [∀φ : ℒₜ.Sentence,∀ψ,∀ts₁,∀ts₂, Decidable (ts₁ = ![(⌜φ⌝ : ℒₜ.Term (Empty ⊕ Fin 0))] ∧ ts₁ = ts₂ ∧ φ = ψ)]
-- tau
  lemma tau_equivalence : (ψ : ℒₜ.Sentence) → ∀p : Proof Th s ψ, ∀φ ∈ get_disq_φs p, 𝐏𝐀 ⊨ᵇ ((tau p).subst ![⌜φ⌝] ⇔ φ) := by
    intro ψ p φ h₁
    apply Theory.models_sentence_iff.mpr
    intro M
    apply realize_iff.mpr
    apply Iff.intro
    -- mp
    intro h₂
    have realizable : ↑M ⊨ subst (tau p) ![⌜φ⌝] := by
      exact h₂
    unfold Sentence.Realize Formula.Realize at realizable
    apply realize_subst.mp at realizable

    have ext₁ : ∃n, ((get_disq_φs p).get n) = φ := by
      apply List.mem_iff_get.mp
      exact h₁

    simp at realizable
    let a : ℒₜ.Sentence := realizable.choose

    have step1 := realizable.choose_spec

    if h₄ : realizable.choose = φ then
      rw[h₄] at step1
      rw[Unique.default_eq]
      exact step1.right.right
    else
      have step2 := step1.right.left
      rw[lem1] at step2
      have step3 : ↑M ⊨ ∼(⌜realizable.choose⌝ =' ⌜φ⌝):= by
        apply PA.all_fs (realizable.choose) φ h₄

      apply realize_not.mp at step3
      simp[realize_bdEqual _ _] at step3

      simp[lem2] at step2
      rw[lem1] at step3
      simp[lem2] at step3
      symm at step2
      contradiction

    --mpr
    intro h₂
    apply realize_subst.mpr
    simp
    apply Exists.intro φ
    apply And.intro
    --left
    exact h₁
    --right
    apply And.intro
    --right.left
    rw[lem1]
    rw[num_all_v]
    --right.right
    rw[Unique.default_eq] at h₂
    exact h₂

variable {L : Language}
  @[simp]
  def bdEqual_iff {t₁ t₂ : L.Term (α ⊕ Fin n)} : t₁ =' t₂ = .equal t₁ t₂ := Eq.refl (t₁ =' t₂)

  def Conservative (Th₁ : ℒₜ.Theory) (Th₂ : ℒₜ.Theory) : Prop :=
    ∀φ : ℒₜ.Formula Nat, (Th₁ ⊨ᵇ (φ)) → (Th₂ ⊨ᵇ φ)

  noncomputable def back_to_l: (φ : ℒₜ.Formula Nat) → (∃ψ: ℒₜ.Formula Nat, φ = (ψ)) → ℒₜ.Formula Nat := by
    intro φ h
    exact h.choose
 --
  -- lemma lem4 : ∀φ,∀Th: ℒₜ.Theory, φ ∈ Th → φ ∈ Th := by
  --   intro φ Th h₁
  --   simp
  --   induction φ with
  --   | falsum =>
  --     apply Exists.intro
  --     apply And.intro
  --     exact h₁
  --     rfl
  --   | equal t₁ t₂ =>
  --     apply Exists.intro
  --     apply And.intro
  --     exact h₁
  --     rfl
  --   | rel R ts =>
  --     apply Exists.intro
  --     apply And.intro
  --     exact h₁
  --     rfl
  --   | imp φ₁ φ₂ ih₁ ih₂ =>
  --     apply Exists.intro
  --     apply And.intro
  --     exact h₁
  --     rfl
  --   | all φ ih =>
  --     apply Exists.intro
  --     apply And.intro
  --     exact h₁
  --     rfl


  lemma lem₅ {ψ : ℒₜ.BoundedFormula (Fin 1) n}: contains_T ψ → contains_T ψ.zero_subst := by
    intro h
    induction ψ with
    | rel R ts =>
      cases R
      exact h
    | imp f₁ f₂ ih₁ ih₂ =>
      simp only [zero_subst,zero_subst,contains_T]
      simp only [contains_T] at h
      cases h with
      | inl h =>
        apply ih₁ at h
        apply Or.intro_left
        exact h
      | inr h =>
        apply ih₂ at h
        apply Or.intro_right
        exact h
    | all f₁ ih =>
      simp [zero_subst,contains_T]
      simp [contains_T] at h
      apply ih at h
      exact h
    | _ => cases h

  lemma lem₆ {ψ : ℒₜ.BoundedFormula (Fin 1) n}: contains_T ψ → contains_T (TB.ind₂ ψ) := by
    intro h
    simp[TB.ind₂]
    apply Or.intro_left
    apply Or.intro_left
    exact lem₅ h

      -- have to show that contains_T perpetuates through variable substitution (use lem₅)
      -- but the syntactic structure of substituted formulas is hard to reason with due to mapTermRel,
      -- so it's better to define contains_T in semantic terms, via the interpretation of t_symbol.


  lemma lem₇ : 𝐏𝐀 ⊨ᵇ ((.rel L_T.Rel.t_symbol ![null] ⟹ .rel L_T.Rel.t_symbol ![null]) : ℒₜ.Sentence) := by
    apply Theory.models_sentence_iff.mpr
    intro M
    apply realize_imp.mpr
    intro h₁
    exact h₁

  -- lemma lem₈ {n} {ψ : ℒₜ.BoundedFormula Empty n} : contains_T ψ ↔ (contains_T (ψ.to_alpha : ℒₜ.BoundedFormula α n)) := by
  --   apply Iff.intro
  --   --mp
  --   intro h

  --   induction ψ with
  --   | rel R ts =>
  --     cases R
  --     simp only [to_alpha]
  --     exact h
  --   | imp f₁ f₂ ih₁ ih₂ =>
  --     simp only [to_alpha,contains_T]
  --     simp only [contains_T] at h
  --     cases h with
  --     | inl h =>
  --       apply ih₁ at h
  --       apply Or.intro_left
  --       exact h
  --     | inr h =>
  --       apply ih₂ at h
  --       apply Or.intro_right
  --       exact h
  --   | all f₁ ih₁ =>
  --     simp only [to_alpha,contains_T]
  --     simp only [contains_T] at h
  --     apply ih₁ at h
  --     exact h
  --   | _ =>
  --     cases h

  --   --mpr
  --   intro h

  --   induction ψ with
  --   | rel R ts =>
  --     cases R
  --     simp only [to_alpha] at h
  --     exact h
  --   | imp f₁ f₂ ih₁ ih₂ =>
  --     simp only [to_alpha,contains_T] at h
  --     simp only [contains_T]
  --     cases h with
  --     | inl h =>
  --       apply ih₁ at h
  --       apply Or.intro_left
  --       exact h
  --     | inr h =>
  --       apply ih₂ at h
  --       apply Or.intro_right
  --       exact h
  --   | all f₁ ih₁ =>
  --     simp only [to_alpha,contains_T] at h
  --     simp only [contains_T]
  --     apply ih₁ at h
  --     exact h
  --   | _ =>
  --     cases h

  lemma lem₉ {n} {φ : ℒₜ.BoundedFormula Empty n} {h : ¬ contains_T φ} : contains_T (TB.tarski_biconditional φ h) := by
    simp only [TB.tarski_biconditional,contains_T,BoundedFormula.iff]
    apply Or.intro_left
    apply Or.intro_left
    apply Or.intro_left
    apply True.intro

  /-- ↓ Write the translation function. The thing is that not all translations have to start with
  a formula that should not contain a T-predicate. There should only be a reference proof on
  which the tau will be based, but that one has furthermore rather little to do with
  the translation currently taking place.
  Also to do:
  1. construct the proof ...
  O, wait, perhaps we are now encountering the exact problems we encountered earlier on with a syntactic reasoning? No, because we now have the semantic connection. So,
  1. Construct the proof that there exists a PA proof of all tau equivalences from the semantic proof 'tau_equivalence'.
  2. Return the tau_equivalences in the case of tb axioms.
  3. Return a proof a the induction schema with a tau replacement of the T's, from the proof that the individual formula contains no T's and the induction schema does not add any T's (for that make lem₆ biconditional rather than the current conditional).
  --/

  @[simp]
  def Sum.contains_T : (ℒₜ.Sentence ⊕ ℒₜ.Formula α) → Prop
  | .inl a => L_T.contains_T a
  | .inr a => L_T.contains_T a

  variable [∀n, ∀α, Encodable (ℒₜ.BoundedFormula α n)]
  /-First, we need the corresponding formula for a TB formula in PA wrt a reference formula reference_f-/
  @[simp]
  def replace_T (replace_f : ℒₜ.Formula (Fin 1)): {n : Nat} → ℒₜ.BoundedFormula α n → ℒₜ.BoundedFormula α n
  | n, .rel (l := 1) R ts =>
    match R, ts 0 with
    | .t_symbol, t =>
      .relabel (fun i : α ⊕ Fin n => match i with
      | .inl a => .inl a
      | .inr n => .inr n) (replace_f.subst ![t])
  | _, .imp φ ψ => .imp (replace_T replace_f φ) (replace_T replace_f ψ)
  | _, .all φ => .all (replace_T replace_f φ)
  | _, φ => φ


/- Secondly, we need the following -/
variable {a : ∀p, Finite (Fin (proof_tau_equiv_list p).length)}
  lemma tau_equivalence₂ : (ψ : ℒₜ.Sentence) → ∀p : Proof Th s ψ, ∀φ ∈ get_disq_φs p, (h : ¬ contains_T φ) → {a : Finite (Fin (proof_tau_equiv_list p).length)} → 𝐏𝐀 ⊨ᵇ replace_T (tau p) (TB.tarski_biconditional φ h) := by

    sorry -- below serves as guidance; it's simply the proof of tau_equivalence
    -- intro ψ p φ h₁ h₂
    -- apply Theory.models_sentence_iff.mpr
    -- intro M
    -- simp
    -- apply realize_iff.mpr
    -- apply Iff.intro
    -- -- mp
    -- intro h₃
    -- have realizable : ↑M ⊨ subst (tau p) ![⌜φ⌝] := by
    --   exact h₂
    -- unfold Sentence.Realize Formula.Realize at realizable
    -- apply realize_subst.mp at realizable
    -- apply realize_iSup.mp at realizable
    -- have ext₁ : ∃n, (get_disq_φs p).get n = φ := by
    --   apply List.mem_iff_get.mp
    --   exact h₁
    -- let realization : Realize ((List.map make_tau_equiv (get_disq_φs p)).get realizable.choose) (fun a ↦ @Term.realize ℒₜ M _ _ (@default (Empty → ↑M) _) (![⌜φ⌝] a)) default := by
    --   exact realizable.choose_spec

    -- rw[List.get_eq_getElem] at realization
    -- rw[List.getElem_map] at realization

    -- if h₄ : (get_disq_φs p)[Fin.val realizable.choose] = φ then
    --   rw[h₄] at realization
    --   simp at realization
    --   apply And.right at realization

    --   rw[Unique.default_eq]
    --   rw[Unique.default_eq]

    --   exact realization

    -- else
    --   simp only [make_tau_equiv,realize_inf] at realization
    --   apply And.left at realization

    --   simp at realization

    --   -- iets met injectief (bewezen in syntax voor ℒ)
    --   -- de sleutel is dat de realization moet kloppen in elke M,
    --   -- dus ook in die waar het de interpretatie van getallen krijgt
    --   -- we moeten bewijzen dat Nat een ∅.ModelType is

    --   simp[Matrix.empty_eq,Matrix.vec_single_eq_const] at realization

    --   have step1 : ↑M ⊨ (∼(⌜(get_disq_φs p)[↑realizable.choose]⌝ =' ⌜φ⌝) : ℒₜ.Sentence) := by
    --     apply PA.all_fs
    --     exact h₄

    --   apply realize_not.mp at step1
    --   simp[realize_bdEqual _ _] at step1
    --   -- we hebben hier peano_arithmetic regels nodig
    --   rw[lem1] at realization
    --   simp[lem2] at realization
    --   rw[lem1] at step1
    --   simp[lem2] at step1
    --   symm at realization
    --   apply step1 at realization
    --   contradiction

    -- --mpr
    -- intro h₂
    -- apply realize_subst.mpr; apply realize_iSup.mpr
    -- have ext : ∃ n, (get_disq_φs p).get n = φ := by
    --   apply List.mem_iff_get.mp h₁

    -- let n : Fin (get_disq_φs p).length := ext.choose
    -- let m : Fin ((get_disq_φs p).map make_tau_equiv).length := by
    --   rw[List.length_map]
    --   exact n

    -- apply Exists.intro m; rw[List.get_eq_getElem]; rw[List.getElem_map]

    -- have m_val_eq_n_val : @Fin.val (List.map make_tau_equiv (get_disq_φs p)).length m = @Fin.val (get_disq_φs p).length n := by
    --   simp[m,Fin.cast_eq_cast']
    -- simp only [m_val_eq_n_val]
    -- have is_phi : (get_disq_φs p)[(Fin.val n)] = φ := by
    --   apply ext.choose_spec
    -- rw[is_phi]; apply BoundedFormula.realize_inf.mpr; apply And.intro

    -- -- left
    -- apply (realize_bdEqual _ _).mpr; simp
    -- rw[num_all_v ((Sum.elim (fun a ↦ Term.realize _ ⌜φ⌝) _)) _]
    -- --right
    -- simp
    -- rw[Unique.default_eq ((Sum.elim (fun a ↦ Term.realize default (⌜φ⌝: ℒₜ.Term Empty)) (default: Fin 0 → ↑M) ∘ fun x ↦ Sum.inl 0))] at h₂
    -- exact h₂


  instance : Decidable (⌜(falsum : ℒₜ.Sentence)⌝ = (⌜(falsum : ℒₜ.Sentence)⌝ : ℒₜ.Term (Empty ⊕ Fin 0)) ∧ ⌜(falsum : ℒₜ.Sentence)⌝ = (⌜(falsum : ℒₜ.Sentence)⌝ : ℒₜ.Term (Empty ⊕ Fin 0)) ∧ falsum = (falsum : ℒₜ.Sentence)) := by
    simp
    apply Decidable.isTrue
    exact True.intro

  lemma merp {ps : ProofSystem}: (get_disq_φs (s := ps) ((Proof.ax (.rel L_T.Rel.t_symbol ![⌜falsum⌝] ⇔ falsum)) (TB.tb.bicon (falsum) (by simp)))) = [falsum] := by
    simp [BoundedFormula.iff]

  lemma de_pemma : ⌜(falsum : ℒₜ.Sentence)⌝ = (⌜(falsum : ℒₜ.Sentence)⌝ : ℒₜ.Term (Empty ⊕ Fin 0)) ∧ ⌜(falsum : ℒₜ.Sentence)⌝ = (⌜(falsum : ℒₜ.Sentence)⌝ : ℒₜ.Term (Empty ⊕ Fin 0)) ∧ falsum = (falsum : ℒₜ.Sentence) := by
    simp

  open Classical Language BoundedFormula
  /-Thirdly, we need the prove that replacing all T's yields a proof in 𝐏𝐀 -/
  #check ℒₜ.Constants
  #check Constants.term (L := ℒₜ) (α := Nat) L_T.Func.zero_symbol
  variable   [∀φ : ℒₜ.Sentence,∀ψ,∀ts₁,∀ts₂, Decidable (ts₁ = ![(⌜φ⌝ : ℒₜ.Term (Empty ⊕ Fin 0))] ∧ ts₁ = ts₂ ∧ φ = ψ)]
  variable [DecidableEq (ℒₜ.Term (Empty ⊕ Fin 0))]
  example {ps : ProofSystem} {sound : Sound ps} {complete : Complete ps} {φ₁} : ∀p : Proof 𝐓𝐁 ps φ₁, Nonempty (Proof 𝐏𝐀 ps (replace_T (tau p) φ₁)) := by
    intro p
    unfold Sound at sound
    unfold Complete at complete

    unfold tau
    apply (complete _ _)
    #check tau_equivalence φ₁ p
    have step1 := tau_equivalence φ₁ p

    induction p with
    | ax φ₂ h =>
      cases h with
      | bicon φ h =>
        match φ with
        | falsum =>
          -- we seemed to need that ∀φ, ∀p, ¬ contains_T φ → 𝐏𝐀 ⊨ᵇ replace_T (tau p) (TB.tarski_biconditional φ), which is slightly different from our current tau_equivalences proof, but solved it with a different notion of tau instead.

          simp[BoundedFormula.iff]
          apply Theory.models_formula_iff.mpr
          intro M₂ v
          apply realize_imp.mpr
          intro h₅
          rw[Unique.default_eq] at h₅
          simp at h₅

          sorry



        | all φ₁ =>
          simp
          /-𝐏𝐀 ⊨ᵇ
  replace_T (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ (proof_tau_equiv_list (Proof.ax (TB.tarski_biconditional φ h) ⋯)))
    (TB.tarski_biconditional φ h)-/
          /- here, we encounter induction problems again. We need that ∀φ : BoundedFormula α n, (h : ¬ contains_T φ) → 𝐏𝐀 ⊨ᵇ replace_T (List.foldr (fun x1 x2 ↦ x1 ⊔ x2) ⊥ (proof_tau_equiv_list (Proof.ax (TB.tarski_biconditional φ h) ⋯))) (TB.tarski_biconditional φ h)-/

          sorry

        | _ => sorry


      | first =>
        apply (complete _ _)
        simp
        apply Theory.models_sentence_of_mem
        apply And.intro
        -- left
        apply TB.tb.first
        -- right
        simp
      | _ => sorry
    | _ => sorry

  example {φ : ℒₜ.BoundedFormula α n} {h : ¬ contains_T φ} : 𝐓𝐁 ⊨ᵇ φ → 𝐏𝐀 ⊨ᵇ φ := by
    intro h
    induction φ with
    | falsum =>

      unfold Theory.ModelsBoundedFormula at h
      unfold Theory.ModelsBoundedFormula
      intro M v xs
      -- have step1 : 𝐓𝐁.ModelType := default
      sorry
    | _ => sorry

  -- def proof_tb_to_proof_pa {p : ProofSystem}{sound : p.Sound}{complete : p.Complete}{h₁ : ¬ Sum.contains_T φ₁} (reference_p : Proof 𝐓𝐁 p φ₁)(h₁ : ¬ Sum.contains_T φ₁) : Proof 𝐓𝐁 p φ₂ → Nonempty (Proof 𝐏𝐀 p φ₃)
  -- | .ax φ₆ h₂ => by
  --   cases h₂ with
  --   | first =>

  --     sorry
  --   | _ => sorry
  -- | _ => sorry

  -- lemma provable_tb_to_provable_pa  {p : ProofSystem}{sound : p.Sound}{complete : p.Complete}(φ : Fml)(h₁ : ¬ Sum.contains_T φ): (𝐓𝐁 ⊢(p) (φ)) → (Nonempty (Provable 𝐏𝐀 p φ (α := α))) := by
  --   intro h₂
  --   apply Classical.choice at h₂
  --   -- let tau : ℒₜ.Formula (Fin 1) := tau h₂
  --   induction h₂ with
  --   | ax ψ h₃ =>
  --     have step12 : ψ ∈ 𝐓𝐁 := h₃
  --     apply Nonempty.intro
  --     have step2 : ψ ∈ 𝐏𝐀 := by
  --       cases h₃ with
  --       | induction ψ₂ =>
  --         simp at h₁
  --         unfold PA.pa
  --         apply And.intro
  --         apply TB.tb.induction ψ₂
  --         exact h₁
  --       | bicon φ₂ h₂ =>
  --         have step1 : contains_T (TB.tarski_biconditional φ₂ h₂) := by
  --           exact lem₉
  --         contradiction
  --       | _ =>
  --         unfold PA.pa
  --         apply And.intro
  --         exact step12
  --         simp only [Sum.contains_T] at h₁
  --         exact h₁

  --       -- | intro w h =>
  --       --   cases h.left with
  --       --   | bicon φ₂ h₂ => -- this cases should still include the translation to PA proof

  --       --     have step1 : contains_T (TB.tarski_biconditional φ₂ h₂) := by
  --       --       exact lem₉

  --       --     apply lem₈.mp at step1
  --       --     rw[h.right] at step1

  --       --     contradiction
  --         -- | _ => sorry
  --       -- TAKES LONG BUT DONE
  --       -- cases step1 with
  --       -- | intro w h =>
  --       --   cases h.left with
  --       --   | induction ψ₂ =>
  --       --     if h₂ : contains_T ψ₂ then
  --       --     have step1 : contains_T ψ := by
  --       --       rw[h.right.symm]
  --       --       simp[TB.ind₂]
  --       --       apply Or.intro_left
  --       --       apply Or.intro_left
  --       --       apply lem₈.mp
  --       --       apply lem₅
  --       --       exact h₂
  --       --     contradiction
  --       --     -- use that contains_T perpetuates through TB.ind (see lem₆)
  --       --     else
  --       --     simp
  --       --     apply Exists.intro
  --       --     apply And.intro
  --       --     unfold PA.pa
  --       --     simp
  --       --     apply And.intro
  --       --     exact chosen_left
  --       --     rw[chosen.right.symm] at h₁
  --       --     exact lem₈.not.mpr h₁
  --       --     exact chosen.right
  --       --   | bicon φ₂ h₂ =>
  --       --     have step1 : contains_T (TB.tarski_biconditional φ₂ h₂) := by
  --       --       exact lem₉
  --       --     apply lem₈.mp at step1
  --       --     rw[h.right] at step1
  --       --     contradiction
  --       --   | _ =>
  --       --     unfold PA.pa
  --       --     simp
  --       --     apply Exists.intro
  --       --     apply And.intro
  --       --     apply And.intro
  --       --     exact h.left
  --       --     simp
  --       --     exact h.right

  --     exact Nonempty.intro (Proof.ax ψ step2)
  --   | un p₁ h₂ h₃ ih_p =>
  --     /-Perhaps here we need to resort to some other form of translation as most is irrelevant -/
  --     #check ih_p
  --     sorry
  --   | _ => sorry
  --   -- let tau : ℒ.Formula (Fin 1) := tau h₁
  --   -- cases h₁ with
  --   -- | ax ψ h₂ =>
  --   --   simp at h₂
  --   --   have chosen := h₂.choose_spec
  --   --   have chosen_left := chosen.left
  --   --   unfold TB.tb at chosen_left
  --   --   sorry
  --   --   -- simp at chosen_left
  --   --   -- cases chosen_left with
  --   --   -- | inl h₃ =>
  --   --   --   unfold PAT.pat at h₃
  --   --   --   simp at h₃
  --   --   --   cases h₃ with
  --   --   --   | inl h₃ =>


  --   --   --     #check Proof.ax (Th := (to_alpha '' 𝐏𝐀))
  --   --   --     sorry
  --   --   --   | inr h₃ => sorry
  --   -- | _ => sorry

  -- theorem conservativity_tb_pa {p₁ : @ProofSystem ℒₜ Nat 0}{p₂ : @ProofSystem ℒₜ Nat 0}{sound₁ : p₁.Sound}{sound₂ : p₂.Sound}{complete₁ : p₁.Complete}{complete₂ : p₂.Complete} : Conservative 𝐓𝐁 𝐏𝐀 := by
  --   intro φ h₁
  --   have tb_proof : Proof (to_alpha '' 𝐓𝐁) p₂ (φ) := by
  --     unfold Complete at complete₂
  --     #check complete₂ φ
  --     apply Classical.choice
  --     apply complete₂ φ
  --     exact h₁
  --   let tau : ℒₜ.Formula (Fin 1) := tau tb_proof

  --   cases tb_proof with
  --   | ax f h =>
  --     sorry
  --     -- | inl h =>
  --     --   -- h ->(by soundness of p₂) {} ⊨ᵇ ϕ.onFormula φ ->(by completeness of p₁) {} ⊢(s₁) φ ->(by superset proves all subset) 𝐏𝐀 ⊨ᵇ φ

  --     --   have proof := Nonempty.intro (Proof.ax (Th := (to_alpha '' {})) (s := p₂) (ϕ.onFormula φ) (by simp[h]))

  --     --   have theo := sound₂ (ϕ.onFormula φ) {} proof


  --     --   sorry
  --     -- | inr h => sorry
  --   | _ => sorry

end Conservativity
