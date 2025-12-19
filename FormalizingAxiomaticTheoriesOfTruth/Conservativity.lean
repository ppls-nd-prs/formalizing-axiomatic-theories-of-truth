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

  variable {Th : ℒₜ.Theory}[∀n, Encodable (ℒₜ.BoundedFormula Empty n)]
  @[simp]
  noncomputable def get_disq_φs : (p : Proof ℒₜ Th) → List (ℒₜ.Sentence)
  | .nil => []
  | .ax φ _ => if th : ∃ψ,∃h, φ = (TB.tarski_biconditional ψ h)
    then
    [th.choose]
    else
    []
  | .node p₁ p₂ _ => (get_disq_φs p₁) ∪ (get_disq_φs p₂)


  variable [Encodable (ℒₜ.Formula (Fin 1))]
  -- instance : Coe (ℒₜ.Sentence) (ℒₜ.Formula (Fin 1)) where
  -- coe := to_alpha

  @[simp]
  def make_tau_equivs (s : ℒₜ.Sentence) : ℒₜ.Formula (Fin 1) := #0 =' ⌜s⌝ ⊓ s

  open Proof
  @[simp]
  noncomputable def tau : Proof ℒₜ Th → ℒₜ.Formula (Fin 1) :=
    fun p => Formula.iSup ((get_disq_φs p).map make_tau_equivs).get

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
  open L_T
  variable {L : Language}{Th : ℒₜ.Theory}{α : Type}{n : Nat}[∀n, Encodable (ℒₜ.BoundedFormula Empty n)]{s : Proof ℒₜ Th}

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

  lemma tau_equivalence : (ψ : ℒₜ.Formula α) → ∀p : Proof ℒₜ Th, ∀φ ∈ get_disq_φs p, 𝐏𝐀 ⊨ᵇ ((tau p).subst ![⌜φ⌝] ⇔ φ) := by
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
    apply realize_iSup.mp at realizable
    have ext₁ : ∃n, (get_disq_φs p).get n = φ := by
      apply List.mem_iff_get.mp
      exact h₁
    let realization : Realize ((List.map make_tau_equivs (get_disq_φs p)).get realizable.choose) (fun a ↦ @Term.realize ℒₜ M _ _ (@default (Empty → ↑M) _) (![⌜φ⌝] a)) default := by
      exact realizable.choose_spec

    rw[List.get_eq_getElem] at realization
    rw[List.getElem_map] at realization

    if h₄ : (get_disq_φs p)[Fin.val realizable.choose] = φ then
      rw[h₄] at realization
      simp at realization
      apply And.right at realization

      rw[Unique.default_eq]
      rw[Unique.default_eq]

      exact realization

    else
      simp only [make_tau_equivs,realize_inf] at realization
      apply And.left at realization

      simp at realization

      -- iets met injectief (bewezen in syntax voor ℒ)
      -- de sleutel is dat de realization moet kloppen in elke M,
      -- dus ook in die waar het de interpretatie van getallen krijgt
      -- we moeten bewijzen dat Nat een ∅.ModelType is

      simp[Matrix.empty_eq,Matrix.vec_single_eq_const] at realization

      have step1 : ↑M ⊨ (∼(⌜(get_disq_φs p)[↑realizable.choose]⌝ =' ⌜φ⌝) : ℒₜ.Sentence) := by
        apply PA.all_fs
        exact h₄

      apply realize_not.mp at step1
      simp[realize_bdEqual _ _] at step1
      -- we hebben hier peano_arithmetic regels nodig
      rw[lem1] at realization
      simp[lem2] at realization
      rw[lem1] at step1
      simp[lem2] at step1
      symm at realization
      apply step1 at realization
      contradiction

    --mpr
    intro h₂
    apply realize_subst.mpr; apply realize_iSup.mpr
    have ext : ∃ n, (get_disq_φs p).get n = φ := by
      apply List.mem_iff_get.mp h₁

    let n : Fin (get_disq_φs p).length := ext.choose
    let m : Fin ((get_disq_φs p).map make_tau_equivs).length := by
      rw[List.length_map]
      exact n

    apply Exists.intro m; rw[List.get_eq_getElem]; rw[List.getElem_map]

    have m_val_eq_n_val : @Fin.val (List.map make_tau_equivs (get_disq_φs p)).length m = @Fin.val (get_disq_φs p).length n := by
      simp[m,Fin.cast_eq_cast']
    simp only [m_val_eq_n_val]
    have is_phi : (get_disq_φs p)[(Fin.val n)] = φ := by
      apply ext.choose_spec
    rw[is_phi]; apply BoundedFormula.realize_inf.mpr; apply And.intro

    -- left
    apply (realize_bdEqual _ _).mpr; simp
    rw[num_all_v ((Sum.elim (fun a ↦ Term.realize _ ⌜φ⌝) _)) _]
    --right
    simp
    rw[Unique.default_eq ((Sum.elim (fun a ↦ Term.realize default (⌜φ⌝: ℒₜ.Term Empty)) (default: Fin 0 → ↑M) ∘ fun x ↦ Sum.inl 0))] at h₂
    exact h₂

  variable {L : Language}
  @[simp]
  def bdEqual_iff {t₁ t₂ : L.Term (α ⊕ Fin n)} : t₁ =' t₂ = .equal t₁ t₂ := Eq.refl (t₁ =' t₂)

  def Conservative (Th₁ : ℒₜ.Theory) (Th₂ : ℒₜ.Theory) : Prop :=
    ∀φ : ℒₜ.Formula Nat, (Th₁ ⊨ᵇ (φ)) → (Th₂ ⊨ᵇ φ)

  noncomputable def back_to_l: (φ : ℒₜ.Formula Nat) → (∃ψ: ℒₜ.Formula Nat, φ = (ψ)) → ℒₜ.Formula Nat := by
    intro φ h
    exact h.choose

  -- lemma lem4 : ∀n,∀φ,∀Th: Set (ℒₜ.BoundedFormula Empty n), φ ∈ Th → (@to_alpha ℕ _ _ φ) ∈ (to_alpha '' Th) := by
  --   intro n φ Th h₁
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

  #check BoundedFormula.subst

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

  -- lemma lem₈ {n} {ψ : ℒₜ.BoundedFormula Empty n} : contains_T ψ ↔ (contains_T (ψ : ℒₜ.BoundedFormula α n)) := by
  --   apply Iff.intro
  --   --mp
  --   intro h

  --   induction ψ with
  --   | rel R ts =>
  --     cases R
  --     exact h
  --   | imp f₁ f₂ ih₁ ih₂ =>
  --     simp only [contains_T]
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

  /- ↓ Write the translation function. The thing is that not all translations have to start with
  a formula that should not contain a T-predicate. There should only be a reference proof on
  which the tau will be based, but that one has furthermore rather little to do with
  the translation currently taking place.
  Also to do:
  1. construct the proof ...
  O, wait, perhaps we are now encountering the exact problems we encountered earlier on with a syntactic reasoning? No, because we now have the semantic connection. So,
  1. Construct the proof that there exists a PA proof of all tau equivalences from the semantic proof 'tau_equivalence'.
  2. Return the tau_equivalences in the case of tb axioms.
  3. Return a proof a the induction schema with a tau replacement of the T's, from the proof that the individual formula contains no T's and the induction schema does not add any T's (for that make lem₆ biconditional rather than the current conditional).
  -/

open Proof
  def proof_tb_to_proof_pa {p : Proof ℒₜ Th}{sound : p.Sound (α := Nat)}{complete : p.Complete (α := Nat)}{φ₁ : ℒₜ.Sentence}{h₁ : ¬ contains_T φ₁}{h₂ : Th ⊢(p) φ₁} : Proof ℒₜ 𝐓𝐁 → Proof ℒₜ 𝐏𝐀
  | .ax φ₂ h₂ => by


    sorry

  | _ => sorry

  lemma provable_tb_to_provable_pa  {p : @Proof ℒₜ Nat 0}{sound : p.Sound}{complete : p.Complete}(φ : ℒₜ.Formula Nat)(h₁ : ¬ contains_T φ): ((to_alpha '' 𝐓𝐁) ⊢(p) (φ)) → (to_alpha '' 𝐏𝐀) ⊢(p) (φ) := by
    intro h₂
    apply Classical.choice at h₂
    -- let tau : ℒₜ.Formula (Fin 1) := tau h₂
    induction h₂ with
    | ax ψ h₃ =>
      simp at h₃
      have chosen := h₃.choose_spec
      have chosen_left := chosen.left
      apply Nonempty.intro
      have step1 : (h₃.choose.to_alpha : ℒₜ.Formula ℕ) ∈ (to_alpha '' 𝐓𝐁) := by
        apply lem4 _ _ _ chosen_left
      rw[chosen.right] at step1
      have step2 : ψ ∈ (to_alpha '' 𝐏𝐀) := by
        cases step1 with
        | intro w h =>
          cases h.left with
          | bicon φ₂ h₂ => -- this cases should still include the translation to PA proof

            have step1 : contains_T (TB.tarski_biconditional φ₂ h₂) := by
              exact lem₉

            apply lem₈.mp at step1
            rw[h.right] at step1

            contradiction
          | _ => sorry
        -- TAKES LONG BUT DONE
        -- cases step1 with
        -- | intro w h =>
        --   cases h.left with
        --   | induction ψ₂ =>
        --     if h₂ : contains_T ψ₂ then
        --     have step1 : contains_T ψ := by
        --       rw[h.right.symm]
        --       simp[TB.ind₂]
        --       apply Or.intro_left
        --       apply Or.intro_left
        --       apply lem₈.mp
        --       apply lem₅
        --       exact h₂
        --     contradiction
        --     -- use that contains_T perpetuates through TB.ind (see lem₆)
        --     else
        --     simp
        --     apply Exists.intro
        --     apply And.intro
        --     unfold PA.pa
        --     simp
        --     apply And.intro
        --     exact chosen_left
        --     rw[chosen.right.symm] at h₁
        --     exact lem₈.not.mpr h₁
        --     exact chosen.right
        --   | bicon φ₂ h₂ =>
        --     have step1 : contains_T (TB.tarski_biconditional φ₂ h₂) := by
        --       exact lem₉
        --     apply lem₈.mp at step1
        --     rw[h.right] at step1
        --     contradiction
        --   | _ =>
        --     unfold PA.pa
        --     simp
        --     apply Exists.intro
        --     apply And.intro
        --     apply And.intro
        --     exact h.left
        --     simp
        --     exact h.right

      exact @Proof.ax _ _ _ _ p ψ step2
    | un p₁ h₂ h₃ ih_p =>

      #check ih_p
      sorry
    | _ => sorry
    -- let tau : ℒ.Formula (Fin 1) := tau h₁
    -- cases h₁ with
    -- | ax ψ h₂ =>
    --   simp at h₂
    --   have chosen := h₂.choose_spec
    --   have chosen_left := chosen.left
    --   unfold TB.tb at chosen_left
    --   sorry
    --   -- simp at chosen_left
    --   -- cases chosen_left with
    --   -- | inl h₃ =>
    --   --   unfold PAT.pat at h₃
    --   --   simp at h₃
    --   --   cases h₃ with
    --   --   | inl h₃ =>


    --   --     #check Proof.ax (Th := (to_alpha '' 𝐏𝐀))
    --   --     sorry
    --   --   | inr h₃ => sorry
    -- | _ => sorry

  theorem conservativity_tb_pa {p₁ : @Proof ℒₜ Nat 0}{p₂ : @Proof ℒₜ Nat 0}{sound₁ : p₁.Sound}{sound₂ : p₂.Sound}{complete₁ : p₁.Complete}{complete₂ : p₂.Complete} : Conservative 𝐓𝐁 𝐏𝐀 := by
    intro φ h₁
    have tb_proof : ProofTree (to_alpha '' 𝐓𝐁) p₂ (φ) := by
      unfold Complete at complete₂
      #check complete₂ φ
      apply Classical.choice
      apply complete₂ φ
      exact h₁
    let tau : ℒₜ.Formula (Fin 1) := tau tb_proof

    cases tb_proof with
    | ax f h =>
      sorry
      -- | inl h =>
      --   -- h ->(by soundness of p₂) {} ⊨ᵇ ϕ.onFormula φ ->(by completeness of p₁) {} ⊢(s₁) φ ->(by superset proves all subset) 𝐏𝐀 ⊨ᵇ φ

      --   have proof := Nonempty.intro (Proof.ax (Th := (to_alpha '' {})) (s := p₂) (ϕ.onFormula φ) (by simp[h]))

      --   have theo := sound₂ (ϕ.onFormula φ) {} proof


      --   sorry
      -- | inr h => sorry
    | _ => sorry

end Conservativity
