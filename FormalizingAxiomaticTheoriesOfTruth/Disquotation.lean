import FormalizingAxiomaticTheoriesOfTruth.Prelims
import Foundation.FirstOrder.Basic.Coding
import Foundation.FirstOrder.Basic.Calculus

open LO
open FirstOrder
open L_T
open PAT

namespace TB

notation:25 "⌜" φ:25 "⌝" => numeral (Semiformula.toNat φ)

def disquotation_schema (φ : SyntacticFormula signature) : SyntacticFormula signature :=
  (T ![⌜φ⌝]) ⇔  φ
def disquotation_set (Γ : Fml → Prop) : Theory signature :=
  { ψ | ∃ φ ∈ ℒₚₐ, Γ φ ∧ ψ = (disquotation_schema φ)}
def tb : Theory signature := {φ | φ ∈ 𝐏𝐀𝐓 ∨ φ ∈ (disquotation_set Set.univ)}

notation "𝐓𝐁" => tb
end TB

def dflt_f : SyntacticFormula signature := = ![&0,&0]

def der_to_disquoted_list (d : Derivation 𝐓𝐁 Γ): (List Fml) :=
  match d with
  | .axL Δ r v => []
  | .verum Δ => []
  | .or der => der_to_disquoted_list der
  | .and der₁ der₂ =>
    if (der_to_disquoted_list der₁) ∩ (der_to_disquoted_list der₂) = ∅ then
      (der_to_disquoted_list der₁) ++ (der_to_disquoted_list der₂) else
      (der_to_disquoted_list der₁) ++ (List.diff (der_to_disquoted_list der₂) ((der_to_disquoted_list der₁) ∩ (der_to_disquoted_list der₂)))
  | .all der => der_to_disquoted_list der
  | .ex _ der => der_to_disquoted_list der
  | .wk der _ => der_to_disquoted_list der
  | .cut _ _ => []
  | .root _ =>
    match Γ with
    | [φ] =>
      match φ with
      | Semiformula.and (Semiformula.or (Semiformula.nrel Rel.t v) (ψ₁)) (Semiformula.or (ψ₂) (Semiformula.rel Rel.t w)) =>
        if ψ₁ = ∼ψ₂ ∧ v = w then [Semiformula.and (= ![&0,(v 0)]) ((Semiformula.ofNat 0 ((natural (v 0)).getD dflt)).getD dflt_f)] else []
      | _ => []
    | _ => []

def build_tau_from_list : List Fml → Fml
  | .nil => .verum
  | .cons h Γ =>
    h ⋎ (build_tau_from_list Γ)

def list1 : List ℕ := [1,2,3]
def list2 : List ℕ := [4,5]
#eval list1 ∩ list2 = ∅

def tau (der : Derivation 𝐓𝐁 Γ) : Fml :=
  build_tau_from_list (der_to_disquoted_list der)

def disq : Fml := TB.disquotation_schema ⊤
def double_disq : Fml := disq ⋏ disq
lemma disq_in_tb : disq ∈ 𝐓𝐁 := by
  rw[disq,TB.tb]
  simp
  rw[TB.disquotation_set]
  simp
  let φ : Fml := ⊤
  have step1 : φ ∈ ℒₚₐ := by
    rw[lpa]
    simp
    simp[φ]
    simp[contains_T]
  have step2 : Set.univ φ := by
    trivial
  have step3 : TB.disquotation_schema ⊤ = TB.disquotation_schema φ := by
    simp
  have step4 : φ ∈ ℒₚₐ ∧ Set.univ φ ∧ TB.disquotation_schema ⊤ = TB.disquotation_schema φ := by
    trivial
  have step5 : ∃ φ ∈ ℒₚₐ, Set.univ φ ∧ TB.disquotation_schema ⊤ = TB.disquotation_schema φ := by
    apply Exists.intro φ step4
  apply Or.intro_right
  trivial

def der : Derivation 𝐓𝐁 [disq] :=
  Derivation.root disq_in_tb

#check der_to_disquoted_list der
#eval der_to_disquoted_list der

#check tau der
#eval tau der

def der_double_disq : Derivation 𝐓𝐁 [double_disq] := by
  rw[double_disq]
  apply Derivation.and
  apply der
  apply der

#check der_to_disquoted_list der_double_disq
#eval der_to_disquoted_list der_double_disq

#check tau der_double_disq
#eval tau der_double_disq

-- one should match is up to a disquotation scheme enirely
-- bewaren voor later: apply Semiformula.or (Semiformula.and (= ![&0,(v 0)]) ((Semiformula.ofNat 0 ((natural (v 0)).getD dflt)).getD dflt_f)) (tau_base_case Γ)
-- # Diepe dingen: er moet een matchup zijn tussen de predicaten
def tau_base_case : Sequent signature → SyntacticFormula signature :=
  fun h : Sequent signature =>
  (match h with
    | List.nil =>
        Semiformula.verum
    | List.cons head Γ =>
      match head with
        | Semiformula.and (Semiformula.or (Semiformula.nrel Rel.t v) (φ₁)) (Semiformula.or (φ₂) (Semiformula.rel Rel.t w)) =>
          if φ₁ = ∼φ₂ ∧ v = w then Semiformula.or (Semiformula.and (= ![&0,(v 0)]) ((Semiformula.ofNat 0 ((natural (v 0)).getD dflt)).getD dflt_f)) (tau_base_case Γ) else Semiformula.or (⊤) (tau_base_case Γ)
        | _ =>
          Semiformula.or (⊤) (tau_base_case Γ))

def wo_t : Fml := = ![&0,&0]
def w_t : Fml := T ![S ![zero]]
def seq : Sequent signature := (wo_t :: [w_t,disq])

#check Rewriting.fix (tau_base_case seq)
def zero2 : Semiterm signature ℕ 1 := zero
#eval (Rewriting.fix (tau_base_case seq))/[zero2]

-- def tau : Derivation 𝐓𝐁 Γ → SyntacticFormula signature :=
--   fun der_tb : Derivation 𝐓𝐁 Γ =>
--     match der_tb with
--       | Derivation.axL Δ r v => tau_base_case Δ
--       | Derivation.verum Δ => tau_base_case Δ
--       | Derivation.or der => tau der
--       | Derivation.and der1 der2 => (tau der1) ⋎ (tau der2)
--       | Derivation.all der => tau der
--       | Derivation.ex _ der => tau der
--       | Derivation.wk der sub => tau der
--       | Derivation.cut der1 der2 => (tau der1) ⋎ (tau der2)
--       | Derivation.root _ => tau_base_case Γ

def der_some_disq : Derivation 𝐓𝐁 [disq] := by
  have step1 : ⊤ ∈ ℒₜ := by
    rw[lt]
    trivial
  --have step2 : ¬ (contains_T ⊤) := by
    --rw[contains_T]
  have step3 : ⊤ ∈ ℒₚₐ := by
    sorry
  sorry

-- replace should replace in a derivation an atomic formula containing
-- T with tau

def lpa_sequent_set : Set (Sequent signature) := Set.univ
notation "𝐒𝐞𝐪ₚₐ" => lpa_sequent_set

def der_to_der : ∀ψ∈ℒₜ, 𝐓𝐁 ⟹ ψ :: Γ → 𝐏𝐀 ⟹ φ :: Δ := by
  intro ψ
  intro in_lt
  intro h
  cases h with
  | axL Γ r v =>
    cases r with
    | t =>
        let tau : SyntacticFormula signature :=
          sorry -- replace(Rel.t v,Γ)

        sorry
    | eq => sorry
  | verum Γ =>
      sorry -- apply Derivation.verum
  | or der =>
      cases der with
      | axL Δ r v =>
        sorry
      | verum => sorry
      | and => sorry
      | or => sorry
      | all => sorry
      | ex => sorry
      | wk => sorry
      | cut => sorry
  | and => sorry
  | all => sorry
  | ex => sorry
  | wk => sorry
  | cut => sorry
  | root => sorry

theorem conservativity_of_tb : ∀φ ∈ ℒₚₐ, 𝐓𝐁 ⊢! φ → 𝐏𝐀 ⊢! φ := by
  sorry
  -- intro φ
  -- intro in_lpa
  -- repeat rw[System.Provable]
  -- intro h
  -- apply Classical.choice at h
  -- apply der_to_der at h
  -- apply Nonempty.intro h
