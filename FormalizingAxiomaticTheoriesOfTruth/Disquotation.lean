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
def disquotation_set (Γ : SyntacticFormula signature → Prop) : Theory signature :=
  { ψ | ∃ φ ∈ ℒₚₐ, Γ φ ∧ ψ = (disquotation_schema φ)}
def tb : Theory signature := {φ | φ ∈ 𝐏𝐀𝐓 ∨ φ ∈ (disquotation_set Set.univ)}

def eq_zero : Fml :=
  ⊤
#eval disquotation_schema eq_zero

notation "𝐓𝐁" => tb

end TB

def dflt_f : SyntacticFormula signature := = ![&0,&0]

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
def disq : Fml := TB.disquotation_schema ⊤
def seq : Sequent signature := (wo_t :: [w_t,disq])

#check Rewriting.fix (tau_base_case seq)
def zero2 : Semiterm signature ℕ 1 := zero
#eval (Rewriting.fix (tau_base_case seq))/[zero2]

def tau : Derivation 𝐓𝐁 Γ → SyntacticFormula signature
  | .axL Δ r v => tau_base_case Δ
  | .verum Δ => tau_base_case Δ
  | .or der => tau der
  | .and der1 der2 => (tau der1) ⋎ (tau der2)
  | .all der => tau der
  | .ex t der => tau der
  | .wk der sub => tau der
  | .cut der1 der2 => (tau der1) ⋎ (tau der2)
  | .root element => sorry

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
