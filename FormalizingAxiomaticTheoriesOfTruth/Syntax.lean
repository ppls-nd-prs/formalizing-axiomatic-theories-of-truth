import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Encoding

open FirstOrder
open Language

namespace String
  def vecToStr : ∀ {n}, (Fin n → String) → String
  | 0,     _ => ""
  | n + 1, s => if n = 0 then s 0 else s 0 ++ ", " ++ @vecToStr n (fun i => s (Fin.succ i))

  #eval vecToStr !["a","b","c"]

end String

namespace Term
  variable {L : Language} {α β : Type}
  variable [∀ k, ToString (L.Functions k)] [ToString α] [ToString β]

  section ToString
    def toStr : Term L ℕ → String :=
      fun t : Term L ℕ =>
        match t with
        | .var k => "⬝" ++ toString k
        | .func (l := 0) c _ => toString c
        | .func (l := _ + 1) f ts => toString f ++ "(" ++ String.vecToStr (fun i => toStr (ts i)) ++ ")"

    instance : Repr (Term L ℕ) := ⟨fun t _ => toStr t⟩
    instance : ToString (Term L ℕ) := ⟨toStr⟩

    def toStr_oplus : Term L (α ⊕ β) → String :=
      fun t : Term L (α ⊕ β) =>
        match t with
        | .var k =>
          match k with
            | (Sum.inl l) => "#" ++ toString l
            | (Sum.inr l) => "&" ++ toString l
        | .func (l := 0) c _ => toString c
        | .func (l := _ + 1) f ts => toString f ++ "(" ++ String.vecToStr (fun i => toStr_oplus (ts i)) ++ ")"

    instance : Repr (Term L (α ⊕ β)) := ⟨fun t _ => toStr_oplus t⟩
    instance : ToString (Term L (α ⊕ β)) := ⟨toStr_oplus⟩
  end ToString
end Term

namespace BoundedFormula
  section ToString
    variable {L : Language} {α : Type} {n : ℕ}
    variable [∀ k, ToString (L.Functions k)] [∀ k, ToString (L.Relations k)] [ToString α]

    def toStr {n} : BoundedFormula L α n → String
      | .falsum                    => "⊥"
      | .equal t₁ t₂               => toString t₁ ++ " = " ++ toString t₂
      | .rel R ts                  => toString R ++ "(" ++ String.vecToStr (fun i => toString (ts i)) ++ ")"
      | .imp f₁ f₂                 => "(" ++ toStr f₁ ++ " → " ++ toStr f₂ ++ ")"
      | .all f                     => "∀" ++ toStr f

    instance : Repr (BoundedFormula L α n) := ⟨fun t _ => toStr t⟩
    instance : ToString (BoundedFormula L α n) := ⟨toStr⟩
  end ToString
end BoundedFormula

namespace Languages
  namespace LPA
    inductive Func : ℕ → Type _ where
      | zero : Func 0
      | succ : Func 1
      | add : Func 2
      | mult : Func 2
      | neg : Func 1
      | conj : Func 2
      | disj : Func 2
      | cond : Func 2
      | forall : Func 1
      | exists : Func 1
      | denote : Func 1
      | subs : Func 3
      deriving DecidableEq

    inductive Rel : ℕ → Type _ where
      | var : Rel 1
      | const : Rel 1
      | term : Rel 1
      | clterm: Rel 1
      | forml : Rel 1
      | sentencel: Rel 1
      | formlt : Rel 1
      | sentencelt : Rel 1
      deriving DecidableEq

    def signature : Language :=
      ⟨Func, Rel⟩

    def funToStr {n}: Func n → String
      | .zero => "0"
      | .succ => "S"
      | .add => "+"
      | .mult => "×"
      | .neg => "𝑛𝑒𝑔"
      | .conj => "𝑐𝑜𝑛𝑗"
      | .disj => "𝑑𝑖𝑠𝑗"
      | .cond => "𝑐𝑜𝑛𝑑"
      | .forall => "𝑎𝑙𝑙"
      | .exists => "𝑒𝑥"
      | .denote => "𝑑𝑒𝑛"
      | .subs => "𝑠𝑢𝑏𝑠"
    instance {n : ℕ}: ToString (signature.Functions n) := ⟨funToStr⟩

    def relToStr {n} : signature.Relations n → String
      | .var => "𝑣𝑎𝑟"
      | .const => "𝑐𝑜𝑛𝑠𝑡"
      | .term => "𝑡𝑒𝑟𝑚"
      | .clterm => "𝑐𝑙𝑡𝑒𝑟𝑚"
      | .forml => "𝑓𝑜𝑟𝑚𝑙"
      | .sentencel => "𝑠𝑒𝑛𝑡𝑙"
      | .formlt => "𝑓𝑜𝑟𝑚𝑙𝑡"
      | .sentencelt => "𝑠𝑒𝑛𝑡𝑙𝑡"
    instance {n} : ToString (signature.Relations n) := ⟨relToStr⟩

    /-
    Useful notation
    -/
    scoped notation "S(" n ")" => Term.func Func.succ ![n]
    scoped notation "zero" => Term.func Func.zero ![]
    scoped notation n "add" m => Term.func Func.add ![n,m]
    scoped notation n "times" m => Term.func Func.mult ![n,m]
    scoped notation n "⬝∧" m => Term.func Func.conj ![n,m]
    scoped notation n "⬝∨" m => Term.func Func.disj ![n,m]
    scoped notation "⬝∼" n => Term.func Func.neg ![n]
    scoped notation n "⬝⟹" m => Term.func Func.cond ![n,m]
    scoped notation "⬝∀" n => Term.func Func.forall ![n]
    scoped notation "⬝∃" n => Term.func Func.exists ![n]
    scoped notation "⬝°"n  => Term.func Func.denote ![n]
    scoped notation "Subs(" n "," x "," t ")" => Term.func Func.subs ![n, x, t]
    scoped notation "Var(" x ")" => BoundedFormula.rel Rel.var ![x]
    scoped notation "Const(" c ")" => BoundedFormula.rel Rel.const ![c]
    scoped notation "Trm(" t ")" => BoundedFormula.rel Rel.term ![t]
    scoped notation "ClosedTerm(" t")" => BoundedFormula.rel Rel.clterm ![t]
    scoped notation "FormL(" t ")" => BoundedFormula.rel Rel.forml ![t]
    scoped notation "SentenceL(" t ")" => BoundedFormula.rel Rel.sentencel ![t]
    scoped notation "FormLT(" t ")" => BoundedFormula.rel Rel.formlt ![t]
    scoped notation "SentenceLT(" t ")" => BoundedFormula.rel Rel.sentencelt ![t]
    abbrev ℒ := signature
    scoped[Languages] prefix:arg "#" => FirstOrder.Language.Term.var ∘ Sum.inl

    /-
    Some useful terms
    -/
    variable {α : Type}
    def null : Term signature α :=
      zero

    def numeral : ℕ → Term signature α
      | .zero => zero
      | .succ n => S(numeral n)

    section Coding
      variable {k : ℕ}
      def Func_enc : signature.Functions k → ℕ
        | .zero => Nat.pair 0 0 + 1
        | .succ => Nat.pair 1 0 + 1
        | .denote => Nat.pair 1 1 + 1
        | .exists => Nat.pair 1 2 + 1
        | .forall => Nat.pair 1 3 + 1
        | .neg => Nat.pair 1 4 + 1
        | .add => Nat.pair 2 0 + 1
        | .mult => Nat.pair 2 1 + 1
        | .cond => Nat.pair 2 2 + 1
        | .disj => Nat.pair 2 3 + 1
        | .conj => Nat.pair 2 4 + 1
        | .subs => Nat.pair 3 0 + 1

      def Func_dec : (n : ℕ) → Option (signature.Functions k)
        | 0 => none
        | e + 1 =>
          match k with
            | 0 =>
              match e.unpair.2 with
                | 0 => some (.zero)
                | _ => none
            | 1 =>
              match e.unpair.2 with
                | 0 => some (.succ)
                | 1 => some (.denote)
                | 2 => some (.exists)
                | 3 => some (.forall)
                | 4 => some (.neg)
                | _ => none
            | 2 =>
              match e.unpair.2 with
                | 0 => some (.add)
                | 1 => some (.mult)
                | 2 => some (.cond)
                | 3 => some (.disj)
                | 4 => some (.conj)
                | _ => none
            | 3 =>
              match e.unpair.2 with
                | 0 => some (.subs)
                | _ => none
            | _ => none

      lemma Func_enc_dec : ∀ f : signature.Functions k, Func_dec (Func_enc f) = (some f) := by
        intro h
        induction h
        simp [Func_enc,Nat.pair,Func_dec]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

      instance enc_f : Encodable (signature.Functions k) where
        encode := Func_enc
        decode := Func_dec
        encodek := Func_enc_dec

      def Rel_enc : signature.Relations k → ℕ
        | .var => Nat.pair 1 0 + 1
        | .const => Nat.pair 1 1 + 1
        | .term => Nat.pair 1 2 + 1
        | .clterm => Nat.pair 1 3 + 1
        | .forml => Nat.pair 1 4 + 1
        | .sentencel => Nat.pair 1 5 + 1
        | .formlt => Nat.pair 1 6 + 1
        | .sentencelt => Nat.pair 1 7 + 1

      def Rel_dec : (n : ℕ) → Option (signature.Relations k)
        | 0 => none
        | e + 1 =>
          match k with
            | 1 =>
              match e.unpair.2 with
                | 0 => some .var
                | 1 => some .const
                | 2 => some .term
                | 3 => some .clterm
                | 4 => some .forml
                | 5 => some .sentencel
                | 6 => some .formlt
                | 7 => some .sentencelt
                | _ => none
            | _ => none

      lemma Rel_enc_dec : ∀ f : signature.Relations k, Rel_dec (Rel_enc f) = (some f) := by
        intro h
        induction h
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

      instance enc_r : Encodable (signature.Relations k) where
        encode := Rel_enc
        decode := Rel_dec
        encodek := Rel_enc_dec

    end Coding
  end LPA

  namespace L_T

    inductive Func : ℕ → Type _ where
      | zero : Func 0
      | succ : Func 1
      | add : Func 2
      | mult : Func 2
      | neg : Func 1
      | conj : Func 2
      | disj : Func 2
      | cond : Func 2
      | forall : Func 1
      | exists : Func 1
      | denote : Func 1
      | subs : Func 3
      deriving DecidableEq

    inductive Rel : ℕ → Type _ where
      | var : Rel 1
      | const : Rel 1
      | t : Rel 1
      | term : Rel 1
      | clterm: Rel 1
      | forml : Rel 1
      | sentencel: Rel 1
      | formlt : Rel 1
      | sentencelt : Rel 1
      deriving DecidableEq

    def signature : Language :=
      ⟨Func, Rel⟩

    variable {n : ℕ}
    def funToStr : Func n → String
      | .zero => "0"
      | .succ => "S"
      | .add => "+"
      | .mult => "×"
      | .neg => "𝑛𝑒𝑔"
      | .conj => "𝑐𝑜𝑛𝑗"
      | .disj => "𝑑𝑖𝑠𝑗"
      | .cond => "𝑐𝑜𝑛𝑑"
      | .forall => "𝑎𝑙𝑙"
      | .exists => "𝑒𝑥"
      | .denote => "𝑑𝑒𝑛"
      | .subs => "𝑠𝑢𝑏𝑠"
    instance : ToString (signature.Functions n) := ⟨funToStr⟩

    def relToStr : signature.Relations n → String
      | .var => "𝑣𝑎𝑟"
      | .const => "𝑐𝑜𝑛𝑠𝑡"
      | .t => "T"
      | .term => "𝑡𝑒𝑟𝑚"
      | .clterm => "𝑐𝑙𝑡𝑒𝑟𝑚"
      | .forml => "𝑓𝑜𝑟𝑚𝑙"
      | .sentencel => "𝑠𝑒𝑛𝑡𝑙"
      | .formlt => "𝑓𝑜𝑟𝑚𝑙𝑡"
      | .sentencelt => "𝑠𝑒𝑛𝑡𝑙𝑡"
    instance : ToString (signature.Relations n) := ⟨relToStr⟩

    /-
    Some useful notation
    -/
    scoped notation "T(" n ")" => BoundedFormula.rel Rel.t ![n]
    scoped notation "S(" n ")" => Term.func Func.succ ![n]
    scoped notation "zero" => Term.func Func.zero ![]
    scoped notation n "add" m => Term.func Func.add ![n,m]
    scoped notation n "times" m => Term.func Func.mult ![n,m]
    scoped notation n "⬝∧" m => Term.func Func.conj ![n,m]
    scoped notation n "⬝∨" m => Term.func Func.disj ![n,m]
    scoped notation "⬝∼" n => Term.func Func.neg ![n]
    scoped notation n "⬝⟹" m => Term.func Func.cond ![n,m]
    scoped notation "⬝∀" n => Term.func Func.forall ![n]
    scoped notation "⬝∃" n => Term.func Func.exists ![n]
    scoped notation "⬝°" n  => Term.func Func.denote ![n]
    scoped notation "Subs(" n "," x "," t ")" => Term.func Func.subs ![n, x, t]
    scoped notation "Var(" x ")" => BoundedFormula.rel L_T.Rel.var ![x]
    scoped notation "Const(" c ")" => BoundedFormula.rel L_T.Rel.const ![c]
    scoped notation "Trm(" t ")" => BoundedFormula.rel Rel.term ![t]
    scoped notation "ClosedTerm(" t")" => BoundedFormula.rel L_T.Rel.clterm ![t]
    scoped notation "FormL(" t ")" => BoundedFormula.rel L_T.Rel.forml ![t]
    scoped notation "SentenceL(" t ")" => BoundedFormula.rel L_T.Rel.sentencel ![t]
    scoped notation "FormLT(" t ")" => BoundedFormula.rel L_T.Rel.formlt ![t]
    scoped notation "SentenceLT(" t ")" => BoundedFormula.rel L_T.Rel.sentencelt ![t]
    abbrev ℒₜ := signature

    variable {α : Type}
    def null : Term signature α :=
      zero

    def numeral : ℕ → Term signature α
      | .zero => zero
      | .succ n => S(numeral n)

    section Coding
      variable {k : ℕ}
      def Func_enc : signature.Functions k → ℕ
        | .zero => Nat.pair 0 0 + 1
        | .succ => Nat.pair 1 0 + 1
        | .denote => Nat.pair 1 1 + 1
        | .exists => Nat.pair 1 2 + 1
        | .forall => Nat.pair 1 3 + 1
        | .neg => Nat.pair 1 4 + 1
        | .add => Nat.pair 2 0 + 1
        | .mult => Nat.pair 2 1 + 1
        | .cond => Nat.pair 2 2 + 1
        | .disj => Nat.pair 2 3 + 1
        | .conj => Nat.pair 2 4 + 1
        | .subs => Nat.pair 3 0 + 1

      def Func_dec : (n : ℕ) → Option (signature.Functions k)
        | 0 => none
        | e + 1 =>
          match k with
            | 0 =>
              match e.unpair.2 with
                | 0 => some (.zero)
                | _ => none
            | 1 =>
              match e.unpair.2 with
                | 0 => some (.succ)
                | 1 => some (.denote)
                | 2 => some (.exists)
                | 3 => some (.forall)
                | 4 => some (.neg)
                | _ => none
            | 2 =>
              match e.unpair.2 with
                | 0 => some (.add)
                | 1 => some (.mult)
                | 2 => some (.cond)
                | 3 => some (.disj)
                | 4 => some (.conj)
                | _ => none
            | 3 =>
              match e.unpair.2 with
                | 0 => some (.subs)
                | _ => none
            | _ => none

      lemma Func_enc_dec : ∀ f : signature.Functions k, Func_dec (Func_enc f) = (some f) := by
        intro h
        induction h
        simp [Func_enc,Nat.pair,Func_dec]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

      instance enc_f : Encodable (signature.Functions k) where
        encode := Func_enc
        decode := Func_dec
        encodek := Func_enc_dec

      def Rel_enc : signature.Relations k → ℕ
        | .var => Nat.pair 1 0 + 1
        | .const => Nat.pair 1 1 + 1
        | .term => Nat.pair 1 2 + 1
        | .clterm => Nat.pair 1 3 + 1
        | .forml => Nat.pair 1 4 + 1
        | .sentencel => Nat.pair 1 5 + 1
        | .formlt => Nat.pair 1 6 + 1
        | .sentencelt => Nat.pair 1 7 + 1
        | .t => Nat.pair 1 8 + 1

      def Rel_dec : (n : ℕ) → Option (signature.Relations k)
        | 0 => none
        | e + 1 =>
          match k with
            | 1 =>
              match e.unpair.2 with
                | 0 => some .var
                | 1 => some .const
                | 2 => some .term
                | 3 => some .clterm
                | 4 => some .forml
                | 5 => some .sentencel
                | 6 => some .formlt
                | 7 => some .sentencelt
                | 8 => some .t
                | _ => none
            | _ => none

      lemma Rel_enc_dec : ∀ f : signature.Relations k, Rel_dec (Rel_enc f) = (some f) := by
        intro h
        induction h
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]
        simp [Rel_enc,Nat.pair,Rel_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]


      instance enc_r : Encodable (signature.Relations k) where
        encode := Rel_enc
        decode := Rel_dec
        encodek := Rel_enc_dec

    end Coding
  end L_T

namespace TermEncoding
  variable {L : Language}[∀i, Encodable (L.Functions i)][∀i, Encodable (L.Relations i)]
  /-- Encodes terms as natural numbers -/
  def term_tonat_N : Term L ℕ → ℕ :=
    fun t => Encodable.encodeList (Term.listEncode t)
  def term_tonat_Empty : Term L (Empty ⊕ Fin 0) → ℕ :=
    fun t => Encodable.encodeList (Term.listEncode t)
  /-- Encodes BoundedFormulas as natural numbers -/
  def formula_N_tonat {n : ℕ} : BoundedFormula L ℕ n → ℕ :=
    fun f => Encodable.encodeList (BoundedFormula.listEncode f)
  /-- Encodes BoundedFormulas as natural numbers -/
  def formula_Empty_tonat : BoundedFormula L Empty 0 → ℕ :=
    fun f => Encodable.encodeList (BoundedFormula.listEncode f)

  scoped notation "⌜" φ "⌝" => L_T.numeral (formula_N_tonat φ)
  scoped notation "⌜" φ "⌝" => L_T.numeral (formula_Empty_tonat φ)
  scoped notation "⌜" φ "⌝" => LPA.numeral (formula_N_tonat φ)
  scoped notation "⌜" t₁ "⌝" => L_T.numeral (term_tonat_N t₁)
  scoped notation "⌜" t₁ "⌝" => L_T.numeral (term_tonat_Empty t₁)

end TermEncoding

  open LPA
  open L_T

  /--
  A coercion from PA.lpa formulas to L_T.lt formulas as all lpa formulas are
  also lt formulas
  -/
  def to_lt_func ⦃arity : ℕ⦄ : (ℒ.Functions arity) → (ℒₜ.Functions arity)
    | .zero => .zero
    | .succ => .succ
    | .add => .add
    | .mult => .mult
    | .neg => .neg
    | .conj => .conj
    | .disj => .disj
    | .cond => .cond
    | .forall => .forall
    | .exists => .exists
    | .denote => .denote
    | .subs => .subs

  def to_l_func ⦃arity : ℕ⦄ : (ℒₜ.Functions arity) → (ℒ.Functions arity)
    | .zero => .zero
    | .succ => .succ
    | .add => .add
    | .mult => .mult
    | .neg => .neg
    | .conj => .conj
    | .disj => .disj
    | .cond => .cond
    | .forall => .forall
    | .exists => .exists
    | .denote => .denote
    | .subs => .subs
  
  def to_l_term {α : Type} : (ℒₜ.Term α) → (ℒ.Term α)
    | .var f => .var f
    | .func f ts => .func (to_l_func f) (fun i => to_l_term (ts i))

  def to_lt_rel ⦃n : ℕ⦄ : (ℒ.Relations n) → (ℒₜ.Relations n)
      | .var => .var
      | .const => .const
      | .term => .term
      | .clterm => .clterm
      | .forml => .forml
      | .sentencel => .sentencel
      | .formlt => .formlt
      | .sentencelt => .sentencelt

  def ϕ : LHom ℒ ℒₜ where
      onFunction := to_lt_func
      onRelation := to_lt_rel
  
  instance : Coe (Formula ℒ ℕ) (Formula ℒₜ ℕ) where
    coe := LHom.onFormula ϕ
  def lt_set : Set (ℒ.Formula ℕ) → Set (ℒₜ.Formula ℕ) :=
    fun s => s.image (ϕ.onFormula)
  instance : Coe (Set (ℒ.Formula ℕ)) (Set (ℒₜ.Formula ℕ)) where
    coe := lt_set
  instance : Coe (Sentence ℒ) (Sentence ℒₜ) where
    coe := LHom.onSentence ϕ
  instance : Coe (Term ℒ (Empty ⊕ Fin 0)) (Term ℒₜ (Empty ⊕ Fin 0)) where
    coe := LHom.onTerm ϕ
  instance : Coe (Theory ℒ) (Theory ℒₜ) where
    coe := LHom.onTheory ϕ

  variable {L : Language}{α : Type}
  def fml_term {n : ℕ} : L.Term (Empty ⊕ Fin n) → L.Term (ℕ ⊕ Fin n)
    | .var (.inl _) => Term.var (.inl 1)
    | .var (.inr _) => Term.var (.inl 1)
    | .func f ts => .func f (fun i => fml_term (ts i))
  instance {n : ℕ} : Coe (L.Term (Empty ⊕ Fin n)) (L.Term (ℕ ⊕ Fin n)) where
    coe := fml_term
  def fml : {n : ℕ} → L.BoundedFormula Empty n → L.BoundedFormula ℕ n
    | _, .falsum => .falsum
    | _, .equal t₁ t₂ => .equal t₁ t₂
    | _, .rel R ts => .rel R (fun i => ts i)
    | _, .imp φ ψ => .imp (fml φ) (fml ψ)
    | _, .all φ => .all (fml φ)
  instance : Coe (L.Sentence) (L.Formula ℕ) where
    coe := fml
  def fml_set : L.Theory → Set (L.Formula ℕ) := fun t => t.image fml
  instance : Coe (L.Theory) (Set (L.Formula ℕ)) where
    coe := fml_set

end Languages

namespace FirstOrder.Language.BoundedFormula
  variable {L : Language}{α : Type}{n : ℕ}
  def g₁ : (Term L ℕ) → ℕ → (Term L ℕ) :=
    fun t : Term L ℕ => fun k : ℕ => ite (k = 0) t (Term.var (k - 1))
  scoped notation A "/[" t "]" => subst A (g₁ t)
  def g₂ {n : ℕ} : (Term L (ℕ ⊕ Fin n)) → (ℕ ⊕ Fin n) → (Term L (ℕ ⊕ Fin n)) := fun t : Term L (ℕ ⊕ Fin n) => fun k : (ℕ ⊕ Fin n) => match k with
  | .inl n =>
    match n with
    | 0 => t
    | .succ n => .var (Sum.inl n)
  | .inr n => .var (.inr n)
  scoped notation A "/[" t "]" => subst A (g₂ t)
  
  def land (f₁ f₂: BoundedFormula L α n) :=
    ∼(f₁ ⟹ ∼f₂)
  scoped notation f₁ "∧'" f₂ => land f₁ f₂
  def lor (f₁ f₂ : BoundedFormula L α n) :=
    ((∼f₁) ⟹ f₂)
  scoped notation f₁ "∨'" f₂ => lor f₁ f₂
  noncomputable def finset_iSup (s : Finset (L.Formula ℕ)) : L.Formula ℕ :=
    (s.1.toList).foldr (· ⊔ ·) ⊥
end FirstOrder.Language.BoundedFormula


namespace SyntaxAxioms
open Languages
open L_T
open LPA
open BoundedFormula
open TermEncoding

def neg_repres (φ : Formula ℒ ℕ) : Sentence ℒₜ :=
  (⬝∼ ⌜φ⌝) =' (⌜∼φ⌝)
def conj_repres (φ ψ : Formula ℒ ℕ): Sentence ℒₜ :=
  (⌜φ⌝ ⬝∧ ⌜ψ⌝) =' (⌜φ ∧' ψ⌝)
def disj_repres (φ ψ : Formula ℒ ℕ) : Sentence ℒₜ :=
  (⌜φ⌝ ⬝∨ ⌜ψ⌝) =' (⌜φ ∨' ψ⌝)
def cond_repres (φ ψ : Formula ℒ ℕ) : Sentence ℒₜ :=
  (⌜φ⌝ ⬝⟹ ⌜ψ⌝) =' (⌜φ ⟹ ψ⌝)
def forall_repres (φ : BoundedFormula ℒ ℕ 1) : Sentence ℒₜ :=
  (⬝∀ ⌜φ⌝) =' (⌜∀'φ⌝)
def exists_repres (φ : BoundedFormula ℒ ℕ 1) : Sentence ℒₜ :=
  (⬝∃ ⌜φ⌝) =' (⌜∃'φ⌝)
def subs_repres (φ : BoundedFormula ℒ ℕ 1) (x : Term ℒ ℕ) (t : Term ℒ ℕ ) : Sentence ℒₜ :=
  Subs(⌜φ⌝, ⌜x⌝, ⌜t⌝) =' ⌜φ /[ t ]⌝
def term_repres (φ : Formula ℒ ℕ) : Sentence ℒₜ :=
  Trm( ⌜φ⌝ )
def formulaL_repres (φ : Formula ℒ ℕ) : Sentence ℒₜ :=
  FormL( ⌜φ⌝ )
def formulaL_T_repres (φ : Formula ℒ ℕ) : Sentence ℒₜ :=
  FormLT( ⌜φ⌝ )
def sentenceL_repres (φ : Formula ℒ ℕ) : Sentence ℒₜ :=
  SentenceL( ⌜φ⌝ )
def sentenceL_T_respres (φ : Formula ℒ ℕ) : Sentence ℒₜ :=
  SentenceLT( ⌜φ⌝ )
def closed_term_repres (t : Term ℒ (Empty ⊕ Fin 0)) : Sentence ℒₜ :=
  ClosedTerm( ⌜t⌝ )
def var_repres (φ : Formula ℒ ℕ) : Sentence ℒₜ :=
  Var( ⌜φ⌝ )
def const_repres (φ : Formula ℒ ℕ) : Sentence ℒₜ :=
  Const( ⌜φ⌝ )
def denote_repres (t : Term ℒ (Empty ⊕ Fin 0)) : Sentence ℒₜ :=
  ClosedTerm(⌜t⌝) ⟹ ((⬝°(⌜t⌝)) =' t)

end SyntaxAxioms

namespace SyntaxTheory
open Languages
open L_T
open SyntaxAxioms
inductive syntax_theory : Theory ℒₜ where
  | negation_representation {φ} : syntax_theory (neg_repres φ)
  | conjunction_representation {φ ψ} : syntax_theory (conj_repres φ ψ)
  | disjunction_representation {φ ψ} : syntax_theory (disj_repres φ ψ)
  | conditional_representation {φ ψ} : syntax_theory (cond_repres φ ψ)
  | forall_representation {φ} : syntax_theory (forall_repres φ)
  | exists_representation {φ} : syntax_theory (exists_repres φ)
  | term_representation {φ} : syntax_theory (term_repres φ)
  | formula_L_representation {φ} : syntax_theory (formulaL_repres φ)
  | formula_L_T_representation {φ} : syntax_theory (formulaL_T_repres φ)
  | sentence_L_representation {φ} : syntax_theory (sentenceL_repres φ)
  | sentence_L_T_representation {φ} : syntax_theory (sentenceL_T_respres φ)
  | closed_term_representation {φ} : syntax_theory (closed_term_repres φ)
  | variable_representation {φ} : syntax_theory (var_repres φ)
  | constant_representation {φ} : syntax_theory (const_repres φ)
  | denote_representation {t} : syntax_theory (denote_repres t)
end SyntaxTheory
