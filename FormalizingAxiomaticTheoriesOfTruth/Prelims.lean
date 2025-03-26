import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Encoding
import Mathlib.Data.Set.Enumerate

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
    def toStr : Term L (α ⊕ β) → String :=
      fun t : Term L (α ⊕ β) =>
        match t with
        | .var k =>
          match k with
            | (Sum.inl l) => "#" ++ toString l
            | (Sum.inr l) => "&" ++ toString l
        | .func (l := 0) c _ => toString c
        | .func (l := _ + 1) f ts => toString f ++ "(" ++ String.vecToStr (fun i => toStr (ts i)) ++ ")"

    instance : Repr (Term L (α ⊕ β)) := ⟨fun t _ => toStr t⟩
    instance : ToString (Term L (α ⊕ β)) := ⟨toStr⟩
  end ToString
end Term

namespace BoundedFormula
  section ToString
    variable {L : Language} {α : Type}
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
  namespace L_PA
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
      | num : Func 1
      | denote : Func 1
      | subs : Func 3

    inductive Rel : ℕ → Type _ where
      | var : Rel 1
      | const : Rel 1
      | term : Rel 1
      | clterm: Rel 1
      | forml : Rel 1
      | sentencel: Rel 1
      | formlt : Rel 1
      | sentencelt : Rel 1

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
      | .num => "𝑛𝑢𝑚"
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
    instance : ToString (signature.Relations n) := ⟨relToStr⟩

    /-
    Useful notation
    -/
    notation "S(" n ")" => Term.func Func.succ ![n]
    notation "zero" => Term.func Func.zero ![]
    notation n "add" m => Term.func Func.add ![n,m]
    notation n "times" m => Term.func Func.mult ![n,m]
    notation n "and" m => Term.func Func.conj ![n,m]
    notation n "or" m => Term.func Func.disj ![n,m]
    notation "not" n => Term.func Func.neg ![n]
    notation n "then" m => Term.func Func.cond ![n,m]
    notation "forall" n => Term.func Func.forall ![n]
    notation "exists" n => Term.func Func.exists ![n]
    notation "num(" n ")" => Term.func Func.num ![n]
    notation n "°" => Term.func Func.denote ![n]
    notation "Subs(" n "," x "," t ")" => Term.func Func.subs ![n, x, t]
    notation "Var(" x ")" => Formula.rel Rel.var ![x]
    notation "Const(" c ")" => Formula.rel Rel.const ![c]
    notation "Term(" t ")" => Formula.rel Rel.term ![t]
    notation "ClosedTerm(" t")" => Formula.rel Rel.clterm ![t]
    notation "FormL(" t ")" => Formula.rel Rel.forml ![t]
    notation "SentenceL(" t ")" => Formula.rel Rel.sentencel ![t]
    notation "FormLT(" t ")" => Formula.rel Rel.formlt ![t]
    notation "SentenceLT(" t ")" => Formula.rel Rel.sentencelt ![t]
    notation "ℒ" => signature
    scoped[Languages] prefix:arg "#" => FirstOrder.Language.Term.var ∘ Sum.inl

    /-
    Some useful terms
    -/
    def null : Term signature α :=
      zero
    def numeral : ℕ → Term signature α
      | .zero => zero
      | .succ n => S(numeral n)

    section Coding
      def Func_enc : signature.Functions k → ℕ
        | .zero => Nat.pair 0 0 + 1
        | .succ => Nat.pair 1 0 + 1
        | .denote => Nat.pair 1 1 + 1
        | .exists => Nat.pair 1 2 + 1
        | .forall => Nat.pair 1 3 + 1
        | .neg => Nat.pair 1 4 + 1
        | .num => Nat.pair 1 5 + 1
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
                | 5 => some (.num)
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

      lemma Func_enc_dec {k : ℕ}: ∀ f : signature.Functions k, Func_dec (Func_enc f) = (some f) := by
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
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

      instance enc_f (k : ℕ) : Encodable (signature.Functions k) where
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

      lemma Rel_enc_dec {k : ℕ}: ∀ f : signature.Relations k, Rel_dec (Rel_enc f) = (some f) := by
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

      instance enc_r (k : ℕ) : Encodable (signature.Relations k) where
        encode := Rel_enc
        decode := Rel_dec
        encodek := Rel_enc_dec

    end Coding
  end L_PA

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
      | num : Func 1
      | denote : Func 1
      | subs : Func 3

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
      | .num => "𝑛𝑢𝑚"
      | .denote => "𝑑𝑒𝑛"
      | .subs => "𝑠𝑢𝑏𝑠"
    instance {n : ℕ}: ToString (signature.Functions n) := ⟨funToStr⟩

    def relToStr {n} : signature.Relations n → String
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
    prefix:60 "T" => Formula.rel Rel.t
    -- notation "S(" n ")" => Term.func Func.succ ![n]
    -- notation "zero" => Term.func Func.zero ![]
    -- notation n "add" m => Term.func Func.add ![n,m]
    -- notation n "times" m => Term.func Func.mult ![n,m]
    -- notation n "and" m => Term.func Func.conj ![n,m]
    -- notation n "or" m => Term.func Func.disj ![n,m]
    -- notation "num(" n ")" => Term.func Func.num ![n]
    -- notation "not" n => Term.func Func.neg ![n]
    -- notation n "then" m => Term.func Func.cond ![n,m]
    -- notation "forall" n => Term.func Func.forall ![n]
    -- notation "exists" n => Term.func Func.exists ![n]
    -- notation n "°" => Term.func Func.denote ![n]
    -- notation "Subs(" n "," x "," t ")" => Term.func Func.subs ![n, x, t]
    -- notation "Var(" x ")" => Formula.rel Rel.var ![x]
    -- notation "Const(" c ")" => Formula.rel Rel.const ![c]
    -- notation "Term(" t ")" => Formula.rel Rel.term ![t]
    -- notation "ClosedTerm(" t")" => Formula.rel Rel.clterm ![t]
    -- notation "FormL(" t ")" => Formula.rel Rel.forml ![t]
    -- notation "SentenceL(" t ")" => Formula.rel Rel.sentencel ![t]
    -- notation "FormLT(" t ")" => Formula.rel Rel.formlt ![t]
    -- notation "SentenceLT(" t ")" => Formula.rel Rel.sentencelt ![t]
    notation "ℒₜ" => signature

    section Coding
      def Func_enc : signature.Functions k → ℕ
        | .zero => Nat.pair 0 0 + 1
        | .succ => Nat.pair 1 0 + 1
        | .denote => Nat.pair 1 1 + 1
        | .exists => Nat.pair 1 2 + 1
        | .forall => Nat.pair 1 3 + 1
        | .neg => Nat.pair 1 4 + 1
        | .num => Nat.pair 1 5 + 1
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
                | 5 => some (.num)
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

      lemma Func_enc_dec {k : ℕ}: ∀ f : signature.Functions k, Func_dec (Func_enc f) = (some f) := by
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
        simp [Func_enc,Nat.pair,Func_dec,Nat.unpair,Nat.sqrt,Nat.sqrt.iter]

      instance enc_f (k : ℕ) : Encodable (signature.Functions k) where
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

      lemma Rel_enc_dec {k : ℕ}: ∀ f : signature.Relations k, Rel_dec (Rel_enc f) = (some f) := by
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


      instance enc_r (k : ℕ) : Encodable (signature.Relations k) where
        encode := Rel_enc
        decode := Rel_dec
        encodek := Rel_enc_dec

    end Coding
  end L_T

  /-
  Some useful notation
  -/
  variable (l : Language)
  abbrev Fml : Type _ := Formula l ℕ -- perhaps

  /-
  A coercion from PA.lpa formulas to L_T.lt formulas as all lpa formulas are
  also lt formulas
  -/
  def to_lt_func ⦃arity : ℕ⦄ : (L_PA.Func arity) → (L_T.Func arity)
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
    | .num => .num
    | .denote => .denote
    | .subs => .subs

  def to_lt_rel ⦃n : ℕ⦄ : (L_PA.signature.Relations n) → (L_T.signature.Relations n)
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
end Languages

namespace encoding

end encoding

namespace Calculus
  open Languages
  open BoundedFormula
  variable {P : Language}{n : ℕ}{α : Type}
  /- Some notation -/
  notation f " ↑' " n " at "  m => liftAt n m f
  notation f "↑" n => f ↑' n at 0
  def g₁ : (Term P ℕ) → ℕ → ℕ → (Term P ℕ) :=
    fun t : Term P ℕ => (fun k : ℕ => (fun l : ℕ => ite (l = k) t (Term.var l)))
  notation A "/[" t "," n "]" => subst A (g₁ t n)

  def land (f₁ f₂: BoundedFormula P α n) :=
    ∼(f₁ ⟹ ∼f₂)
  notation f₁ "∧'" f₂ => land f₁ f₂
  def lor (f₁ f₂ : BoundedFormula P α n) :=
    (∼f₁ ⟹ f₂)
  notation f₁ "∨'" f₂ => lor f₁ f₂

  /-- Shifts all variable references one down so one is pushed into
  the to-be-bound category -/
  def shift_one_down : ℕ → ℕ ⊕ Fin 1
    | .zero => .inr Nat.zero
    | .succ n => .inl n

  /-- Shifts all free variables (that are not to be bound) up by one-/
  def shift_free_up : ℕ → ℕ ⊕ Fin 0
    | .zero => .inl (.succ .zero)
    | .succ n => .inl (.succ (n + 1))

  /-- Proof that addition is also transitive in BoundedFormula types -/
  def m_add_eq_add_m {m} : BoundedFormula P ℕ (m + n) → BoundedFormula P ℕ (n + m) := by
    rw[add_comm]
    intro h
    exact h
  instance {m} : Coe (BoundedFormula P ℕ (m + n)) (BoundedFormula P ℕ (n + m)) where
    coe := m_add_eq_add_m

  /-- Proof that adding zero als does nothing in BoundedFormula types -/
  def add_zero_does_nothing : BoundedFormula P ℕ (0 + n) → BoundedFormula P ℕ n := by
    intro h
    rw[zero_add] at h
    exact h
  instance : Coe (BoundedFormula P ℕ (0 + n)) (BoundedFormula P ℕ n) where
    coe := add_zero_does_nothing
  instance : Coe (BoundedFormula P ℕ (n + 0)) (BoundedFormula P ℕ (0 + n)) where
    coe := m_add_eq_add_m

  notation Δ"↑"  => (λf => (relabel shift_free_up f)) '' Δ
  notation A"↓" => relabel shift_one_down A

  /-- G3c sequent calculus -/
  inductive Derivable : (Set (Formula P ℕ)) → (Set (Formula P ℕ)) → Prop where
    | lax {Γ Δ} : ((Γ ∩ Δ) ≠ ∅) → (Derivable Γ Δ)
    | left_conjunction {A B Γ Δ} : Derivable (Γ ∪ {A, B}) Δ → Derivable (Γ ∪ {A ∧' B} ) Δ
    | left_disjunction {A B Γ Δ} : Derivable (Γ ∪ {A}) Δ → Derivable (Γ ∪ {B}) Δ → Derivable (Γ ∪ {A ∨' B}) Δ
    | left_implication {A B Γ Δ} : Derivable Γ (Δ ∪ {A}) → Derivable ({B} ∪ Γ) Δ → Derivable ({A ⟹ B} ∪ Γ) Δ
    | left_bot {Γ Δ} : Derivable ({⊥} ∪ Γ) Δ
    | right_conjunction {A B Γ Δ} : Derivable Γ (Δ ∪ {A}) → Derivable Γ (Δ ∪ {B}) → Derivable Γ (Δ ∪ {A ∧' B})
    | right_disjunction {A B Γ Δ} : Derivable Γ (Δ ∪ {A, B}) → Derivable Γ (Δ ∪ {A ∨' B})
    | right_implication {A B Γ Δ} : Derivable ({A} ∪ Γ) (Δ ∪ {B}) → Derivable Γ (Δ ∪ {A ⟹ B})
    | left_forall {A : Formula P ℕ} {B} {p : B = A↓} {t Γ Δ} : Derivable (Γ ∪ {(A/[t,0]), (∀'B)}) Δ → Derivable (Γ ∪ {∀'B}) Δ
    | left_exists {A B Γ Δ} {p : B = A↓} : Derivable ((Γ↑) ∪ {A}) (Δ↑) → Derivable ({∃' B} ∪ Γ) Δ
    | right_forall {A B Γ Δ} {p : B = A↓} : Derivable (Γ↑) ((Δ↑) ∪ {A}) → Derivable Γ (Δ ∪ {∀'B})
    | right_exists {A : Formula P ℕ} {B t Γ Δ} {p : B = A↓} : Derivable Γ (Δ ∪ {∃'B, A/[t,0]}) → Derivable Γ (Δ  ∪ {∃'B})

  def sent_term_to_formula_term : Term P (Empty ⊕ Fin n) → Term P (ℕ ⊕ Fin n)
      | .var n => match n with
        | .inl _ => .var (.inl Nat.zero)
        | .inr k => .var (.inr k)
      | .func f ts => .func f (fun i => sent_term_to_formula_term (ts i))
  instance : Coe (Term P (Empty ⊕ Fin n)) (Term P (ℕ ⊕ Fin n)) where
    coe := sent_term_to_formula_term
  def bf_empty_to_bf_N : ∀{n}, BoundedFormula P Empty n → BoundedFormula P ℕ n
      | _, .falsum => .falsum
      | _, .equal t₁ t₂ => .equal t₁ t₂
      | _, .rel R ts => .rel R (fun i => ts i)
      | _, .imp f₁ f₂ => .imp (bf_empty_to_bf_N f₁) (bf_empty_to_bf_N f₂)
      | _, .all f => .all (bf_empty_to_bf_N f)
  instance : Coe (Sentence P) (Formula P ℕ) where
    coe := bf_empty_to_bf_N
  instance : Coe (Theory P) (Set (Formula P ℕ)) where
    coe := fun Th : Theory P => bf_empty_to_bf_N '' Th

  def proves (Th : Theory P) (f : Formula P ℕ) : Prop :=
    ∃Δ: Set (Formula P ℕ), ∃_: Derivable Th (Δ ∪ {f}), ⊤
  notation Th " ⊢ " f => proves Th f


  def f₁ : Sentence ℒ :=
    ∀' (zero =' &0)
  def f₂ : Sentence ℒ :=
    zero =' zero
  def f₃ : Sentence ℒ :=
    ∀' ∼ (S(&0) =' zero)
  def T₁ : Theory ℒ := {f₁}

  open Term
  def gamma : Set (Formula ℒ ℕ) := {bf_empty_to_bf_N f₂}
  def delta : Set (Formula ℒ ℕ) := {bf_empty_to_bf_N f₂}
  lemma derivable : Derivable gamma delta := by
    have step1 : (gamma ∩ delta) ≠ ∅ := by
      rw[gamma,delta]
      simp[Set.inter]
    apply Derivable.lax step1
  example : T₁ ⊢ f₁ := by
    rw[proves]
    simp
    let Δ : Set (Formula ℒ ℕ) := ∅
    have step1 : Derivable (bf_empty_to_bf_N '' T₁) (insert (bf_empty_to_bf_N f₁) ∅) := by
      rw[T₁]
      apply Derivable.lax
      simp
    apply Exists.intro Δ step1
  def plero : Term ℒ ℕ :=
    zero
  def A : Formula ℒ ℕ := ∼(S(#0) =' zero)
  def G : Formula ℒ ℕ := A/[plero,0]
  example : A/[plero,0] = ∼(S(zero) =' zero) := by
    rw[A,plero]
    simp

    rw[A,BoundedFormula.not,plero,BoundedFormula.subst]
    have step1 : g₁ = fun t : Term P ℕ => fun k l : ℕ => ite (l = k) t (Term.var l) := by rfl
    simp[Sum.inl]
    simp[mapTermRel,g₁]
    rw[BoundedFormula.not]
    rw[mapTermRel.eq_def]
    simp
    apply And.intro
    rw[Term.subst.eq_def]

  #check A
  #check G
  #eval func L_PA.Func.succ ![var (Sum.inl 0)] =' func L_PA.Func.zero ![] ⟹ ⊥
  example : A = G := by
    rw[A,G,BoundedFormula.subst,plero,BoundedFormula.not]
    simp
    rw[A]
    rw[Function.comp]






  #eval mapTermRel (fun x t ↦ t.subst (Sum.elim (Term.relabel Sum.inl ∘ fun k ↦ match k with | 0 => func L.Func.zero ![] | x => var k) (var ∘ Sum.inr))) (fun x ↦ id) (fun x ↦ id) (func L.Func.succ ![var (Sum.inl 0)] =' func L.Func.zero ![])
  #eval ding
  def ding₂ : Formula ℒ ℕ := func L.Func.succ ![func L.Func.zero ![] ] =' func L.Func.zero ![]
  #eval ding₂
  example : ding = ding₂ := by
    rw[ding,ding₂]
    let test : Formula ℒ ℕ := S(zero) =' zero
    have step1 : ding = test := by
      rw[ding]
      simp[test]
      simp
      rfl
    rfl
  #check (∼(func L.Func.succ ![(var ∘ Sum.inl) 0] =' func L.Func.zero ![])).subst ![func L.Func.zero ![] ]
  #check subst A ![plero]
  #eval subst A ![plero]
  def B : Formula ℒ ℕ := A/[plero,0]
  def G₂ : Formula ℒ ℕ := ∼(S(zero) =' zero)
  #eval G
  #check mapTermRel (fun x t ↦ t.subst (Sum.elim (Term.relabel Sum.inl ∘ g₁ (func L.Func.zero ![]) 0) (var ∘ Sum.inr)))
  def f₃ : Formula ℒ ℕ := mapTermRel (fun x t ↦ t.subst (Sum.elim (Term.relabel Sum.inl ∘ g₁ (func L.Func.zero ![]) 0) (var ∘ Sum.inr))) (fun x ↦ id) (fun x ↦ id) (func L.Func.succ ![var (Sum.inl 0)] =' func L.Func.zero ![] ⟹ ⊥)
  #eval f₃
  def f₄ : Formula ℒ ℕ := ∼(func L.Func.succ ![func L.Func.zero ![] ] =' func L.Func.zero ![])
  #eval f₄
  example : f₃ = f₄ := by
    let f₅ : Formula ℒ ℕ := f₃
    let f₆ : Formula ℒ ℕ := f₄
    rw[f₃] at f₅

    rw[f₃,f₄]
    simp
  example : B = G := by
    rw[B,G,A,BoundedFormula.subst,BoundedFormula.not,plero]
    simp[g₁]

    sorry






  def f₃ : Formula ℒ ℕ := ∼ (S(zero) =' zero)
  example : gamma ⊢ ∼ (S(zero) =' zero) := by
    let A : Formula ℒ ℕ := ∼(S(#0) =' zero)
    let B : BoundedFormula ℒ ℕ 1 := A↓
    let Γ₁ : Set (Formula ℒ ℕ) :=
      {∼(S(zero) =' zero),∀'∼(S(&0) =' zero)}
    have step1 : A/[zero,0] = ∼(S(zero) =' zero)  := by
      simp[A,subst]
      rfl
      sorry

    have step1 : Γ₁ = {A/[zero,0],∀'B} := by
      simp[Γ₁]
    let Δ₁ : Set (Formula ℒ ℕ) :=
      {∼(S(zero) =' zero)}
    have step1 : Γ₁ ∩ Δ₁ ≠ ∅ := by
      simp[Γ₁,Δ₁]
    have step2 : Derivable Γ₁ Δ₁ := by
      apply Derivable.lax step1
    let Γ₂ : Set (Formula ℒ ℕ) := {∀'∼(S(&0) =' zero)}
    let Δ₂ : Set (Formula ℒ ℕ) := {∼ (S(zero) =' zero)}
    apply Derivable.left_forall at step2




    sorry










  def Syntax : Theory
    | .first φ : neg_repres. φ

  /- Below functions as inspiration -/
  inductive prf : Set (BoundedFormula L α n) → BoundedFormula L β m → Type _ where
  | axm Γ A : A ∈ Γ → prf Γ A
  | impI Γ A B : prf (insert A Γ) B → prf Γ (A ⟹ B)
  | impE Γ A B : prf Γ (A ⟹ B) → prf Γ A → prf Γ B
  | falsumE Γ A : prf (insert ∼A Γ) ⊥ → prf Γ A
  | allI Γ A : prf ((λf => f ↑ 1) '' Γ) A → prf Γ (∀' A)
  | allE₂ Γ A t : prf Γ (∀' A) → prf Γ (A/[t])
  | ref Γ t : prf Γ (t =' t')
  | subst₂ Γ s t f : prf Γ (s =' t) → prf Γ (f/[s]) → prf Γ (f/[t])
end Calculus

namespace PA
  open Languages
  open L
  open L_T

  /-
  Playing around
  -/

  def and_assoc : BoundedFormula ℒ (Fin 1) 0 :=
    ∀' ∀' ∀' (((&0 and &1) and &2) =' (&0 and (&1 and &2)))

  def commutative : BoundedFormula ℒ (Fin 1) 0 :=
    ∀' ∀' ((&0 and &1) =' (&1 and &0))

  def eq_forall : BoundedFormula ℒ (Fin 1) 1 :=
    ∀'(&0 =' forall &0)


  -- /-
  -- Running into trouble with the indexing typing in combination with substitution.
  -- -/

  -- def eq_var : BoundedFormula ℒ (Fin 1) 1 :=
  --   S(&0) =' S(&0)
  -- #check eq_var.toFormula
  -- #check eq_var/[L.null]
  -- def replace : Sentence ℒ :=
  --   ((S(&0) =' S(&0))/[L.null])
  -- example : (eq_var/[L.null]) = (S(L.null) =' S(L.null)) :=
  -- #check ∀' eq_var
  -- inductive axioms : Theory ℒ where
  -- | first : axioms (∀' ∼(L.null =' S(&0)))
  -- | second :axioms (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
  -- | third : axioms (∀' ((&0 add L.null) =' &0))
  -- | fourth : axioms (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
  -- | fifth : axioms (∀' ((&0 times L.null) =' L.null))
  -- | sixth : axioms (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
  -- | induction φ : (axioms (∼ (((φ/[L.null]) ⟹ ∼(∀'(φ ⟹ φ/[succ_var_term]))) ⟹ ∀' φ)))
  -- /-
  -- A coercion from ℒₚₐ Axioms to ℒₜ Axioms as all ℒₚₐ Axioms are also
  -- ℒₜ Axioms -/
  -- def
  -- def to_lt_T : Theory ℒ → Theory ℒₜ := by
  --   repeat rewrite[Theory]
  --   repeat rewrite[Set]
  --   intro set
  --   intro φ
  --   sorry
  -- inductive axioms : Theory ℒ where
  -- | first :
end PA
