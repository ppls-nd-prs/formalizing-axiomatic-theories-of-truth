import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Encoding
import Mathlib.Logic.Equiv.List

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
  namespace L
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
  end L

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
    notation "S(" n ")" => Term.func Func.succ ![n]
    notation "zero" => Term.func Func.zero ![]
    notation n "add" m => Term.func Func.add ![n,m]
    notation n "times" m => Term.func Func.mult ![n,m]
    notation n "and" m => Term.func Func.conj ![n,m]
    notation n "or" m => Term.func Func.disj ![n,m]
    notation "num(" n ")" => Term.func Func.num ![n]
    notation "not" n => Term.func Func.neg ![n]
    notation n "then" m => Term.func Func.cond ![n,m]
    notation "forall" n => Term.func Func.forall ![n]
    notation "exists" n => Term.func Func.exists ![n]
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

  section Coding
    /-- Encodes terms as natural numbers -/
    def term_tonat {n : ℕ} : Term ℒ (ℕ ⊕ (Fin n)) → ℕ :=
      fun t => Encodable.encodeList (Term.listEncode t)
    /-- Encodes BoundedFormulas as natural numbers -/
    def formula_tonat {n : ℕ} : BoundedFormula ℒ ℕ n → ℕ :=
      fun f => Encodable.encodeList (BoundedFormula.listEncode f)

    def t₁ : Term ℒ (ℕ ⊕ Fin 0) :=
      #0
    def f₁ : BoundedFormula ℒ ℕ 0 :=
      t₁ =' t₁

    #eval term_tonat t₁ -- output : 1
    #eval formula_tonat f₁ -- output : 52
  end Coding

  /-
  Some useful notation
  -/
  variable (l : Language)
  abbrev Fml : Type _ := Formula l ℕ -- perhaps

  /-
  A coercion from PA.lpa formulas to L_T.lt formulas as all lpa formulas are
  also lt formulas
  -/
  def to_lt_func ⦃arity : ℕ⦄ : (L.Func arity) → (L_T.Func arity)
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

  def to_lt_rel ⦃n : ℕ⦄ : (L.signature.Relations n) → (L_T.signature.Relations n)
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
  notation f " ↑' " n " at "  m => liftAt n m f
  notation f "↑" n => f ↑' n at 0
  notation A "/[" t "]" => subst A ![t]
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

namespace PA
  /-- The induction function for ℒₚₐ -/
  def induction (φ : BoundedFormula ℒₚₐ Empty 1) : Sentence ℒₚₐ :=
    ∼ (φ//[LPA.null] ⟹ (∼(∀'(φ ⟹ (relabel g (φ.toFormula/[S(&0)])))))) ⟹ ∀'(φ)

  /-- Peano arithemtic -/
  inductive peano_arithmetic : Theory ℒₚₐ where
  | first : peano_arithmetic (∀' ∼(LPA.null =' S(&0)))
  | second :peano_arithmetic (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
  | third : peano_arithmetic (∀' ((&0 add LPA.null) =' &0))
  | fourth : peano_arithmetic (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
  | fifth : peano_arithmetic (∀' ((&0 times LPA.null) =' LPA.null))
  | sixth : peano_arithmetic (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
  | induction (φ) : peano_arithmetic (induction φ)

  notation "𝐏𝐀" => peano_arithmetic


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
