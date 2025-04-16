import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Encoding
import Mathlib.Data.Set.Enumerate
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
    notation n "⬝∧" m => Term.func Func.conj ![n,m]
    notation n "⬝∨" m => Term.func Func.disj ![n,m]
    notation "⬝∼" n => Term.func Func.neg ![n]
    notation n "⬝⟹" m => Term.func Func.cond ![n,m]
    notation "⬝∀" n => Term.func Func.forall ![n]
    notation "⬝∃" n => Term.func Func.exists ![n]
    notation "⬝°"n  => Term.func Func.denote ![n]
    notation "Subs(" n "," x "," t ")" => Term.func Func.subs ![n, x, t]
    notation "Var(" x ")" => BoundedFormula.rel Rel.var ![x]
    notation "Const(" c ")" => BoundedFormula.rel Rel.const ![c]
    notation "Trm(" t ")" => BoundedFormula.rel Rel.term ![t]
    notation "ClosedTerm(" t")" => BoundedFormula.rel Rel.clterm ![t]
    notation "FormL(" t ")" => BoundedFormula.rel Rel.forml ![t]
    notation "SentenceL(" t ")" => BoundedFormula.rel Rel.sentencel ![t]
    notation "FormLT(" t ")" => BoundedFormula.rel Rel.formlt ![t]
    notation "SentenceLT(" t ")" => BoundedFormula.rel Rel.sentencelt ![t]
    notation "ℒ" => signature
    scoped[Languages] prefix:arg "#" => FirstOrder.Language.Term.var ∘ Sum.inl

    /-
    Some useful terms
    -/
    def null : Term signature α :=
      zero

    section Coding
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

      def Rel_dec {k} : (n : ℕ) → Option (signature.Relations k)
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
    notation "T(" n ")" => BoundedFormula.rel Rel.t ![n]
    notation "S(" n ")" => Term.func Func.succ ![n]
    notation "zero" => Term.func Func.zero ![]
    notation n "add" m => Term.func Func.add ![n,m]
    notation n "times" m => Term.func Func.mult ![n,m]
    notation n "⬝∧" m => Term.func Func.conj ![n,m]
    notation n "⬝∨" m => Term.func Func.disj ![n,m]
    notation "⬝∼" n => Term.func Func.neg ![n]
    notation n "⬝⟹" m => Term.func Func.cond ![n,m]
    notation "⬝∀" n => Term.func Func.forall ![n]
    notation "⬝∃" n => Term.func Func.exists ![n]
    notation "⬝°" n  => Term.func Func.denote ![n]
    notation "Subs(" n "," x "," t ")" => Term.func Func.subs ![n, x, t]
    notation "Var(" x ")" => BoundedFormula.rel L_T.Rel.var ![x]
    notation "Const(" c ")" => BoundedFormula.rel L_T.Rel.const ![c]
    notation "Trm(" t ")" => BoundedFormula.rel Rel.term ![t]
    notation "ClosedTerm(" t")" => BoundedFormula.rel L_T.Rel.clterm ![t]
    notation "FormL(" t ")" => BoundedFormula.rel L_T.Rel.forml ![t]
    notation "SentenceL(" t ")" => BoundedFormula.rel L_T.Rel.sentencel ![t]
    notation "FormLT(" t ")" => BoundedFormula.rel L_T.Rel.formlt ![t]
    notation "SentenceLT(" t ")" => BoundedFormula.rel L_T.Rel.sentencelt ![t]
    notation "ℒₜ" => signature

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
    def term_tonat_N : Term ℒ ℕ → ℕ :=
      fun t => Encodable.encodeList (Term.listEncode t)
    def term_tonat_Empty : Term ℒ (Empty ⊕ Fin 0) → ℕ :=
      fun t => Encodable.encodeList (Term.listEncode t)
    /-- Encodes BoundedFormulas as natural numbers -/
    def formula_N_tonat {n : ℕ} : BoundedFormula ℒ ℕ n → ℕ :=
      fun f => Encodable.encodeList (BoundedFormula.listEncode f)
    /-- Encodes BoundedFormulas as natural numbers -/
    def formula_Empty_tonat {n : ℕ} : BoundedFormula ℒ Empty 0 → ℕ :=
      fun f => Encodable.encodeList (BoundedFormula.listEncode f)


    def t₁ : Term ℒ ℕ :=
      Term.var 0
    def f₁ : BoundedFormula ℒ ℕ 0 :=
      #0 =' #1

    #eval term_tonat_N t₁ -- output : 1
    #eval formula_N_tonat f₁ -- output : 52

    -- notation "#" t => term_tonat_N t
    -- notation "#" φ => formula_tonat φ

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

  def inverse_homomorphism (f : ϕ.onFormula) ()

  example : ϕ.onFormula

  instance : Coe (Formula ℒ ℕ) (Formula ℒₜ ℕ) where
    coe := LHom.onFormula ϕ
  instance : Coe (Sentence ℒ) (Sentence ℒₜ) where
    coe := LHom.onSentence ϕ
  instance : Coe (Term ℒ (Empty ⊕ Fin 0)) (Term ℒₜ (Empty ⊕ Fin 0)) where
    coe := LHom.onTerm ϕ

end Languages

namespace SyntaxAxioms
open Languages
open L
open L_T
open BoundedFormula

variable {L : Language}

notation "⌜" φ "⌝" => L_T.numeral (formula_N_tonat φ)
notation "⌜" φ "⌝" => L_T.numeral (formula_Empty_tonat φ)
notation "⌜" t₁ "⌝" => L_T.numeral (term_tonat_N t₁)
notation "⌜" t₁ "⌝" => L_T.numeral (term_tonat_Empty t₁)
/- Some notation -/
notation f " ↑' " n " at "  m => liftAt n m f
notation f "↑" n => f ↑' n at 0
def g₁ : (Term L ℕ) → ℕ → (Term L ℕ) :=
  fun t : Term L ℕ => fun k : ℕ => ite (k = 0) t (Term.var (k - 1))
notation A "/[" t "]" => subst A (g₁ t)

def land (f₁ f₂: BoundedFormula L α n) :=
  ∼(f₁ ⟹ ∼f₂)
notation f₁ "∧'" f₂ => land f₁ f₂
def lor (f₁ f₂ : BoundedFormula L α n) :=
  ((∼f₁) ⟹ f₂)
notation f₁ "∨'" f₂ => lor f₁ f₂

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
def closed_term_repres (t₁ : Term ℒ (Empty ⊕ Fin 0)) : Sentence ℒₜ :=
  ClosedTerm( ⌜t₁⌝ )
def var_repres (φ : Formula ℒ ℕ) : Sentence ℒₜ :=
  Var( ⌜φ⌝ )
def const_repres (φ : Formula ℒ ℕ) : Sentence ℒₜ :=
  Const( ⌜φ⌝ )
def denote_repres (t₁ : Term ℒ (Empty ⊕ Fin 0)) : Sentence ℒₜ :=
  ClosedTerm(⌜t₁⌝) ⟹ ((⬝°(⌜t₁⌝)) =' t₁)

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

namespace PA
  open Languages
  open L
  open L_T
  open BoundedFormula

  def replace_bv_with_non_var_term {L} (f : BoundedFormula L α 1) (t : Term L α) : Formula L α :=
    subst f.toFormula (fun _ : α ⊕ Fin 1 => t)
  notation A "//[" t "]" => replace_bv_with_non_var_term A t
  def replace_bv_with_bv_term {α} {L} (f : BoundedFormula L α 1) (t : Term L (α ⊕ Fin 1)) : BoundedFormula L α 1 :=
    (relabel id (subst (f.toFormula) (fun _ : (α ⊕ Fin 1) => t)))
  notation A "///[" t "]" => replace_bv_with_bv_term A t

  /-- The induction function for ℒₚₐ -/
  def induction {α} (f : BoundedFormula ℒ α 1) : Formula ℒ α :=
    ∼ (f//[L.null] ⟹ (∼(∀'(f ⟹ f///[S(&0)])))) ⟹ ∀'f

  /-- Peano arithemtic -/
  inductive pre_peano_arithmetic {α}: Set (Formula ℒ α) where
    | first : pre_peano_arithmetic (∀' ∼(L.null =' S(&0)))
    | second :pre_peano_arithmetic (∀' ∀' ((S(&1) =' S(&0)) ⟹ (&1 =' &0)))
    | third : pre_peano_arithmetic (∀' ((&0 add L.null) =' &0))
    | fourth : pre_peano_arithmetic (∀' ∀' ((&1 add S(&0)) =' S(&1 add &0)))
    | fifth : pre_peano_arithmetic (∀' ((&0 times L.null) =' L.null))
    | sixth : pre_peano_arithmetic (∀' ∀' ((&1 times S(&0)) =' ((&1 times &0)) add &1))
    | induction (φ) : pre_peano_arithmetic (induction φ)

  def true_PA : Theory ℒ := pre_peano_arithmetic
  #check true_PA
  def some_PA : Set (Formula ℒ ℕ) := pre_peano_arithmetic


  notation "𝐏𝐀" => pre_peano_arithmetic

end PA

namespace PAT
open Languages
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
open PAT
open SyntaxTheory

inductive tarski_biconditionals : Theory ℒₜ where
  | pat_axioms {φ} : peano_arithmetic_t φ → tarski_biconditionals φ
  | syntax_axioms {φ} : syntax_theory φ → tarski_biconditionals φ
  | disquotation {φ : Sentence ℒ} : tarski_biconditionals (T(⌜φ⌝) ⇔ φ)

notation "𝐓𝐁" => tarski_biconditionals
end TB

namespace Calculus
  open Languages
  open BoundedFormula
  variable {L : Language}{n : ℕ}{α : Type}

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
  def m_add_eq_add_m {m} : BoundedFormula L ℕ (m + n) → BoundedFormula L ℕ (n + m) := by
    rw[add_comm]
    intro h
    exact h
  instance {m} : Coe (BoundedFormula L ℕ (m + n)) (BoundedFormula L ℕ (n + m)) where
    coe := m_add_eq_add_m

  /-- Proof that adding zero als does nothing in BoundedFormula types -/
  def add_zero_does_nothing : BoundedFormula L ℕ (0 + n) → BoundedFormula L ℕ n := by
    intro h
    rw[zero_add] at h
    exact h
  instance : Coe (BoundedFormula L ℕ (0 + n)) (BoundedFormula L ℕ n) where
    coe := add_zero_does_nothing
  instance : Coe (BoundedFormula L ℕ (n + 0)) (BoundedFormula L ℕ (0 + n)) where
    coe := m_add_eq_add_m

  def sent_term_to_formula_term : Term L (Empty ⊕ Fin n) → Term L (ℕ ⊕ Fin n)
      | .var m => match m with
        | .inl _ => .var (.inl Nat.zero)
        | .inr k => .var (.inr k)
      | .func f ts => .func f (fun i => sent_term_to_formula_term (ts i))
  instance : Coe (Term L (Empty ⊕ Fin n)) (Term L (ℕ ⊕ Fin n)) where
    coe := sent_term_to_formula_term
  def bf_empty_to_bf_N : ∀{n}, BoundedFormula L Empty n → BoundedFormula L ℕ n
      | _, .falsum => .falsum
      | _, .equal t₁ t₂ => .equal t₁ t₂
      | _, .rel R ts => .rel R (fun i => ts i)
      | _, .imp f₁ f₂ => .imp (bf_empty_to_bf_N f₁) (bf_empty_to_bf_N f₂)
      | _, .all f => .all (bf_empty_to_bf_N f)

  -- def is_free_variable : ∀{n}, Term L (ℕ ⊕ Fin n) → Prop
  --     | _, .var v => match v with
  --       | .inl _ => true
  --       | .inr _ => false
  --     | _, .func f ts => sorry

  -- def contains_free_variable {n} : BoundedFormula L ℕ n → Prop
  --     | .falsum => false
  --     | .equal t₁ t₂ => (is_free_variable t₁) ∨ (is_free_variable t₂)
  --     | .rel R ts => sorry
  --     | .imp f₁ f₂ => (contains_free_variable f₁) ∨ (contains_free_variable f₂)
  --     | .all f => contains_free_variable f

  -- def form_term_to_sent_term {n} (f : Term L (ℕ ⊕ Fin n)) : (is_free_variable t) → Term L (Empty ⊕ Fin n)
  --     | True => &0


  -- def form_to_sent {n} (f : BoundedFormula L ℕ n) : (contains_free_variable f) → BoundedFormula L Empty n
  --     | True => .falsum
  --     | False => match f with
  --       | .falsum => .falsum
  --       | .equal t₁ t₂ => .equal t₁ t₂
  --       | .rel R ts => sorry
  --       | .imp f₁ f₂ => sorry
  --       | .all f => sorry


  -- def f₁ : BoundedFormula ℒₜ Empty 0 :=
  --   ∀' (&0 =' &0)
  #check bf_empty_to_bf_N f₁
  #eval bf_empty_to_bf_N f₁

  -- def bf_N_to_bf_empty : ∀{n}, BoundedFormula L ℕ n → BoundedFormula L Empty n
  --     | _, .falsum => .falsum
  --     | _, .equal =>

  instance : Coe (Sentence L) (Formula L ℕ) where
    coe := bf_empty_to_bf_N
  def th_to_set_form : Theory L → (Set (Formula L ℕ)) :=
    fun Th : Theory L => bf_empty_to_bf_N '' Th
  instance : Coe (Theory L) (Set (Formula L ℕ)) where
    coe := th_to_set_form

  notation Δ"↑"  => (λf => (relabel shift_free_up f)) '' Δ
  notation A"↓" => relabel shift_one_down A

  /-- G3c sequent calculus -/
  inductive Derivation : (Theory L) → (Set (Formula L ℕ)) → (Set (Formula L ℕ)) → Type _ where
    | tax {Th Γ Δ} (f : Sentence L) (h₁ : f ∈ Th) (h₂ : (bf_empty_to_bf_N f) ∈ Δ) : Derivation Th Γ Δ
    | lax {Th Γ Δ} (h : (Γ ∩ Δ) ≠ ∅) : Derivation Th Γ Δ
    | left_conjunction (A B S) {Th Γ Δ} (h₁ : Derivation Th S Δ) (h₂ : A ∈ S) (h₃ : B ∈ S) (h₄ : Γ = (((S \ {A}) \ {B}) ∪ {A ∧' B})): Derivation Th Γ Δ
    | left_disjunction (A B S₁ S₂ S₃) {Th Γ Δ} (h₁ : Derivation Th S₁ Δ) (h₂ : S₁ = S₃ ∪ {A}) (h₃ : Derivation Th S₂ Δ) (h₄ : S₂ = S₃ ∪ {B}) (h₅ : Γ = S₃ ∪ {A ∨' B}) : Derivation Th Γ Δ
    | left_implication (A B S₁ S₂ S₃) {Th Γ Δ} (d₁ : Derivation Th S₁ S₂) (h₁ : S₂ = Δ ∪ {A}) (d₂ : Derivation Th S₃ Δ) (h₂ : S₃ = {B} ∪ S₁) (h₃ : Γ = S₁ ∪ {A ⟹ B}): Derivation Th Γ Δ
    | left_bot {Th Γ Δ} (h : ⊥ ∈ Γ) : Derivation Th Γ Δ
    | right_conjunction {Th Γ Δ} (A B S₁ S₂ S₃) (d₁ : Derivation Th Γ S₁) (h₁ : S₁ = S₃ ∪ {A}) (d₂ : Derivation Th Γ S₂) (h₂ : S₂ = S₃ ∪ {B}) (h₃ : Δ = S₃ ∪ {A ∧' B}) : Derivation Th Γ Δ
    | right_disjunction {Th Γ Δ} (A B S) (d₁ : Derivation Th Γ S) (h₁ : Δ = (S \ {A, B}) ∪ {A ∨' B}): Derivation Th Γ Δ
    | right_implication {Th Γ Δ} (A B S₁ S₂ S₃) (d₁ : Derivation Th S₁ S₂) (h₁ : S₁ = {A} ∪ Γ) (h₂ : S₂ = S₃ ∪ {B}) (h₃ : Δ = S₃ ∪ {A ⟹ B}): Derivation Th Γ Δ
    | left_forall {Th Γ Δ}  (A : Formula L ℕ) (B) (h₁ : B = A↓) (t S) (d : Derivation Th S Δ) (h₂ : (A/[t]) ∈ S ∧ (∀'B) ∈ S) (h₃ : Γ = S \ {(A/[t])}) : Derivation Th Γ Δ
    | left_exists {Th Γ Δ} (A B) (S₁ : Set (Formula L ℕ)) (p : B = A↓) (d₁ : Derivation Th ((S₁↑) ∪ {A}) (Δ↑)) (h₁ : Γ = S₁ ∪ {∃' B}) : Derivation Th Γ Δ
    | right_forall {Th Γ Δ} (A B S) (p : B = A↓) (d₁ : Derivation Th (Γ↑) ((S↑) ∪ {A})) (h₁ : Δ = S ∪ {∀'B}) : Derivation Th Γ Δ
    | right_exists {Th Γ Δ} (A : Formula L ℕ) (B t S) (p : B = A↓) (d₁ : Derivation Th Γ (S ∪ {∃'B, A/[t]})) (h₁ : Δ = S ∪ {∃'B}) : Derivation Th Γ Δ
    | cut {Th Γ Δ} (A S₁ S₂ S₃ S₄) (d₁ : Derivation Th S₁ (S₂ ∪ {A})) (d₂ : Derivation Th ({A} ∪ S₃) S₄) (h₁ : Γ = S₁ ∪ S₃) (h₂ : Δ = S₂ ∪ S₄) : Derivation Th Γ Δ


  def sequent_provable (Th : Theory L) (Γ Δ : Set (Formula L ℕ)) : Prop :=
    Nonempty (Derivation Th Γ Δ)
  notation Th " ⊢ " Γ Δ => sequent_provable Th Γ Δ
  def formula_provable (Th : Theory L) (f : Formula L ℕ) : Prop :=
    sequent_provable Th ∅ {f}
  notation Th " ⊢ " f => formula_provable Th f

end Calculus

namespace Conservativity
  open Languages
  open Calculus
  open TB
  open PA

  def not_contains_T {α} : ∀{n}, BoundedFormula ℒₜ α n → Prop
  | _, .rel L_T.Rel.t _ => false
  | _, .imp f₁ f₂ => not_contains_T f₁ ∧ not_contains_T f₂
  | _, .all f => not_contains_T f
  | _, _ => true

  -- lemma forall_indexing_sets : ∀f:BoundedFormula ℒₜ Empty n,∀g:BoundedFormula ℒₜ β n, not_contains_T f → not_contains_T g := by
  --   intro h₁
  --   intro h₂
  --   intro h₃
  --   induction h₁ with
  --   | falsum =>

  -- lemma if_sent_not_T_then_form_not_T : ∀(f: Sentence ℒₜ), (not_contains_T f) → (not_contains_T (bf_empty_to_bf_N f)) := by
  --   intro h₁
  --   intro h₂

  --   sorry

  -- inductive real_L {n} : BoundedFormula ℒₜ ℕ n → Prop
  -- | val (h : not_contains_T f) : real_L f

  def real_PA : Theory ℒₜ := {f | f ∈ 𝐓𝐁 ∧ (not_contains_T f)}

  instance : Coe (Set (Formula ℒ ℕ)) (Set (Formula ℒₜ ℕ)) where
    coe S := ϕ.onFormula '' S
  /- Need to define -/
  /- ALSO TODO define a set translation coercion for sets of formula in ℒ
  to sets of formulas in ℒₜ -/
  example : ∀{s : Sentence ℒₜ}, not_contains_T (bf_empty_to_bf_N s) → not_contains_T s := by
    intro h₁
    intro h₂
    cases h₁ with
    | falsum =>
      simp[bf_empty_to_bf_N] at h₂
      exact h₂
    | equal t₁ t₂ =>
      simp[bf_empty_to_bf_N] at h₂
      rfl
    | rel R ts =>
      simp[bf_empty_to_bf_N] at h₂
      cases R with
      | t =>
        simp[not_contains_T] at h₂
      | _ => rfl
    | imp f₁ f₂ =>
      simp[bf_empty_to_bf_N] at h₂

  -- def translation {Γ Δ : Set (Formula ℒₜ ℕ)} (ha : ∀f ∈ Γ, not_contains_T f) (hb : ∀f ∈ Δ, not_contains_T f) : Derivation 𝐓𝐁 Γ Δ  → Derivation real_PA Γ Δ
  --   | .tax (f : Sentence ℒₜ) (h₁ : f ∈ 𝐓𝐁) (h₂ : (bf_empty_to_bf_N f) ∈ Δ) => by
  --     cases f with
  --       | falsum =>
  --         apply Derivation.tax
  --         rw[real_PA]
  --         simp
  --         apply And.intro h₁
  --         rfl
  --         exact h₂
  --       | equal t₁ t₂ =>
  --         apply Derivation.tax
  --         rw[real_PA]
  --         simp
  --         apply And.intro h₁
  --         rfl
  --         exact h₂
  --       | rel R ts =>
  --         apply Derivation.tax
  --         rw[real_PA]
  --         simp
  --         apply And.intro h₁
  --         rfl





  --     sorry
  --     -- have step1 : f ∈ real_PA := by





  --     -- have step1 : ∃f : Sentence ℒₜ, f ∈ real_PA ∧ (bf_empty_to_bf_N f) ∈ Δ := by
  --     --   rcases h with ⟨f, a₁, a₂⟩
  --     --   have step2 : not_contains_T f := by
  --     --     apply hb at a₂
  --     --     exact a₂
  --     --   have step3 : f ∈ real_PA := by
  --     --     rw[real_PA]
  --     --     simp
  --     --     apply And.intro a₁ step2
  --     --   have step4 : f ∈ real_PA ∧ f ∈ Δ := by
  --     --     apply And.intro step3 a₂
  --     --   apply Exists.intro f step4

  --     apply Derivation.tax step1
  --   | .lax (h : (Γ ∩ Δ) ≠ ∅) => Derivation.lax h
  --   | .left_conjunction A B S (h₁ : Derivation 𝐓𝐁 S Δ) (h₂ : A ∈ S) (h₃ : B ∈ S) (h₄ : Γ = (((S \ {A}) \ {B}) ∪ {A ∧' B})) => sorry
  --   | .left_disjunction A B S₁ S₂ S₃ (h₁ : Derivation 𝐓𝐁 S₁ Δ) (h₂ : S₁ = S₃ ∪ {A}) (h₃ : Derivation 𝐓𝐁 S₂ Δ) (h₄ : S₂ = S₃ ∪ {B}) (h₅ : Γ = S₃ ∪ {A ∨' B}) => sorry
  --   | .left_implication A B S₁ S₂ S₃ (d₁ : Derivation 𝐓𝐁 S₁ S₂) (h₁ : S₂ = Δ ∪ {A}) (d₂ : Derivation 𝐓𝐁 S₃ Δ) (h₂ : S₃ = {B} ∪ S₁) (h₃ : Γ = S₁ ∪ {A ⟹ B}) => sorry
  --   | .left_bot (h : ⊥ ∈ Γ) => Derivation.left_bot h
  --   | .right_conjunction A B S₁ S₂ S₃ (d₁ : Derivation 𝐓𝐁 Γ S₁) (h₁ : S₁ = S₃ ∪ {A}) (d₂ : Derivation 𝐓𝐁 Γ S₂) (h₂ : S₂ = S₃ ∪ {B}) (h₃ : Δ = S₃ ∪ {A ∧' B}) => sorry
  --   | .right_disjunction A B S (d₁ : Derivation 𝐓𝐁 Γ S) (h₁ : Δ = (S \ {A, B}) ∪ {A ∨' B}) => sorry
  --   | .right_implication A B S₁ S₂ S₃ (d₁ : Derivation 𝐓𝐁 S₁ S₂) (h₁ : S₁ = {A} ∪ Γ) (h₂ : S₂ = S₃ ∪ {B}) (h₃ : Δ = S₃ ∪ {A ⟹ B}) => sorry
  --   | .right_bot S (d : Derivation 𝐓𝐁 Γ S) (h₁ : ⊥ ∈ S) (h₂ : Δ = S \ ⊥) => sorry
  --   | .left_forall (A : Formula ℒₜ ℕ) (B) (h₁ : B = A↓) t S (d : Derivation 𝐓𝐁 S Δ) (h₂ : (A/[t]) ∈ S ∧ (∀'B) ∈ S) (h₃ : Γ = S \ {(A/[t])}) => sorry
  --   | .left_exists A B (S₁ : Set (Formula ℒₜ ℕ)) (p : B = A↓) (d₁ : Derivation 𝐓𝐁 ((S₁↑) ∪ {A}) (Δ↑)) (h₁ : Γ = S₁ ∪ {∃' B}) => sorry
  --   | .right_forall A B S (p : B = A↓) (d₁ : Derivation 𝐓𝐁 (Γ↑) ((S↑) ∪ {A})) (h₁ : Δ = S ∪ {∀'B}) => sorry
  --   | .right_exists (A : Formula ℒₜ ℕ) B t S (p : B = A↓) (d₁ : Derivation 𝐓𝐁 Γ (S ∪ {∃'B, A/[t]})) (h₁ : Δ = S ∪ {∃'B}) => sorry

  theorem conservativity_of_tb : ∀f : Formula ℒ ℕ, (𝐓𝐁 ⊢ f) → (pre_peano_arithmetic ⊢ f) := by
  intro f
  intro h
  rw[formula_provable,sequent_provable]
  cases f with
  | falsum => sorry
  | equal t₁ t₂ => sorry
  | rel R ts => sorry
  | imp f₁ f₂ => sorry
  | all f => sorry

end Conservativity

namespace Hidden
  inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

def head {α} : {n : Nat} → Vector α (n+1) → α
  | n, Vector.cons a as => a

def tail {α} : {n : Nat} → Vector α (n+1) → Vector α n
  | n, Vector.cons a as => as

  theorem eta {α} : ∀ {n : Nat} (v : Vector α (n+1)), Vector.cons (head v) (tail v) = v
  | n, Vector.cons a as => rfl

-- Define the predicate P for the subset
def P (a : Nat) : Prop := a - 2 = 0

-- Define the subset B using a subtype
def B : Type := { x : Nat // P x }
#check B
def a : B := ⟨2, rfl⟩
#check a
#eval a

example : ∀i : B, i ∈ Set.univ := by

-- Define an element of B
def b : B := ⟨4, rfl⟩

-- Define an element of A that is not in B
def a : A := 3

-- Define a function that checks if an element of A is in B
def is_in_B (x : A) : Prop := P x

-- Example usage
#eval is_in_B 4 -- true
#eval is_in_B 3 -- false

end Hidden
