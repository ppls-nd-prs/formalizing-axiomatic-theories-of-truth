namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

inductive Nat_from (n : Nat) where
  | begin : Nat_from n
  | succ : (Nat_from n) → (Nat_from n)
