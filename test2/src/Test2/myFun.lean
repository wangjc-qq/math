
inductive N where
  | Z: N
  | S:N->N

open N

def Nadd (m n : N) : N :=
  match n with
  | Z => m
  | S n' => S (Nadd m n')


theorem Nzero_add : ∀ n, Nadd Z n = n := by
  intro n
  induction n
  case Z => rfl
  case S n' IH =>
    unfold Nadd
    rewrite [IH]
    rfl

def Divides (m n : Nat) : Prop :=
  ∃ k : Nat, n = m * k


def Prime (n: Nat) : Prop :=
  ∀ k: Nat, 1 < k → k < n → ¬Divides k n
