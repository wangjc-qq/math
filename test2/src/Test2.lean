-- This module serves as the root of the `Test2` library.
-- Import modules here that should be built as part of the library.
import Test2.Basic

theorem Euclid : ∀ n: Nat, ∃ p : Nat, p > n ∧ Prime p :=
 sorry

theorem Nzero_add : ∀ n, Nadd Z n = n

theorem NSadd : ∀ m n, Nadd (S m) n = S (Nadd mn)

theorem Nadd_comm: ∀ m n, Nadd m n = Nadd n m
