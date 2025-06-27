import Bbb

import Mathlib.Data.Nat.Basic  -- 导入 Mathlib4 的自然数库

#check Nat.add_comm  -- 检查加法交换律定理

example : ∀ a b : Nat, a + b = b + a :=
  Nat.add_comm  -- 使用 Mathlib4 中的定理


def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
