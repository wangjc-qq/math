-- This module serves as the root of the `MyDemo1` library.
-- Import modules here that should be built as part of the library.
import MyDemo1.Basic

import Mathlib.Tactic.Abel

import Mathlib.Data.Nat.Basic  -- 导入 mathlib4 的自然数基础库

-- 测试定理：自然数加法交换律（mathlib 已证明，这里直接用）
open Nat  -- 打开 Nat 命名空间以访问 add_comm

example : ∀ (a b : Nat), a + b = b + a := by
  exact add_comm  -- 调用 mathlib 中的定理

#eval "Hello World! "
