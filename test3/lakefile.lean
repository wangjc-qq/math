import Lake
open Lake DSL

-- 配置本地 Mathlib4 路径
-- require mathlib from "mathlib-4.20.0"  -- 相对路径
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.20.0"

package test3 where
  -- 包配置

@[default_target]
lean_lib test3 where
  -- 库配置
