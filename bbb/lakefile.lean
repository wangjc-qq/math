import Lake

open Lake DSL

/-!
-- Mathlib dependencies on upstream projects
-- 添加 Mathlib4 依赖
  -- require mathlib4 from git "https://github.com/leanprover-community/mathlib4" @ "master"
-/
  require mathlib from  ".lake/packages/mathlib"
  require proofwidgets from  ".lake/packages/proofwidgets"
  require aesop from  ".lake/packages/aesop"
  require batteries from  ".lake/packages/batteries"
  require importGraph from  ".lake/packages/importGraph"
  require LeanSearchClient from  ".lake/packages/LeanSearchClient"
  require plausible from  ".lake/packages/plausible"
  require Qq from  ".lake/packages/Qq"
  require Cli from  ".lake/packages/Cli"


/-!
## Options for building mathlib
-/

package bbb where

/-!
## Mathlib libraries
-/
lean_lib Bbb where
  -- name := "Basic"
/-!
## Executables provided by Mathlib
-/

  -- 定义可执行文件（可选）
  @[default_target]
  lean_exe bbb where
    root := `Main
