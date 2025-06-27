-- -- import IO
-- import SearchPath

-- /--
-- 打印 Lean 的模块搜索路径
-- -/
-- def main : IO Unit := do
--   IO.println (← SearchPath.getModuleDirs)



import Lean

/--
打印 Lean 的模块搜索路径
-/

-- def main : IO Unit := do
--   IO.println s!"searchPath: {← Lean.getSearchPath}"
def main : IO Unit := do
  let sp ← IO.getEnv "LEAN_PATH"
  IO.println s!"LEAN_PATH: {sp}"
