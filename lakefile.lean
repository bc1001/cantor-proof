import Lake
open Lake DSL

package "cantor_conjecture" where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib" @ git "v4.35.0-rc4"

@[default_target]
lean_lib «StrictFormalConjecture1» where
  srcDir := "."

-- 同时注册试卷模块
lean_lib «Conjecture1_Comparator» where
  srcDir := "."
