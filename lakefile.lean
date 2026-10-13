import Lake
open Lake DSL

package "cantor_conjecture" where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib" @ git "v4.35.0-rc4"

@[default_target]
lean_lib «StrictFormalConjecture1» where
  srcDir := "."

@[default_target]
lean_lib «Conjecture1_Comparator» where
  srcDir := "."
