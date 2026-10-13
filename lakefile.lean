import Lake
open Lake DSL

package «lean-sudakov» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

@[default_target]
lean_lib LeanSudakov where
  globs := #[.andSubmodules `LeanSudakov]
