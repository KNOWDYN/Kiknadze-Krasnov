import Lake
open Lake DSL

package KiknadzeKrasnov where
  version := v!"1.0.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a"

@[default_target]
lean_lib KiknadzeKrasnov where
