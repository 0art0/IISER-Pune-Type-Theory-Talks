import Lake
open Lake DSL

package TypeTheoryTalks {
  -- add configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib TypeTheoryTalks {
  -- add configuration options here
}
