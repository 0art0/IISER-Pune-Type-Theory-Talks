import Lake
open Lake DSL

package TypeTheoryTalks {
  -- add configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require proofwidgets from git "https://github.com/EdAyers/ProofWidgets4"@"v0.0.7"

@[default_target]
lean_lib TypeTheoryTalks {
  -- add configuration options here
}

@[default_target]
lean_lib Demos {
  -- add configuration options here
}

@[default_target]
lean_lib LambdaCalculus {
}
