import Lake
open Lake DSL

package TypeTheoryTalks {
  -- add configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require leanslides from git "https://github.com/0art0/lean-slides"@"master"

@[default_target]
lean_lib TypeTheoryTalks {
  -- add configuration options here
}

@[default_target]
lean_lib LeanIntroTalks {
  precompileModules := true
}

@[default_target]
lean_lib Demos {
  -- add configuration options here
}

@[default_target]
lean_lib LambdaCalculus {
}
