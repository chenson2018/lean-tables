import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0-rc2"

package table {
  -- add configuration options here
}

@[default_target]
lean_lib Table {
  roots := #[`Table]
  globs := #[Glob.submodules `Table]
}

@[test_driver]
lean_lib Tests {
  globs := #[Glob.submodules `Tests]
}
