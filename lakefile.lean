import Lake
open Lake DSL

package «lean-move» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.7.0-rc2"

require ssreflect from git "https://github.com/verse-lab/lean-ssr" @ "master"

@[default_target]
lean_lib «LeanMove» where
  -- add any library configuration options here
