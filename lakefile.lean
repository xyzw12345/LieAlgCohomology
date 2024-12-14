import Lake
open Lake DSL

package "LieAlgCohomology" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

-- require "leanprover-community" / "mathlib"
require "Blackfeather007" / "Filtered_Ring" from git "https://github.com/Blackfeather007/Filtered_Ring"

@[default_target]
lean_lib «LieAlgCohomology» where
  -- add any library configuration options here
