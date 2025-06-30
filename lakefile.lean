import Lake
open Lake DSL

/-! # Lake configuration for ArkLib

Many of these configs are taken from mathlib
 -/

/-! ## Dependencies on upstream projects -/

require VCVio from git "https://github.com/dtumad/VCV-io.git" @ "v4.21.0-rc3"

-- don't need to specify this, since VCV already imports mathlib
-- require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.21.0-rc3"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git" @ "lean4.18.0"

-- Dependent rewrite tactic
require seq from git "https://github.com/Vtec234/lean4-seq.git"

-- meta if get_config? env = some "dev" then

/-- These options are used
* as `leanOptions`, prefixed by `` `weak``, so that `lake build` uses them;
* as `moreServerArgs`, to set their default value in arklib
  (as well as `Archive`, `Counterexamples` and `test`).
-/
abbrev arklibOnlyLinters : Array LeanOption := #[
  -- We use the same set of standard Mathlib linter options
  ⟨`linter.mathlibStandardSet, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
]

/-- These options are passed as `leanOptions` to building arklib, as well as the
`Archive` and `Counterexamples`. (`tests` omits the first two options.) -/
abbrev arklibLeanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ] ++ -- options that are used in `lake build`
    arklibOnlyLinters.map fun s ↦ { s with name := `weak ++ s.name }

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-DAutoImplicit=false"
]

package «Arklib» {
  -- add any package configuration options here
  leanOptions := arklibLeanOptions
  -- ArkLib also enforces these linter options, which are not active by default.
  moreServerOptions := arklibOnlyLinters
}

@[default_target]
lean_lib «ArkLib» {
  -- add any library configuration options here
}
