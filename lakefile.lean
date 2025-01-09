import Lake
open Lake DSL

package «formalizing-axiomatic-theories-of-truth» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d1fa45bcb0bb5ae74fc38931a796fba555e94e41"

@[default_target]
lean_lib «FormalizingAxiomaticTheoriesOfTruth» where
  -- add any library configuration options here

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

require foundation from git "https://github.com/FormalizedFormalLogic/Foundation.git" @ "d5a5b566c4bbc8d91a509979ae5091e750e67059"
