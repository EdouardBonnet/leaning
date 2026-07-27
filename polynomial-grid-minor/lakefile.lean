import Lake

open Lake DSL

package polynomialGridMinor where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "ff96409d623285fbfe777cf47c50574f05f63a3d"

@[default_target]
lean_lib PolynomialGridMinor where
  roots := #[`PolynomialGridMinor, `AxiomAudit, `«statements-and-proofs»]
  globs := #[
    .one `PolynomialGridMinor,
    .one `AxiomAudit,
    .submodules `«statements-and-proofs»
  ]
