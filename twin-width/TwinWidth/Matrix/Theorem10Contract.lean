import TwinWidth.Matrix.Theorem10Defs

/-!
# Contract statements for matrix Theorem 10

This file is intentionally a contract layer: it states the final matrix-level
Theorem 10 interface.  Contract axioms must not be imported into completed
proof modules as if they were proofs; this axiom should be replaced by a
corresponding theorem in the full proof file once both directions are proved.
-/

namespace TwinWidth
namespace Matrix
namespace Theorem10Contract

/-- Matrix Theorem 10: a `d`-twin-ordered matrix has mixed number at most
`2 * d + 2`, and every matrix has matrix twin-width bounded by the explicit
Theorem 10 bound at its matrix mixed number. -/
axiom theorem10_matrix_mixed_number_and_matrix_twin_width_bound_each_other :
    (∀ {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
      MatrixTwinOrderedAtMost M d → matrixMixedNumber M ≤ 2 * d + 2) ∧
    (∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
      MatrixTwinWidthAtMost M (theorem10MatrixTwinWidthBound (matrixMixedNumber M)))

end Theorem10Contract
end Matrix
end TwinWidth
