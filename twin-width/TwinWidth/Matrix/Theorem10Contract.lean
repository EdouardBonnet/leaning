import TwinWidth.Matrix.Theorem10

/-!
# Contract statement for matrix Theorem 10

This file states the final matrix-level Theorem 10 interface.
-/

namespace TwinWidth
namespace Matrix
namespace Theorem10Contract

variable {α : Type*}

/-- Matrix Theorem 10 over a nonempty finite alphabet: twin-ordered matrices
have linearly bounded mixed number, and every matrix has matrix twin-width
bounded by the explicit Theorem 10 function of the alphabet size and the matrix
mixed number. -/
theorem theorem10_matrix_mixed_number_and_matrix_twin_width_bound_each_other
    [Fintype α] [DecidableEq α] [Inhabited α] :
    (∀ {n m d : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
      MatrixTwinOrderedAtMost M d → matrixMixedNumber M ≤ 2 * d + 2) ∧
    (∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α),
      MatrixTwinWidthAtMost M
        (theorem10AlphabetMatrixTwinWidthBound (Fintype.card α) (matrixMixedNumber M))) := by
  exact TwinWidth.Matrix.theorem10_matrix_mixed_number_and_matrix_twin_width_bound_each_other

end Theorem10Contract
end Matrix
end TwinWidth
