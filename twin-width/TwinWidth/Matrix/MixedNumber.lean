import TwinWidth.Matrix.MixedMinor

/-!
# Mixed number of a Boolean matrix

The mixed number is the largest `k ≤ min n m` for which the matrix has a
`k`-mixed minor.  The `k = 0` convention from `HasMixedMinor` ensures this
maximum is always defined.
-/

namespace TwinWidth
namespace Matrix

/-- The mixed number of a Boolean matrix: the largest order of a mixed minor,
searched up to the smaller matrix dimension. -/
noncomputable def matrixMixedNumber {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool) : ℕ :=
  by
    classical
    exact Nat.findGreatest (HasMixedMinor M) (min n m)

theorem matrixMixedNumber_le_min_card {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool) :
    matrixMixedNumber M ≤ min n m :=
  by
    classical
    exact Nat.findGreatest_le (P := HasMixedMinor M) (min n m)

theorem hasMixedMinor_matrixMixedNumber {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool) :
    HasMixedMinor M (matrixMixedNumber M) := by
  classical
  exact Nat.findGreatest_spec (P := HasMixedMinor M) (m := 0) (n := min n m)
    (Nat.zero_le _) (hasMixedMinor_zero M)

end Matrix
end TwinWidth
