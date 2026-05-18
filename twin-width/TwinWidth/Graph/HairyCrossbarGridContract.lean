import TwinWidth.Graph.HairyPathOfSets
import TwinWidth.Graph.Crossbar
import TwinWidth.Graph.CrossbarPower
import TwinWidth.Graph.Degree
import TwinWidth.Graph.HairyCrossbarGridIndex
import TwinWidth.Graph.Minor
import Mathlib.Data.Nat.Log

/-!
# Contract for the large-case crossbar-grid assembly

This file states only the large-parameter part of the Section 3 assembly
theorem.  The proof-facing module handles the complementary small case
formally by taking the `1 x 1` grid minor from the underlying strong
path-of-sets system.
-/

namespace TwinWidth
namespace SimpleGraph
namespace HairyCrossbarGridContract

/-- Chuzhoy--Tan Theorem 3.2, stated as a large-case contract.

The paper obtains order `Ω(g / log^{1.5} g)`.  We record the weaker but simpler
integer consequence `g ≤ c * g' * (log_2 g)^2`, which is sufficient for a
polynomial excluded-grid bound.  The additional hypothesis
`c * (log_2 g)^2 < g` removes the small case handled in the proof-facing
wrapper.
-/
axiom gridMinor_of_hairy_pathOfSets_and_crossbars_large :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                c * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    c * (Nat.log 2 g) ^ 2 < g →
                      (∀ i : Fin ell, HairyCrossbarGrid.OneBasedOdd i →
                        Nonempty (Crossbar (Hsys.hairLocalGraph i)
                          (Hsys.base.left i) (Hsys.base.right i)
                          (Hsys.y i) (g ^ 2))) →
                        ∃ g' : ℕ,
                          g ≤ c * g' * (Nat.log 2 g) ^ 2 ∧
                            ContainsGridMinor G g'

end HairyCrossbarGridContract
end SimpleGraph
end TwinWidth
