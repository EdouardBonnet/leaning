import TwinWidth.Graph.HairyPathOfSets
import TwinWidth.Graph.Degree
import TwinWidth.Graph.TreewidthContract
import Mathlib.Data.Nat.Log

/-!
# Contract for finding hairy path-of-sets systems

This file states Chuzhoy--Tan Theorem 2.3: sufficiently large treewidth forces
a maximum-degree-three subgraph containing a hairy Path-of-Sets System.
-/

namespace TwinWidth
namespace SimpleGraph
namespace HairyPathOfSetsContract

/-- Chuzhoy--Tan Theorem 2.3, stated as a contract.

The paper's condition `k / log^c' k > c w ell^48` is encoded without division as
`c * w * ell^48 * (log_2 k)^c' < k`.
-/
axiom exists_subgraph_hairy_pathOfSets_of_treewidth :
    ∃ c c' : ℕ, 0 < c ∧ 0 < c' ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k : ℕ},
          1 < ell →
            1 < w →
              1 < k →
                k ≤ treewidth G →
                  c * w * ell ^ 48 * (Nat.log 2 k) ^ c' < k →
                    ∃ H : _root_.SimpleGraph V,
                      H ≤ G ∧
                        MaxDegreeAtMost H 3 ∧
                          Nonempty (HairyPathOfSetsSystem H ell w)

end HairyPathOfSetsContract
end SimpleGraph
end TwinWidth
