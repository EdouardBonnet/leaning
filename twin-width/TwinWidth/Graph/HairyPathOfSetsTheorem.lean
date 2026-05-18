import TwinWidth.Graph.HairyPathOfSetsContract

/-!
# Finding hairy path-of-sets systems

This module exposes the hairy Path-of-Sets System existence theorem outside
the contract namespace.  The current proof is the corresponding contract axiom.
-/

namespace TwinWidth
namespace SimpleGraph
namespace HairyPathOfSetsTheorem

/-- Sufficiently large treewidth forces a maximum-degree-three subgraph
containing a hairy Path-of-Sets System. -/
theorem exists_subgraph_hairy_pathOfSets_of_treewidth :
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
                          Nonempty (HairyPathOfSetsSystem H ell w) := by
  exact HairyPathOfSetsContract.exists_subgraph_hairy_pathOfSets_of_treewidth

end HairyPathOfSetsTheorem
end SimpleGraph
end TwinWidth
