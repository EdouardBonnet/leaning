import «statements-and-proofs».ChekuriChuzhoy

/-!
# Contract for the path-of-sets to grid-minor conversion

This is the structural Theorem 2.1-style interface used downstream: a strong
path-of-sets system whose length and width dominate the Chekuri--Chuzhoy
Corollary 3.3 thresholds contains the requested grid minor.
-/

namespace SimpleGraph
namespace PathOfSetsGridContract

universe u

/-- Path-of-sets-to-grid conversion, structural form.

If a strong path-of-sets system has length at least `2 * g * (g - 1)` and width
at least `16 * g^2 + 10 * g`, then the host graph contains a `g x g` grid
minor. -/
theorem containsGridMinor_of_strongPathOfSets_ge :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {ell w g : ℕ},
        2 ≤ g →
          2 * g * (g - 1) ≤ ell →
            16 * g ^ 2 + 10 * g ≤ w →
              StrongPathOfSetsSystem G ell w →
                ContainsGridMinor G g := by
  intro V _ _ G ell w g hg hlength hwidth Hsys
  exact _root_.SimpleGraph.ChekuriChuzhoy.containsGridMinor_of_strongPathOfSets_ge
    G hg hlength hwidth Hsys

end PathOfSetsGridContract
end SimpleGraph
