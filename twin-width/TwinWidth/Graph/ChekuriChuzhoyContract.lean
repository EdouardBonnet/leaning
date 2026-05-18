import TwinWidth.Graph.ChekuriChuzhoyStitchedRows
import TwinWidth.Graph.GridMinor

/-!
# Contract for the Chekuri--Chuzhoy Corollary 3.2 dichotomy

This file states the remaining non-formalized input from Chekuri--Chuzhoy:
Corollary 3.2 applied with `h₁ = h₂ = g`, for the strong path-of-sets systems
used downstream.  The outcome is either a direct `g x g` grid minor or stitched
rows of the form used in Appendix C.1.  The implementation file proves that the
stitched-row branch also contains a `g x g` grid minor.
-/

namespace TwinWidth
namespace SimpleGraph
namespace ChekuriChuzhoyContract

/-- Chekuri--Chuzhoy Corollary 3.2, specialized to the parameters used in
Corollary 3.3. -/
axiom gridMinor_or_stitchedRows_of_pathOfSets :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {g : ℕ},
        2 ≤ g →
          (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) (16 * g ^ 2 + 10 * g)) →
            ContainsGridMinor G g ∨
              Nonempty
                (ChekuriChuzhoy.StitchedRows G g (16 * g ^ 2 + 10 * g)
                  P.toPathOfSetsSystem)

end ChekuriChuzhoyContract
end SimpleGraph
end TwinWidth
