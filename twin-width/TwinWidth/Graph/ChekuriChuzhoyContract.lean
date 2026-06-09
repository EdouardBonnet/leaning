import TwinWidth.Graph.ChekuriChuzhoyCorollary33Contract
import TwinWidth.Graph.ChekuriChuzhoyStitchedRows

/-!
# Downstream Chekuri--Chuzhoy contract adapter

The named paper contracts are split across:

* `ChekuriChuzhoyTheorem215Contract`
* `ChekuriChuzhoyTheoremB1Contract`
* `ChekuriChuzhoyTheorem31Contract`
* `ChekuriChuzhoyCorollary32Contract`
* `ChekuriChuzhoyCorollary33Contract`

This file keeps the narrow specialized interface consumed by the existing
Appendix C.1 formalization in `ChekuriChuzhoy.lean`: Corollary 3.2 at the exact
parameters used in Corollary 3.3, returning either a direct grid minor or the
stitched-row object already handled by the full proof file.
-/

namespace TwinWidth
namespace SimpleGraph
namespace ChekuriChuzhoyContract

universe u

/-- Chekuri--Chuzhoy Corollary 3.2, specialized to the parameters used in
Corollary 3.3 and to the stitched-row data consumed by the Appendix C.1
assembly proof. -/
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
