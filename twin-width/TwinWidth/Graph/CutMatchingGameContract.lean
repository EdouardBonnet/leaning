import TwinWidth.Graph.HairyCrossbarGrid

/-!
# Contract for the cut-matching game

This file states the Section 4 upper-bound theorem from Khandekar--Khot--
Orecchia--Vishnoi, *On a Cut-Matching Game for the Sparsest Cut Problem*, in
the form used by the Chuzhoy--Tan crossbar-grid assembly.

The paper proves that there is a cut-player strategy using `O(log n)` rounds
which, against every matching player, makes the union of the matching rounds an
edge expander.  In the repository's large crossbar-grid construction the
matching player's response is the transported matching supplied by the local
crossbars.  The statement below therefore exposes the concrete output needed
downstream: a finite sequence of full bisections of the grid-coordinate set
whose transported matching union is a half-edge-expander.
-/

namespace TwinWidth
namespace SimpleGraph
namespace HairyCrossbarGrid
namespace CutMatchingGameContract

universe u

/-- Section 4 of the cut-matching-game paper, specialized to the transported
matching rounds used in the crossbar-grid construction.

There is a universal round constant `cRound` such that, for every large
crossbar-grid instance, the cut player can choose
`cRound * log_2 g` full bisections `U_r, W_r` of the `g × g` coordinate set.
For the transported matching round forced by the local crossbars across each
chosen bisection, the union of all rounds is a half-edge-expander.

The hypotheses `2 ≤ g`, `IsPowerOfTwo g`, and `g^2 ≤ w` are the conventions
under which the local crossbar machinery supplies a perfect transported
matching across every full bisection of `GridVertex g`.
-/
axiom exists_bisection_strategy_transported_matchings_half_expander :
    ∃ cRound : ℕ, 0 < cRound ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                (hrounds : (2 * cRound) * Nat.log 2 g ≤ ell) →
                  g ^ 2 ≤ w →
                    (hcrossbars :
                      ∀ i : Fin ell, OneBasedOdd i →
                        Nonempty (Crossbar (Hsys.hairLocalGraph i)
                          (Hsys.base.left i) (Hsys.base.right i)
                          (Hsys.y i) (g ^ 2))) →
                      ∃ U W :
                          Fin (largeCaseRoundBound cRound g) →
                            Finset (GridVertex g),
                        ∃ hdisj : ∀ r : Fin (largeCaseRoundBound cRound g),
                            Disjoint (U r) (W r),
                          ∃ hcard :
                              ∀ r : Fin (largeCaseRoundBound cRound g),
                                (U r).card = (W r).card,
                            (∀ r : Fin (largeCaseRoundBound cRound g),
                                U r ∪ W r = Finset.univ) ∧
                              (SelectedOddLocalCrossbarGridTransportedRoundFamily.ofFinCuts
                                Hsys hcrossbars
                                  (two_mul_largeCaseRoundBound_le_of_two_mul_roundConstant
                                    hrounds)
                                  (le_rfl :
                                    largeCaseRoundBound cRound g ≤
                                      largeCaseRoundBound cRound g)
                                  U W hdisj hcard).IsHalfEdgeExpander

end CutMatchingGameContract
end HairyCrossbarGrid
end SimpleGraph
end TwinWidth
