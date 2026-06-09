import Chapter01.proposition_1_9_1
import Chapter01.cut_space_incidence_image

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.9.6.
The kernel of the incidence matrix is the cycle space, and the image of
its transpose is the cut space.
-/
theorem proposition_1_9_6 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet] :
  (∀ F : EdgeSpace G,
    ((∀ v : V, (∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then F e else 0)) = 0) ↔
      F ∈ cycle_space G)) ∧
    (∀ D : EdgeSpace G,
      D ∈ cut_space G ↔
        ∃ U : VertexSpace V,
          ∀ e : G.edgeSet,
            D e = ∑ v : V, (if v ∈ (e : Sym2 V) then U v else 0)) := by
  constructor
  · intro F
    constructor
    · intro hF
      exact (proposition_1_9_1 G F).2.mpr fun v =>
        (even_incidence_iff_sum_zero F v).mpr (hF v)
    · intro hF v
      exact cycle_space_incidence_sum_zero hF v
  · exact cut_space_incidence_image G

end Chapter01
end Diestel
