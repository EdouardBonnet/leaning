import Chapter01.definitions_ch1

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.9.6.
Natural-language statement:
The kernel of the incidence matrix is the cycle space, and the image of
its transpose is the cut space.
-/
axiom proposition_1_9_6 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet] :
  (∀ F : EdgeSpace G,
    ((∀ v : V, (∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then F e else 0)) = 0) ↔
      F ∈ cycle_space G)) ∧
    (∀ D : EdgeSpace G,
      D ∈ cut_space G ↔
        ∃ U : VertexSpace V,
          ∀ e : G.edgeSet,
            D e = ∑ v : V, (if v ∈ (e : Sym2 V) then U v else 0))

end Chapter01
end Diestel
