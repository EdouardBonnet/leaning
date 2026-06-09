import Chapter02.theorem_2_2_1
import Chapter02.petersen_counting

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Corollary 2.2.2 (Petersen).
Natural-language statement:
Every finite bridgeless cubic graph has a 1-factor.
-/
theorem corollary_2_2_2 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
  IsCubic G →
    IsBridgeless G →
      ∃ M : G.Subgraph, M.IsPerfectMatching := by
  intro hCubic hBridgeless
  exact (theorem_2_2_1 G).2 fun S =>
    PetersenCounting.not_isTutteViolator_of_boundary_odd_and_ne_one G S hCubic
      (fun C => PetersenCounting.boundary_natCard_odd_of_cubic G S hCubic C)
      (fun C => PetersenCounting.boundary_natCard_ne_one_of_bridgeless G S hBridgeless C)

end Chapter02
end Diestel
