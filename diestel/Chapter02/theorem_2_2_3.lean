import Chapter02.gallai_edmonds_existence_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Theorem 2.2.3 (Gallai-Edmonds).
Natural-language statement:
Every finite graph has a set `S` matchable to the components of `G - S`
such that every component of `G - S` is factor-critical; for every such
`S`, the graph has a 1-factor iff `|S|` equals the number of components of
`G - S`.
-/
theorem theorem_2_2_3 {V : Type u} (G : SimpleGraph V) [Finite V] :
  (∃ S : Set V, GallaiEdmondsSet G S) ∧
    ∀ S : Set V, GallaiEdmondsSet G S →
      ((∃ M : G.Subgraph, M.IsPerfectMatching) ↔
        S.ncard = Nat.card (DeletedComponent G S)) := by
  refine ⟨GallaiEdmondsExistence.exists_gallaiEdmondsSet G, ?_⟩
  intro S hS
  exact GallaiEdmondsAux.isPerfectMatching_iff_ncard_eq_of_gallaiEdmondsSet hS

end Chapter02
end Diestel
