import Chapter02.gallai_milgram_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Theorem 2.5.1 (Gallai-Milgram).
Every finite directed graph has a path cover with one representative
vertex from each path, and the representatives form an independent set.
-/
theorem theorem_2_5_1 {V : Type u} [Fintype V] [DecidableEq V]
    (D : DirectedGraph V) :
    HasIndependentPathCoverRepresentatives D := by
  classical
  rcases GallaiMilgramAux.exists_inclusion_minimal_terminal_path_cover_on
      D (Finset.univ : Finset V) with
    ⟨P, hmin⟩
  exact ⟨P, GallaiMilgramAux.pathCoverOn_univ_to_pathCover D hmin.1,
    GallaiMilgramAux.minimal_pathCoverOn_has_representatives D
      (Finset.univ : Finset V) P hmin⟩

end Chapter02
end Diestel
