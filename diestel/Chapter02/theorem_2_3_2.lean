import Chapter02.erdos_posa_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

open scoped BigOperators

/--
Diestel, Theorem 2.3.2 (Erdos-Posa).
There is a function `f : ℕ → ℕ` such that every finite graph contains either
`k` disjoint cycles or a set of at most `f k` vertices meeting all cycles.
-/
theorem theorem_2_3_2 :
    ∃ f : ℕ → ℕ, ErdosPosaCycleBound f := by
  refine ⟨ErdosPosa.bound, ?_⟩
  intro V G _ _ _ k
  classical
  by_cases hpack : HasKDisjointCycles G k
  · exact Or.inl hpack
  · right
    obtain ⟨H, hmax⟩ :=
      ErdosPosa.exists_maximal_degreeTwoOrThreeSubgraph G
    haveI : Finite H.edgeSet := Set.Finite.to_subtype (Set.toFinite _)
    haveI : ∀ v : V, Fintype (H.neighborSet v) := fun _ => Fintype.ofFinite _
    by_cases hlarge :
        erdosPosaS k < ((ErdosPosa.branchSet H).ncard : ℝ)
    · exact False.elim
        (hpack (ErdosPosa.hasKDisjointCycles_of_large_branchSet
          H hmax.1 k hlarge))
    · refine ⟨ErdosPosa.coverSet H, ?_, ?_⟩
      · have hB :
            (ErdosPosa.branchSet H).ncard ≤ Nat.ceil (erdosPosaS k) :=
          ErdosPosa.ncard_le_ceil_erdosPosaS_of_not_large hlarge
        have hX : (ErdosPosa.xSet H).ncard ≤ k :=
          ErdosPosa.xSet_ncard_le_of_not_hasKDisjointCycles
            hmax.1 hmax hpack
        exact ErdosPosa.coverSet_ncard_le_bound hX hB
      · exact ErdosPosa.coverSet_isCycleVertexCover_of_maximal hmax

end Chapter02
end Diestel
