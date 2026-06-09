import Chapter01.proposition_1_3_1
import Chapter02.cycle_packing_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

/-- The `k = 1` specialization of Diestel, Lemma 2.3.1. -/
theorem lemma_2_3_1_k_one {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] :
    G.IsCubic →
      erdosPosaS 1 < (G.vertexSet.ncard : ℝ) →
        G.HasKDisjointCycles 1 := by
  classical
  intro hCubic hLarge
  have hLarge' : (1 : ℝ) < (G.vertexSet.ncard : ℝ) := by
    simpa [erdosPosaS] using hLarge
  have hpos : 0 < G.vertexSet.ncard := by
    by_contra hnot
    have hz : G.vertexSet.ncard = 0 := Nat.eq_zero_of_not_pos hnot
    have hz_real : (G.vertexSet.ncard : ℝ) = 0 := by
      exact_mod_cast hz
    nlinarith
  have hvertex_nonempty : G.vertexSet.Nonempty :=
    (Set.ncard_pos (s := G.vertexSet)).mp hpos
  haveI : Nonempty G.vertexSet := hvertex_nonempty.to_subtype
  letI : Fintype G.vertexSet := Fintype.ofFinite G.vertexSet
  letI : DecidableRel G.toSimpleGraph.Adj := Classical.decRel _
  by_cases hmin : 2 ≤ G.toSimpleGraph.minDegree
  · obtain ⟨_, hcyclePart⟩ :=
      Diestel.Chapter01.proposition_1_3_1 G.toSimpleGraph
    obtain ⟨r, c, hc, _hlen⟩ := hcyclePart hmin
    exact hasOneDisjointCycle_of_simpleCycle (G := G) hc
  · obtain ⟨x, hxmindeg⟩ := G.toSimpleGraph.exists_minimal_degree_vertex
    have hshadow_lt : G.toSimpleGraph.degree x < 2 := by
      have hmin_lt : G.toSimpleGraph.minDegree < 2 := Nat.lt_of_not_ge hmin
      rwa [hxmindeg] at hmin_lt
    have hshadow_le : G.toSimpleGraph.degree x ≤ 1 := by
      omega
    have hmulti_deg : G.degree x.1 = 3 := hCubic.2 x.1 x.2
    obtain ⟨e, f, y, hef, hxy, he, hf⟩ :=
      exists_parallel_edges_of_simple_degree_le_one (G := G)
        hCubic.1 x.2 hmulti_deg hshadow_le
    exact hasOneDisjointCycle_of_parallel_edges (G := G) hef hxy he hf

/-- Boundary-inclusive `k = 1` specialization of Diestel, Lemma 2.3.1. -/
theorem lemma_2_3_1_k_one_ge {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] :
    G.IsCubic →
      erdosPosaS 1 ≤ (G.vertexSet.ncard : ℝ) →
        G.HasKDisjointCycles 1 := by
  classical
  intro hCubic hLarge
  have hOneLe : (1 : ℝ) ≤ (G.vertexSet.ncard : ℝ) := by
    simpa [erdosPosaS] using hLarge
  have hposReal : (0 : ℝ) < (G.vertexSet.ncard : ℝ) := by
    nlinarith
  have hpos : 0 < G.vertexSet.ncard := by
    exact_mod_cast hposReal
  have hvertex_nonempty : G.vertexSet.Nonempty :=
    (Set.ncard_pos (s := G.vertexSet)).mp hpos
  haveI : Nonempty G.vertexSet := hvertex_nonempty.to_subtype
  letI : Fintype G.vertexSet := Fintype.ofFinite G.vertexSet
  letI : DecidableRel G.toSimpleGraph.Adj := Classical.decRel _
  by_cases hmin : 2 ≤ G.toSimpleGraph.minDegree
  · obtain ⟨_, hcyclePart⟩ :=
      Diestel.Chapter01.proposition_1_3_1 G.toSimpleGraph
    obtain ⟨r, c, hc, _hlen⟩ := hcyclePart hmin
    exact hasOneDisjointCycle_of_simpleCycle (G := G) hc
  · obtain ⟨x, hxmindeg⟩ := G.toSimpleGraph.exists_minimal_degree_vertex
    have hshadow_lt : G.toSimpleGraph.degree x < 2 := by
      have hmin_lt : G.toSimpleGraph.minDegree < 2 := Nat.lt_of_not_ge hmin
      rwa [hxmindeg] at hmin_lt
    have hshadow_le : G.toSimpleGraph.degree x ≤ 1 := by
      omega
    have hmulti_deg : G.degree x.1 = 3 := hCubic.2 x.1 x.2
    obtain ⟨e, f, y, hef, hxy, he, hf⟩ :=
      exists_parallel_edges_of_simple_degree_le_one (G := G)
        hCubic.1 x.2 hmulti_deg hshadow_le
    exact hasOneDisjointCycle_of_parallel_edges (G := G) hef hxy he hf

end MultiGraph

end Chapter02
end Diestel
