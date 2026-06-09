import Chapter02.multigraph_spanning_tree_aux
import Chapter02.theorem_2_4_1_forward

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma empty_isSpanningTree_of_vertexSet_eq_empty {G : MultiGraph V E}
    (hV : G.vertexSet = ∅) :
    G.IsSpanningTree (∅ : Set E) := by
  exact ⟨Set.finite_empty, by simp, Or.inl ⟨hV, rfl⟩⟩

lemma hasOneEdgeDisjointSpanningTree_of_vertexSet_eq_empty {G : MultiGraph V E}
    (hV : G.vertexSet = ∅) :
    G.HasKEdgeDisjointSpanningTrees 1 := by
  refine ⟨fun _ : Fin 1 => (∅ : Set E), ?_, ?_⟩
  · intro _
    exact empty_isSpanningTree_of_vertexSet_eq_empty (G := G) hV
  · intro i j hij
    fin_cases i
    fin_cases j
    exact (hij rfl).elim

lemma connected_of_partition_bound_one {G : MultiGraph V E} [Finite E]
    (hne : G.vertexSet.Nonempty)
    (hbound : ∀ P : Finset (Set V), IsVertexPartitionOf G.vertexSet P →
      1 * (P.card - 1) ≤ G.crossEdgeCount P) :
    G.Connected := by
  classical
  rw [Connected]
  by_contra hnot
  have hnonempty : Nonempty G.vertexSet := by
    rcases hne with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  have hnotpre : ¬ G.toSimpleGraph.Preconnected := by
    intro hpre
    exact hnot { preconnected := hpre, nonempty := hnonempty }
  rw [SimpleGraph.Preconnected] at hnotpre
  push Not at hnotpre
  rcases hnotpre with ⟨x, y, hxy⟩
  let U : Set V := {v | ∃ hv : v ∈ G.vertexSet,
    G.toSimpleGraph.Reachable x ⟨v, hv⟩}
  let W : Set V := G.vertexSet \ U
  have hxU : x.1 ∈ U := ⟨x.2, SimpleGraph.Reachable.refl _⟩
  have hyNotU : y.1 ∉ U := by
    rintro ⟨hyG, hyreach⟩
    exact hxy (by simpa using hyreach)
  have hyW : y.1 ∈ W := ⟨y.2, hyNotU⟩
  have hUWne : U ≠ W := by
    intro hUW
    have hxW : x.1 ∈ W := by simpa [hUW] using hxU
    exact hxW.2 hxU
  let P : Finset (Set V) := {U, W}
  have hUP : U ∈ P := by simp [P]
  have hWP : W ∈ P := by simp [P, hUWne.symm]
  have hdisj : Disjoint U W := by
    rw [Set.disjoint_left]
    intro z hzU hzW
    exact hzW.2 hzU
  have hpart : IsVertexPartitionOf G.vertexSet P := by
    refine ⟨?_, ?_, ?_⟩
    · intro A hA
      have hAUW : A = U ∨ A = W := by simpa [P, hUWne] using hA
      rcases hAUW with rfl | rfl
      · exact ⟨⟨x.1, hxU⟩, fun z hz => hz.1⟩
      · exact ⟨⟨y.1, hyW⟩, fun z hz => hz.1⟩
    · intro A hA B hB hAB
      have hAUW : A = U ∨ A = W := by simpa [P, hUWne] using hA
      have hBUW : B = U ∨ B = W := by simpa [P, hUWne] using hB
      rcases hAUW with rfl | rfl <;> rcases hBUW with rfl | rfl
      · exact (hAB rfl).elim
      · exact hdisj
      · exact hdisj.symm
      · exact (hAB rfl).elim
    · intro z hz
      by_cases hzU : z ∈ U
      · exact ⟨U, hUP, hzU⟩
      · exact ⟨W, hWP, ⟨hz, hzU⟩⟩
  have hPcard : P.card = 2 := by
    simp [P, hUWne]
  have hNoCross : ∀ e : E, ¬ G.IsCrossEdge P e := by
    intro e he
    rcases he with ⟨_heG, a, b, hlink, A, hA, B, hB, hAB, haA, hbB⟩
    have hAUW : A = U ∨ A = W := by simpa [P, hUWne] using hA
    have hBUW : B = U ∨ B = W := by simpa [P, hUWne] using hB
    have no_UW {a b : V} (haU : a ∈ U) (hbW : b ∈ W)
        (hlinkab : G.IsLink e a b) : False := by
      rcases haU with ⟨haG, hareach⟩
      have hareach' : G.toSimpleGraph.Reachable x ⟨a, hlinkab.left_mem⟩ := by
        simpa using hareach
      have hneab : (⟨a, hlinkab.left_mem⟩ : G.vertexSet) ≠
          ⟨b, hlinkab.right_mem⟩ := by
        intro hab
        have habv : a = b := congrArg Subtype.val hab
        subst b
        exact hbW.2 ⟨hlinkab.left_mem, hareach'⟩
      have hadj : G.toSimpleGraph.Adj ⟨a, hlinkab.left_mem⟩ ⟨b, hlinkab.right_mem⟩ :=
        ⟨hneab, e, hlinkab⟩
      have hbU : b ∈ U :=
        ⟨hlinkab.right_mem, hareach'.trans (SimpleGraph.Adj.reachable hadj)⟩
      exact hbW.2 hbU
    rcases hAUW with rfl | rfl <;> rcases hBUW with rfl | rfl
    · exact hAB rfl
    · exact no_UW haA hbB hlink
    · exact no_UW hbB haA hlink.symm
    · exact hAB rfl
  have hCrossZero : G.crossEdgeCount P = 0 := by
    simp [crossEdgeCount, hNoCross]
  have hle := hbound P hpart
  have : 1 ≤ 0 := by
    simpa [hPcard, hCrossZero] using hle
  omega

theorem theorem_2_4_1_k_one {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] :
    G.Loopless →
      (G.HasKEdgeDisjointSpanningTrees 1 ↔
        ∀ P : Finset (Set V), IsVertexPartitionOf G.vertexSet P →
          1 * (P.card - 1) ≤ G.crossEdgeCount P) := by
  intro _hloopless
  constructor
  · intro hpack P hP
    exact theorem_2_4_1_forward (G := G) 1 hpack P hP
  · intro hbound
    by_cases hV : G.vertexSet = ∅
    · exact hasOneEdgeDisjointSpanningTree_of_vertexSet_eq_empty (G := G) hV
    · have hne : G.vertexSet.Nonempty := Set.nonempty_iff_ne_empty.mpr hV
      exact hasOneEdgeDisjointSpanningTree_of_connected (G := G)
        (connected_of_partition_bound_one (G := G) hne hbound)

end MultiGraph

end Chapter02
end Diestel
