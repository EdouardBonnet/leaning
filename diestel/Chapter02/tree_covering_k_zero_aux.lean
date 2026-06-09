import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma edgeSet_eq_empty_of_canCoverEdgesByAtMostKTrees_zero {G : MultiGraph V E}
    (hcover : G.CanCoverEdgesByAtMostKTrees 0) :
    G.edgeSet = ∅ := by
  classical
  ext e
  constructor
  · intro he
    exfalso
    rcases hcover with ⟨n, hn, T, _hForest, hCovered⟩
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    rcases hCovered e he with ⟨i, _hi⟩
    exact Fin.elim0 i
  · intro he
    exact False.elim (by simpa using he)

lemma canCoverEdgesByAtMostKTrees_zero_of_edgeSet_eq_empty {G : MultiGraph V E}
    (hE : G.edgeSet = ∅) :
    G.CanCoverEdgesByAtMostKTrees 0 := by
  refine ⟨0, le_rfl, fun i : Fin 0 => Fin.elim0 i, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro e he
    exact False.elim (by simpa [hE] using he)

lemma inducedEdgeCount_eq_zero_of_edgeSet_eq_empty {G : MultiGraph V E} [Finite E]
    (hE : G.edgeSet = ∅) (U : Set V) :
    G.inducedEdgeCount U = 0 := by
  simp [inducedEdgeCount, EdgeSetInside, hE]

lemma edgeSet_eq_empty_of_inducedEdgeCount_zero {G : MultiGraph V E} [Finite E]
    (hloop : G.Loopless)
    (hbound : ∀ U : Set V, U ⊆ G.vertexSet → U.Nonempty →
      G.inducedEdgeCount U ≤ 0) :
    G.edgeSet = ∅ := by
  classical
  ext e
  constructor
  · intro he
    exfalso
    rcases Graph.exists_isLink_of_mem_edgeSet (G := G) he with ⟨x, y, hlink⟩
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hloop he x hlink
    let U : Set V := {x, y}
    have hUsub : U ⊆ G.vertexSet := by
      intro z hz
      simp [U] at hz
      rcases hz with rfl | rfl
      · exact hlink.left_mem
      · exact hlink.right_mem
    have hUne : U.Nonempty := ⟨x, by simp [U]⟩
    have heInside : e ∈ G.EdgeSetInside U := by
      refine ⟨he, ?_⟩
      intro z hz
      rcases hz.eq_or_eq_of_isLink hlink with rfl | rfl <;> simp [U]
    have hpos : 0 < G.inducedEdgeCount U := by
      dsimp [inducedEdgeCount]
      haveI : Nonempty {e : E // e ∈ G.EdgeSetInside U} := ⟨⟨e, heInside⟩⟩
      exact Nat.card_pos
    exact (not_le_of_gt hpos) (hbound U hUsub hUne)
  · intro he
    exact False.elim (by simpa using he)

/-- The `k = 0` specialization of Diestel, Theorem 2.4.3. -/
theorem theorem_2_4_3_k_zero {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] :
    G.Loopless →
      (G.CanCoverEdgesByAtMostKTrees 0 ↔
        ∀ U : Set V, U ⊆ G.vertexSet → U.Nonempty →
          G.inducedEdgeCount U ≤ 0 * (U.ncard - 1)) := by
  intro hloop
  constructor
  · intro hcover U _hUsub _hUne
    have hE := edgeSet_eq_empty_of_canCoverEdgesByAtMostKTrees_zero
      (G := G) hcover
    have hzero := inducedEdgeCount_eq_zero_of_edgeSet_eq_empty
      (G := G) hE U
    simpa [hzero]
  · intro hbound
    have hE : G.edgeSet = ∅ :=
      edgeSet_eq_empty_of_inducedEdgeCount_zero (G := G) hloop
        (fun U hUsub hUne => by simpa using hbound U hUsub hUne)
    exact canCoverEdgesByAtMostKTrees_zero_of_edgeSet_eq_empty (G := G) hE

end MultiGraph

end Chapter02
end Diestel
