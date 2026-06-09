import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma edgeBoundary_subset_edgeSet (G : MultiGraph V E) (U : Set V) :
    G.edgeBoundary U ⊆ G.edgeSet := by
  intro e he
  exact he.1

lemma mem_of_adj_delete_edgeBoundary {G : MultiGraph V E} {U : Set V}
    {x y : G.vertexSet}
    (hxy : ((G.edgeSubgraph (G.edgeSet \ G.edgeBoundary U)).induce G.vertexSet).Adj x y)
    (hxU : x.1 ∈ U) :
    y.1 ∈ U := by
  classical
  by_contra hyU
  rcases hxy with ⟨_hne, e, heDel, _heG, hlink⟩
  exact heDel.2 ⟨heDel.1, x.1, y.1, hlink, hxU, hlink.right_mem, hyU⟩

lemma mem_of_reachable_delete_edgeBoundary {G : MultiGraph V E} {U : Set V}
    {x y : G.vertexSet}
    (hxy : ((G.edgeSubgraph (G.edgeSet \ G.edgeBoundary U)).induce G.vertexSet).Reachable x y)
    (hxU : x.1 ∈ U) :
    y.1 ∈ U := by
  classical
  rcases hxy with ⟨w⟩
  induction w with
  | nil =>
      exact hxU
  | cons hAdj _ ih =>
      exact ih (mem_of_adj_delete_edgeBoundary (G := G) (U := U) hAdj hxU)

/--
The cut-counting step in Diestel's proof of Corollary 2.4.2:
in an `l`-edge-connected multigraph, every proper vertex side has at
least `l` boundary edges.
-/
lemma edgeBoundary_ncard_ge_of_isLEdgeConnected {G : MultiGraph V E} [Finite E]
    {l : ℕ} (hconn : G.IsLEdgeConnected l) {U : Set V}
    {x y : V} (hxG : x ∈ G.vertexSet) (hxU : x ∈ U)
    (hyG : y ∈ G.vertexSet) (hyU : y ∉ U) :
    l ≤ (G.edgeBoundary U).ncard := by
  classical
  by_contra hnot
  have hlt : (G.edgeBoundary U).ncard < l := Nat.lt_of_not_ge hnot
  have hconnected :
      ((G.edgeSubgraph (G.edgeSet \ G.edgeBoundary U)).induce G.vertexSet).Connected :=
    hconn (G.edgeBoundary U) (Set.toFinite _) (edgeBoundary_subset_edgeSet G U) hlt
  let x' : G.vertexSet := ⟨x, hxG⟩
  let y' : G.vertexSet := ⟨y, hyG⟩
  have hreach :
      ((G.edgeSubgraph (G.edgeSet \ G.edgeBoundary U)).induce G.vertexSet).Reachable x' y' :=
    hconnected.preconnected x' y'
  exact hyU (mem_of_reachable_delete_edgeBoundary (G := G) (U := U) hreach hxU)

lemma edgeBoundary_ncard_ge_of_partition_class {G : MultiGraph V E} [Finite E]
    {l : ℕ} (hconn : G.IsLEdgeConnected l) {P : Finset (Set V)}
    (hP : IsVertexPartitionOf G.vertexSet P) {U W : Set V}
    (hU : U ∈ P) (hW : W ∈ P) (hUW : U ≠ W) :
    l ≤ (G.edgeBoundary U).ncard := by
  classical
  rcases (hP.1 U hU).1 with ⟨x, hxU⟩
  rcases (hP.1 W hW).1 with ⟨y, hyW⟩
  exact edgeBoundary_ncard_ge_of_isLEdgeConnected (G := G) (l := l) hconn
    ((hP.1 U hU).2 hxU) hxU ((hP.1 W hW).2 hyW)
    (fun hyU =>
      Set.disjoint_left.mp (hP.2.1 U hU W hW hUW) hyU hyW)

lemma edgeBoundary_subset_crossEdges_of_partition_class {G : MultiGraph V E}
    {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P)
    {U : Set V} (hU : U ∈ P) :
    G.edgeBoundary U ⊆ {e : E | G.IsCrossEdge P e} := by
  classical
  intro e he
  rcases he with ⟨heG, x, y, hlink, hxU, hyG, hyU⟩
  rcases hP.2.2 y hyG with ⟨W, hW, hyW⟩
  have hUW : U ≠ W := by
    intro hUW
    exact hyU (by simpa [hUW] using hyW)
  exact ⟨heG, x, y, hlink, U, hU, W, hW, hUW, hxU, hyW⟩

lemma edgeBoundary_ncard_le_crossEdgeCount_of_partition_class {G : MultiGraph V E}
    [Finite E] {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P)
    {U : Set V} (hU : U ∈ P) :
    (G.edgeBoundary U).ncard ≤ G.crossEdgeCount P := by
  classical
  have hle :
      (G.edgeBoundary U).ncard ≤ ({e : E | G.IsCrossEdge P e}).ncard :=
    Set.ncard_le_ncard (edgeBoundary_subset_crossEdges_of_partition_class
      (G := G) (P := P) hP hU)
  simpa [crossEdgeCount, Set.ncard] using hle

lemma le_crossEdgeCount_of_isLEdgeConnected_partition_class {G : MultiGraph V E}
    [Finite E] {l : ℕ} (hconn : G.IsLEdgeConnected l)
    {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P)
    {U W : Set V} (hU : U ∈ P) (hW : W ∈ P) (hUW : U ≠ W) :
    l ≤ G.crossEdgeCount P :=
  le_trans
    (edgeBoundary_ncard_ge_of_partition_class (G := G) (l := l) hconn hP hU hW hUW)
    (edgeBoundary_ncard_le_crossEdgeCount_of_partition_class (G := G) (P := P) hP hU)

/-- Incidences between partition classes and their boundary edges. -/
abbrev BoundaryIncidence (G : MultiGraph V E) (P : Finset (Set V)) :=
  Sigma fun U : {U : Set V // U ∈ P} => {e : E // e ∈ G.edgeBoundary U.1}

/-- The partition classes whose boundary contains a fixed crossing edge. -/
abbrev CrossEdgeBoundaryClass (G : MultiGraph V E) (P : Finset (Set V))
    (e : G.CrossEdge P) :=
  {U : {U : Set V // U ∈ P} // e.1 ∈ G.edgeBoundary U.1}

noncomputable def boundaryIncidenceEquivCrossEdgeSigma {G : MultiGraph V E}
    {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P) :
    BoundaryIncidence G P ≃ Sigma fun e : G.CrossEdge P =>
      CrossEdgeBoundaryClass G P e where
  toFun x :=
    ⟨⟨x.2.1, edgeBoundary_subset_crossEdges_of_partition_class
      (G := G) (P := P) hP x.1.2 x.2.2⟩, ⟨x.1, x.2.2⟩⟩
  invFun x := ⟨x.2.1, ⟨x.1.1, x.2.2⟩⟩
  left_inv x := by
    cases x with
    | mk U e =>
        cases e
        rfl
  right_inv x := by
    cases x with
    | mk e U =>
        cases U
        rfl

lemma inc_vertices_ncard_le_two_of_isLink {G : MultiGraph V E}
    {e : E} {x y : V} (hlink : G.IsLink e x y) :
    ({z : V | G.Inc e z}).ncard ≤ 2 := by
  classical
  have hsub : {z : V | G.Inc e z} ⊆ ({x, y} : Set V) := by
    intro z hz
    rcases hz.eq_or_eq_of_isLink hlink with rfl | rfl <;> simp
  have hpairFinite : ({x, y} : Set V).Finite := by simp
  have hpairCard : ({x, y} : Set V).ncard ≤ 2 := by
    calc
      ({x, y} : Set V).ncard = (insert x ({y} : Set V)).ncard := rfl
      _ ≤ ({y} : Set V).ncard + 1 := Set.ncard_insert_le x ({y} : Set V)
      _ = 2 := by simp
  exact (Set.ncard_le_ncard hsub hpairFinite).trans hpairCard

lemma crossEdgeBoundaryClass_natCard_le_two {G : MultiGraph V E}
    {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P)
    (e : G.CrossEdge P) :
    Nat.card (CrossEdgeBoundaryClass G P e) ≤ 2 := by
  classical
  rcases e.2 with ⟨_heG, x, y, hlink, _hcross⟩
  have hincSub : {z : V | G.Inc e.1 z} ⊆ ({x, y} : Set V) := by
    intro z hz
    rcases hz.eq_or_eq_of_isLink hlink with rfl | rfl <;> simp
  have hincFinite : ({z : V | G.Inc e.1 z} : Set V).Finite :=
    (by simp : ({x, y} : Set V).Finite).subset hincSub
  haveI : Finite {x : V // G.Inc e.1 x} := hincFinite.to_subtype
  let f : CrossEdgeBoundaryClass G P e → {x : V // G.Inc e.1 x} :=
    fun U =>
      ⟨Classical.choose U.2.2,
        by
          rcases Classical.choose_spec U.2.2 with ⟨y, hlink, _hxU, _hyG, _hyU⟩
          exact hlink.inc_left⟩
  have hf : Function.Injective f := by
    intro U W hUW
    apply Subtype.ext
    apply Subtype.ext
    by_contra hne
    have hvertex : (f U).1 = (f W).1 := congrArg Subtype.val hUW
    rcases Classical.choose_spec U.2.2 with ⟨yU, _hlinkU, hxU, _hyGU, _hyUU⟩
    rcases Classical.choose_spec W.2.2 with ⟨yW, _hlinkW, hxW, _hyGW, _hyUW⟩
    have hdisj := hP.2.1 U.1.1 U.1.2 W.1.1 W.1.2 hne
    have hchosen : Classical.choose U.2.2 = Classical.choose W.2.2 := by
      simpa [f] using hvertex
    exact Set.disjoint_left.mp hdisj hxU (by simpa [hchosen] using hxW)
  have hle :
      Nat.card (CrossEdgeBoundaryClass G P e) ≤ Nat.card {x : V // G.Inc e.1 x} :=
    Nat.card_le_card_of_injective f hf
  exact hle.trans (by simpa [Nat.card_coe_set_eq] using
    inc_vertices_ncard_le_two_of_isLink (G := G) (e := e.1) hlink)

lemma boundaryIncidence_natCard_eq_sum {G : MultiGraph V E} [Finite E]
    (P : Finset (Set V)) :
    Nat.card (BoundaryIncidence G P) =
      ∑ U : {U : Set V // U ∈ P}, (G.edgeBoundary U.1).ncard := by
  classical
  rw [Nat.card_sigma]
  exact Finset.sum_congr rfl fun U _ => by
    exact Nat.card_coe_set_eq (G.edgeBoundary U.1)

lemma crossEdgeBoundarySigma_natCard_eq_sum {G : MultiGraph V E}
    (P : Finset (Set V)) [Fintype (G.CrossEdge P)] :
    Nat.card (Sigma fun e : G.CrossEdge P => CrossEdgeBoundaryClass G P e) =
      ∑ e : G.CrossEdge P, Nat.card (CrossEdgeBoundaryClass G P e) := by
  classical
  exact Nat.card_sigma

lemma sum_edgeBoundary_ncard_le_two_mul_crossEdgeCount {G : MultiGraph V E}
    [Finite E] {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P) :
    (∑ U : {U : Set V // U ∈ P}, (G.edgeBoundary U.1).ncard) ≤
      2 * G.crossEdgeCount P := by
  classical
  letI : Fintype (G.CrossEdge P) := Fintype.ofFinite _
  have hcongr :
      Nat.card (BoundaryIncidence G P) =
        Nat.card (Sigma fun e : G.CrossEdge P => CrossEdgeBoundaryClass G P e) :=
    Nat.card_congr (boundaryIncidenceEquivCrossEdgeSigma (G := G) (P := P) hP)
  calc
    (∑ U : {U : Set V // U ∈ P}, (G.edgeBoundary U.1).ncard) =
        Nat.card (BoundaryIncidence G P) :=
      (boundaryIncidence_natCard_eq_sum (G := G) P).symm
    _ = Nat.card (Sigma fun e : G.CrossEdge P => CrossEdgeBoundaryClass G P e) := hcongr
    _ = ∑ e : G.CrossEdge P, Nat.card (CrossEdgeBoundaryClass G P e) :=
      crossEdgeBoundarySigma_natCard_eq_sum (G := G) P
    _ ≤ ∑ _e : G.CrossEdge P, 2 := by
      exact Finset.sum_le_sum fun e _ =>
        crossEdgeBoundaryClass_natCard_le_two (G := G) (P := P) hP e
    _ = 2 * G.crossEdgeCount P := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card (α := G.CrossEdge P)]
      simp [crossEdgeCount, CrossEdge, mul_comm]

lemma partitionClassSubtype_natCard_eq (P : Finset (Set V)) :
    Nat.card {U : Set V // U ∈ P} = P.card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

lemma exists_ne_partition_class_of_mem_of_two_le_card {P : Finset (Set V)}
    {U : Set V} (hU : U ∈ P) (hcard : 2 ≤ P.card) :
    ∃ W ∈ P, U ≠ W := by
  classical
  have hEraseCard := Finset.card_erase_add_one hU
  have hErasePos : 0 < (P.erase U).card := by omega
  rcases Finset.card_pos.mp hErasePos with ⟨W, hW⟩
  rw [Finset.mem_erase] at hW
  exact ⟨W, hW.2, fun hUW => hW.1 hUW.symm⟩

lemma two_mul_k_mul_partition_card_le_sum_edgeBoundary {G : MultiGraph V E}
    [Finite E] {k : ℕ} (hconn : G.IsLEdgeConnected (2 * k))
    {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P)
    (hcard : 2 ≤ P.card) :
    (2 * k) * P.card ≤
      ∑ U : {U : Set V // U ∈ P}, (G.edgeBoundary U.1).ncard := by
  classical
  have hsumConst :
      (∑ _U : {U : Set V // U ∈ P}, 2 * k) = (2 * k) * P.card := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.card_coe]
    ac_rfl
  calc
    (2 * k) * P.card = ∑ _U : {U : Set V // U ∈ P}, 2 * k := hsumConst.symm
    _ ≤ ∑ U : {U : Set V // U ∈ P}, (G.edgeBoundary U.1).ncard := by
      refine Finset.sum_le_sum fun U _ => ?_
      rcases exists_ne_partition_class_of_mem_of_two_le_card (P := P) U.2 hcard with
        ⟨W, hW, hUW⟩
      exact edgeBoundary_ncard_ge_of_partition_class
        (G := G) (l := 2 * k) hconn hP U.2 hW hUW

/--
The full cut-counting inequality in Diestel's proof of Corollary 2.4.2:
`2k`-edge-connectivity implies the Nash-Williams/Tutte partition lower
bound on crossing edges.
-/
lemma isLEdgeConnected_partition_bound {G : MultiGraph V E} [Finite E]
    {k : ℕ} (hconn : G.IsLEdgeConnected (2 * k))
    {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P) :
    k * (P.card - 1) ≤ G.crossEdgeCount P := by
  classical
  by_cases hcard : 2 ≤ P.card
  · have hlower :=
      two_mul_k_mul_partition_card_le_sum_edgeBoundary
        (G := G) (k := k) hconn hP hcard
    have hupper :=
      sum_edgeBoundary_ncard_le_two_mul_crossEdgeCount (G := G) (P := P) hP
    have hdouble : 2 * (k * P.card) ≤ 2 * G.crossEdgeCount P := by
      calc
        2 * (k * P.card) = (2 * k) * P.card := (Nat.mul_assoc 2 k P.card).symm
        _ ≤ ∑ U : {U : Set V // U ∈ P}, (G.edgeBoundary U.1).ncard := hlower
        _ ≤ 2 * G.crossEdgeCount P := hupper
    have hkp : k * P.card ≤ G.crossEdgeCount P :=
      Nat.le_of_mul_le_mul_left hdouble (by decide : 0 < 2)
    exact (Nat.mul_le_mul_left k (Nat.sub_le P.card 1)).trans hkp
  · have hle : P.card ≤ 1 := by omega
    have hzero : P.card - 1 = 0 := by omega
    simp [hzero]

end MultiGraph

end Chapter02
end Diestel
