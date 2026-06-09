import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma partitionClass_unique {X : Set V} {P : Finset (Set V)}
    (hP : IsVertexPartitionOf X P) {U W : Set V} (hU : U ∈ P) (hW : W ∈ P)
    {x : V} (hxU : x ∈ U) (hxW : x ∈ W) :
    U = W := by
  by_contra hne
  have hdisj := hP.2.1 U hU W hW hne
  exact Set.disjoint_left.mp hdisj hxU hxW

noncomputable def partitionClass (X : Set V) (P : Finset (Set V))
    (hP : IsVertexPartitionOf X P) (x : X) : {U : Set V // U ∈ P} :=
  ⟨Classical.choose (hP.2.2 x.1 x.2), (Classical.choose_spec (hP.2.2 x.1 x.2)).1⟩

lemma mem_partitionClass (X : Set V) (P : Finset (Set V))
    (hP : IsVertexPartitionOf X P) (x : X) :
    x.1 ∈ (partitionClass X P hP x).1 :=
  (Classical.choose_spec (hP.2.2 x.1 x.2)).2

lemma partitionClass_eq_of_mem {X : Set V} {P : Finset (Set V)}
    (hP : IsVertexPartitionOf X P) (x : X) {U : Set V} (hU : U ∈ P)
    (hxU : x.1 ∈ U) :
    partitionClass X P hP x = ⟨U, hU⟩ := by
  apply Subtype.ext
  exact partitionClass_unique hP (partitionClass X P hP x).2 hU
    (mem_partitionClass X P hP x) hxU

lemma partitionSubtype_natCard_eq (P : Finset (Set V)) :
    Nat.card {U : Set V // U ∈ P} = P.card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

lemma quotientReachable_of_edgeSubgraph_adj {G : MultiGraph V E} {F : Set E}
    {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P)
    {x y : G.vertexSet}
    (hxy : ((G.edgeSubgraph F).induce G.vertexSet).Adj x y) :
    (G.quotientEdgeSubgraph P {e : G.CrossEdge P | e.1 ∈ F}).Reachable
      (partitionClass G.vertexSet P hP x) (partitionClass G.vertexSet P hP y) := by
  classical
  by_cases hsame :
      partitionClass G.vertexSet P hP x = partitionClass G.vertexSet P hP y
  · simpa [hsame]
  · rcases hxy with ⟨hne, e, heF, heG, hlink⟩
    let U := partitionClass G.vertexSet P hP x
    let W := partitionClass G.vertexSet P hP y
    have hxU : x.1 ∈ U.1 := mem_partitionClass G.vertexSet P hP x
    have hyW : y.1 ∈ W.1 := mem_partitionClass G.vertexSet P hP y
    have hUW : U.1 ≠ W.1 := by
      intro h
      exact hsame (Subtype.ext h)
    let ce : G.CrossEdge P :=
      ⟨e, ⟨heG, x.1, y.1, hlink, U.1, U.2, W.1, W.2, hUW, hxU, hyW⟩⟩
    have hqadj :
        (G.quotientEdgeSubgraph P {e : G.CrossEdge P | e.1 ∈ F}).Adj U W := by
      refine ⟨?_, ce, ?_, x.1, hxU, y.1, hyW, hlink⟩
      · exact hsame
      · exact heF
    exact SimpleGraph.Adj.reachable hqadj

lemma quotientReachable_of_edgeSubgraph_reachable {G : MultiGraph V E} {F : Set E}
    {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P)
    {x y : G.vertexSet}
    (hxy : ((G.edgeSubgraph F).induce G.vertexSet).Reachable x y) :
    (G.quotientEdgeSubgraph P {e : G.CrossEdge P | e.1 ∈ F}).Reachable
      (partitionClass G.vertexSet P hP x) (partitionClass G.vertexSet P hP y) := by
  classical
  rcases hxy with ⟨w⟩
  induction w with
  | nil =>
      exact SimpleGraph.Reachable.refl _
  | cons hAdj _ ih =>
      exact SimpleGraph.Reachable.trans
        (quotientReachable_of_edgeSubgraph_adj (G := G) (F := F) (P := P) hP hAdj) ih

lemma quotientEdgeSubgraph_connected_of_spanningTree {G : MultiGraph V E} {F : Set E}
    {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P)
    (hPne : P.Nonempty) (hTree : G.IsSpanningTree F) :
    (G.quotientEdgeSubgraph P {e : G.CrossEdge P | e.1 ∈ F}).Connected := by
  classical
  haveI : Nonempty {U : Set V // U ∈ P} := by
    rcases hPne with ⟨U, hU⟩
    exact ⟨⟨U, hU⟩⟩
  rcases hTree with ⟨_hFfin, _hFsub, hTree⟩
  rcases hTree with hEmpty | hConn
  · rcases hPne with ⟨U, hU⟩
    rcases (hP.1 U hU).1 with ⟨x, hxU⟩
    exact False.elim (by simpa [hEmpty.1] using (hP.1 U hU).2 hxU)
  · rcases hConn with ⟨hConn, _hcard⟩
    refine ⟨fun U W => ?_⟩
    rcases (hP.1 U.1 U.2).1 with ⟨x, hxU⟩
    rcases (hP.1 W.1 W.2).1 with ⟨y, hyW⟩
    have hxG : x ∈ G.vertexSet := (hP.1 U.1 U.2).2 hxU
    have hyG : y ∈ G.vertexSet := (hP.1 W.1 W.2).2 hyW
    let x' : G.vertexSet := ⟨x, hxG⟩
    let y' : G.vertexSet := ⟨y, hyG⟩
    have hxpart : partitionClass G.vertexSet P hP x' = U :=
      partitionClass_eq_of_mem hP x' U.2 hxU
    have hypart : partitionClass G.vertexSet P hP y' = W :=
      partitionClass_eq_of_mem hP y' W.2 hyW
    have hreach : ((G.edgeSubgraph F).induce G.vertexSet).Reachable x' y' :=
      hConn.preconnected x' y'
    have hq :
        (G.quotientEdgeSubgraph P {e : G.CrossEdge P | e.1 ∈ F}).Reachable
          (partitionClass G.vertexSet P hP x') (partitionClass G.vertexSet P hP y') := by
      exact quotientReachable_of_edgeSubgraph_reachable (G := G) (F := F) (P := P) hP hreach
    simpa [hxpart, hypart] using hq

lemma partition_card_le_quotient_edge_card_add_one_of_spanningTree
    {G : MultiGraph V E} {F : Set E} {P : Finset (Set V)}
    (hP : IsVertexPartitionOf G.vertexSet P) (hPne : P.Nonempty)
    (hTree : G.IsSpanningTree F) :
    P.card ≤
      Nat.card
        (G.quotientEdgeSubgraph P {e : G.CrossEdge P | e.1 ∈ F}).edgeSet + 1 := by
  classical
  have hconn :=
    quotientEdgeSubgraph_connected_of_spanningTree (G := G) (F := F) (P := P) hP hPne hTree
  have hcard := hconn.card_vert_le_card_edgeSet_add_one
  simpa [partitionSubtype_natCard_eq] using hcard

lemma quotientEdgeLabel_exists {G : MultiGraph V E} {P : Finset (Set V)}
    {S : Set (G.CrossEdge P)}
    (q : (G.quotientEdgeSubgraph P S).edgeSet) :
    ∃ e : G.CrossEdge P, e ∈ S ∧
      ∃ U W : {U : Set V // U ∈ P}, (q : Sym2 {U : Set V // U ∈ P}) = s(U, W) ∧
        ∃ x ∈ U.1, ∃ y ∈ W.1, G.IsLink e.1 x y := by
  classical
  rcases q with ⟨qval, hq⟩
  change ∃ e : G.CrossEdge P, e ∈ S ∧
      ∃ U W : {U : Set V // U ∈ P}, qval = s(U, W) ∧
        ∃ x ∈ U.1, ∃ y ∈ W.1, G.IsLink e.1 x y
  induction qval using Sym2.inductionOn with
  | hf U W =>
      have hAdj : (G.quotientEdgeSubgraph P S).Adj U W := by
        simpa [SimpleGraph.mem_edgeSet] using hq
      rcases hAdj with ⟨_hne, e, heS, x, hx, y, hy, hlink⟩
      exact ⟨e, heS, U, W, rfl, x, hx, y, hy, hlink⟩

noncomputable def quotientEdgeLabel {G : MultiGraph V E} {P : Finset (Set V)}
    {S : Set (G.CrossEdge P)}
    (q : (G.quotientEdgeSubgraph P S).edgeSet) : G.CrossEdge P :=
  Classical.choose (quotientEdgeLabel_exists (G := G) (P := P) (S := S) q)

lemma quotientEdgeLabel_mem {G : MultiGraph V E} {P : Finset (Set V)}
    {S : Set (G.CrossEdge P)}
    (q : (G.quotientEdgeSubgraph P S).edgeSet) :
    quotientEdgeLabel (G := G) (P := P) (S := S) q ∈ S :=
  (Classical.choose_spec (quotientEdgeLabel_exists (G := G) (P := P) (S := S) q)).1

lemma quotientEdgeLabel_injective {G : MultiGraph V E} {P : Finset (Set V)}
    {S : Set (G.CrossEdge P)} (hP : IsVertexPartitionOf G.vertexSet P) :
    Function.Injective (quotientEdgeLabel (G := G) (P := P) (S := S)) := by
  classical
  intro q r hqr
  obtain ⟨_hqS, U, W, hqval, x, hxU, y, hyW, hqLink⟩ :=
    Classical.choose_spec (quotientEdgeLabel_exists (G := G) (P := P) (S := S) q)
  obtain ⟨_hrS, U', W', hrval, x', hxU', y', hyW', hrLink⟩ :=
    Classical.choose_spec (quotientEdgeLabel_exists (G := G) (P := P) (S := S) r)
  have hrLinkLabel : G.IsLink (quotientEdgeLabel (G := G) (P := P) (S := S) r).1 x' y' := by
    dsimp [quotientEdgeLabel]
    exact hrLink
  have hrLink' : G.IsLink (quotientEdgeLabel (G := G) (P := P) (S := S) q).1 x' y' := by
    simpa [hqr] using hrLinkLabel
  apply Subtype.ext
  rw [hqval, hrval]
  rcases hqLink.eq_and_eq_or_eq_and_eq hrLink' with hsame | hswap
  · rcases hsame with ⟨hxx, hyy⟩
    have hUU : U = U' := by
      apply Subtype.ext
      exact partitionClass_unique hP U.2 U'.2 hxU (by simpa [← hxx] using hxU')
    have hWW : W = W' := by
      apply Subtype.ext
      exact partitionClass_unique hP W.2 W'.2 hyW (by simpa [← hyy] using hyW')
    subst U'
    subst W'
    rfl
  · rcases hswap with ⟨hxy, hyx⟩
    have hUW : U = W' := by
      apply Subtype.ext
      exact partitionClass_unique hP U.2 W'.2 hxU (by simpa [← hxy] using hyW')
    have hWU : W = U' := by
      apply Subtype.ext
      exact partitionClass_unique hP W.2 U'.2 hyW (by simpa [← hyx] using hxU')
    subst W'
    subst U'
    exact Sym2.eq_swap

lemma quotient_edge_card_le_selected_crossEdge_card {G : MultiGraph V E} [Finite E]
    {P : Finset (Set V)} {S : Set (G.CrossEdge P)}
    (hP : IsVertexPartitionOf G.vertexSet P) :
    Nat.card (G.quotientEdgeSubgraph P S).edgeSet ≤ Nat.card S := by
  classical
  refine Nat.card_le_card_of_injective
    (fun q : (G.quotientEdgeSubgraph P S).edgeSet =>
      (⟨quotientEdgeLabel (G := G) (P := P) (S := S) q,
        quotientEdgeLabel_mem (G := G) (P := P) (S := S) q⟩ : S))
    ?_
  intro q r hqr
  apply quotientEdgeLabel_injective (G := G) (P := P) (S := S) hP
  exact congrArg Subtype.val hqr

lemma partition_card_sub_one_le_selected_crossEdges_of_spanningTree
    {G : MultiGraph V E} [Finite E] {F : Set E} {P : Finset (Set V)}
    (hP : IsVertexPartitionOf G.vertexSet P) (hTree : G.IsSpanningTree F) :
    P.card - 1 ≤ Nat.card {e : G.CrossEdge P | e.1 ∈ F} := by
  classical
  by_cases hPne : P.Nonempty
  · have hquot :=
      partition_card_le_quotient_edge_card_add_one_of_spanningTree
        (G := G) (F := F) (P := P) hP hPne hTree
    have hle :=
      quotient_edge_card_le_selected_crossEdge_card
        (G := G) (P := P) (S := {e : G.CrossEdge P | e.1 ∈ F}) hP
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hPne
    simp [hPne]

lemma crossEdge_sigma_injective_of_edgeDisjointFamily {G : MultiGraph V E}
    {k : ℕ} {T : Fin k → Set E} {P : Finset (Set V)}
    (hdisj : EdgeDisjointFamily T) :
    Function.Injective
      (fun x : Sigma fun i : Fin k => {e : G.CrossEdge P | e.1 ∈ T i} => x.2.1) := by
  classical
  rintro ⟨i, e⟩ ⟨j, f⟩ hsame
  have hedge : e.1.1 = f.1.1 := congrArg Subtype.val hsame
  have hij : i = j := by
    by_contra hne
    have hd : Disjoint (T i) (T j) := hdisj hne
    have hfmem : e.1.1 ∈ T j := by
      rw [hedge]
      exact f.2
    exact Set.disjoint_left.mp hd e.2 hfmem
  subst j
  have hef : e = f := by
    apply Subtype.ext
    exact hsame
  subst f
  rfl

lemma hasKEdgeDisjointSpanningTrees_partition_bound {G : MultiGraph V E} [Finite E]
    {k : ℕ} (hpack : G.HasKEdgeDisjointSpanningTrees k)
    {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P) :
    k * (P.card - 1) ≤ G.crossEdgeCount P := by
  classical
  rcases hpack with ⟨T, hTrees, hdisj⟩
  let D := Sigma fun i : Fin k => {e : G.CrossEdge P | e.1 ∈ T i}
  have hD_le_cross : Nat.card D ≤ Nat.card (G.CrossEdge P) := by
    refine Nat.card_le_card_of_injective
      (fun x : D => (x.2.1 : G.CrossEdge P)) ?_
    exact crossEdge_sigma_injective_of_edgeDisjointFamily
      (G := G) (T := T) (P := P) hdisj
  have hmul_le_D : k * (P.card - 1) ≤ Nat.card D := by
    rw [Nat.card_sigma]
    calc
      k * (P.card - 1) = ∑ _i : Fin k, (P.card - 1) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i : Fin k, Nat.card {e : G.CrossEdge P | e.1 ∈ T i} := by
        exact Finset.sum_le_sum fun i _ =>
          partition_card_sub_one_le_selected_crossEdges_of_spanningTree
            (G := G) (F := T i) (P := P) hP (hTrees i)
  exact hmul_le_D.trans (by simpa [D, crossEdgeCount, CrossEdge] using hD_le_cross)

end MultiGraph

end Chapter02
end Diestel
