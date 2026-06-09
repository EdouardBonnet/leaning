import Chapter02.tree_packing_quotient_aux

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter02

universe u v

namespace SimpleGraph

variable {V : Type u} {H : SimpleGraph V}

lemma reachable_induce_mono {U X : Set V} (hUX : U ⊆ X)
    {x y : U} (hxy : (H.induce U).Reachable x y) :
    (H.induce X).Reachable
      (⟨x.1, hUX x.2⟩ : X) (⟨y.1, hUX y.2⟩ : X) := by
  rcases hxy with ⟨w⟩
  induction w with
  | nil =>
      exact SimpleGraph.Reachable.refl _
  | @cons a b c hab _ ih =>
      have habX :
          (H.induce X).Adj (⟨a.1, hUX a.2⟩ : X) (⟨b.1, hUX b.2⟩ : X) := hab
      exact SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable habX) ih

end SimpleGraph

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma edgeSetInside_not_isCrossEdge_of_partition
    {G : MultiGraph V E} {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P)
    {U : Set V} (hU : U ∈ P) {e : E}
    (heU : e ∈ G.EdgeSetInside U) :
    ¬ G.IsCrossEdge P e := by
  intro heCross
  rcases heCross with ⟨_heG, x, y, hlink, A, hA, B, hB, hAB, hxA, hyB⟩
  have hxU : x ∈ U := heU.2 x hlink.inc_left
  have hyU : y ∈ U := heU.2 y hlink.inc_right
  have hAU : A = U :=
    partitionClass_unique (X := G.vertexSet) hP hA hU hxA hxU
  have hBU : B = U :=
    partitionClass_unique (X := G.vertexSet) hP hB hU hyB hyU
  exact hAB (hAU.trans hBU.symm)

lemma edgeSetInside_disjoint_of_ne_partitionClass
    {G : MultiGraph V E} {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P)
    {U W : Set V} (hU : U ∈ P) (hW : W ∈ P) (hUW : U ≠ W) :
    Disjoint (G.EdgeSetInside U) (G.EdgeSetInside W) := by
  rw [Set.disjoint_left]
  intro e heU heW
  rcases G.exists_isLink_of_mem_edgeSet heU.1 with ⟨x, y, hlink⟩
  have hxU : x ∈ U := heU.2 x hlink.inc_left
  have hxW : x ∈ W := heW.2 x hlink.inc_left
  exact hUW (partitionClass_unique (X := G.vertexSet) hP hU hW hxU hxW)

/-- Lift a quotient edge set back to the underlying multiedge labels of `G`. -/
def liftQuotientEdgeSet (G : MultiGraph V E) {P : Finset (Set V)}
    (Q : Set (G.CrossEdge P)) : Set E :=
  {e | ∃ q : G.CrossEdge P, q ∈ Q ∧ q.1 = e}

lemma mem_liftQuotientEdgeSet {G : MultiGraph V E} {P : Finset (Set V)}
    {Q : Set (G.CrossEdge P)} {q : G.CrossEdge P} (hq : q ∈ Q) :
    q.1 ∈ G.liftQuotientEdgeSet Q :=
  ⟨q, hq, rfl⟩

lemma liftQuotientEdgeSet_subset_edgeSet {G : MultiGraph V E} {P : Finset (Set V)}
    {Q : Set (G.CrossEdge P)} :
    G.liftQuotientEdgeSet Q ⊆ G.edgeSet := by
  rintro e ⟨q, _hq, rfl⟩
  exact q.2.1

lemma liftQuotientEdgeSet_disjoint_edgeSetInside
    {G : MultiGraph V E} {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P)
    {U : Set V} (hU : U ∈ P) {Q : Set (G.CrossEdge P)} :
    Disjoint (G.liftQuotientEdgeSet Q) (G.EdgeSetInside U) := by
  rw [Set.disjoint_left]
  rintro e ⟨q, _hq, rfl⟩ heU
  exact edgeSetInside_not_isCrossEdge_of_partition
    (G := G) (P := P) hP hU heU q.2

/--
The edge set obtained by gluing one tree inside each partition class to one
spanning tree of the quotient.
-/
def gluedTreeEdgeSet (G : MultiGraph V E) {P : Finset (Set V)}
    (A : {U : Set V // U ∈ P} → Set E) (Q : Set (G.CrossEdge P)) : Set E :=
  (⋃ U : {U : Set V // U ∈ P}, A U) ∪ G.liftQuotientEdgeSet Q

lemma mem_gluedTreeEdgeSet_internal {G : MultiGraph V E} {P : Finset (Set V)}
    {A : {U : Set V // U ∈ P} → Set E} {Q : Set (G.CrossEdge P)}
    (U : {U : Set V // U ∈ P}) {e : E} (he : e ∈ A U) :
    e ∈ G.gluedTreeEdgeSet A Q := by
  exact Or.inl (Set.mem_iUnion.mpr ⟨U, he⟩)

lemma mem_gluedTreeEdgeSet_quotient {G : MultiGraph V E} {P : Finset (Set V)}
    {A : {U : Set V // U ∈ P} → Set E} {Q : Set (G.CrossEdge P)}
    {q : G.CrossEdge P} (hq : q ∈ Q) :
    q.1 ∈ G.gluedTreeEdgeSet A Q := by
  exact Or.inr (mem_liftQuotientEdgeSet (G := G) hq)

lemma gluedTreeEdgeSet_subset_edgeSet
    {G : MultiGraph V E} {P : Finset (Set V)}
    {A : {U : Set V // U ∈ P} → Set E} {Q : Set (G.CrossEdge P)}
    (hA : ∀ U : {U : Set V // U ∈ P}, A U ⊆ G.edgeSet) :
    G.gluedTreeEdgeSet A Q ⊆ G.edgeSet := by
  intro e he
  rcases he with heA | heQ
  · rcases Set.mem_iUnion.mp heA with ⟨U, heU⟩
    exact hA U heU
  · exact liftQuotientEdgeSet_subset_edgeSet (G := G) heQ

lemma isSpanningTreeOn_connected_of_nonempty
    {G : MultiGraph V E} {U : Set V} {F : Set E}
    (hF : G.IsSpanningTreeOn U F) (hUne : U.Nonempty) :
    ((G.edgeSubgraph F).induce U).Connected := by
  rcases hF with ⟨_hUsub, _hfin, _hsub, hempty | hconn⟩
  · exact False.elim (by
      rcases hempty with ⟨hUempty, _hFempty⟩
      rw [hUempty] at hUne
      exact Set.not_nonempty_empty hUne)
  · exact hconn.1

lemma isQuotientSpanningTree_connected_of_partition_nonempty
    {G : MultiGraph V E} {P : Finset (Set V)} {Q : Set (G.CrossEdge P)}
    (hQ : G.IsQuotientSpanningTree P Q) (hPne : P.Nonempty) :
    (G.quotientEdgeSubgraph P Q).Connected := by
  rcases hQ with ⟨_hfin, hempty | hconn⟩
  · exact False.elim (by
      rcases hempty with ⟨hPempty, _hQempty⟩
      exact Finset.not_nonempty_iff_eq_empty.mpr hPempty hPne)
  · exact hconn.1

lemma isSpanningTreeOn_ncard_add_one_eq_of_nonempty
    {G : MultiGraph V E} {U : Set V} {F : Set E}
    (hF : G.IsSpanningTreeOn U F) (hUne : U.Nonempty) :
    F.ncard + 1 = U.ncard := by
  rcases hF with ⟨_hUsub, _hfin, _hsub, hempty | hconn⟩
  · exact False.elim (by
      rcases hempty with ⟨hUempty, _hFempty⟩
      rw [hUempty] at hUne
      exact Set.not_nonempty_empty hUne)
  · exact hconn.2

lemma isQuotientSpanningTree_ncard_add_one_eq_of_partition_nonempty
    {G : MultiGraph V E} {P : Finset (Set V)} {Q : Set (G.CrossEdge P)}
    (hQ : G.IsQuotientSpanningTree P Q) (hPne : P.Nonempty) :
    Q.ncard + 1 = P.card := by
  rcases hQ with ⟨_hfin, hempty | hconn⟩
  · exact False.elim (by
      rcases hempty with ⟨hPempty, _hQempty⟩
      exact Finset.not_nonempty_iff_eq_empty.mpr hPempty hPne)
  · exact hconn.2

lemma isVertexPartitionOf_sum_ncard_eq
    {X : Set V} [Finite V] {P : Finset (Set V)}
    (hP : IsVertexPartitionOf X P) :
    (∑ U ∈ P, U.ncard) = X.ncard := by
  classical
  let f : Set V → Finset V := fun U => (Set.toFinite U).toFinset
  have hdisj : (P : Set (Set V)).PairwiseDisjoint f := by
    intro U hU W hW hUW
    change Disjoint (f U) (f W)
    rw [Finset.disjoint_left]
    intro x hxU hxW
    exact Set.disjoint_left.mp (hP.2.1 U hU W hW hUW)
      ((Set.toFinite U).mem_toFinset.mp hxU)
      ((Set.toFinite W).mem_toFinset.mp hxW)
  have hcover : P.biUnion f = (Set.toFinite X).toFinset := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨U, hU, hxU⟩
      exact (Set.toFinite X).mem_toFinset.mpr (by
        have hxU' : x ∈ U := (Set.toFinite U).mem_toFinset.mp hxU
        exact (hP.1 U hU).2 hxU' : x ∈ X)
    · intro hx
      have hxX : x ∈ X := (Set.toFinite X).mem_toFinset.mp hx
      rcases hP.2.2 x hxX with ⟨U, hU, hxU⟩
      exact Finset.mem_biUnion.mpr ⟨U, hU, (Set.toFinite U).mem_toFinset.mpr hxU⟩
  have hcard :=
    Finset.card_biUnion (s := P) (t := f) hdisj
  calc
    (∑ U ∈ P, U.ncard) = ∑ U ∈ P, (f U).card := by
      apply Finset.sum_congr rfl
      intro U _hU
      exact Set.ncard_eq_toFinset_card U (Set.toFinite U)
    _ = (P.biUnion f).card := hcard.symm
    _ = (Set.toFinite X).toFinset.card := by rw [hcover]
    _ = X.ncard := (Set.ncard_eq_toFinset_card X (Set.toFinite X)).symm

lemma isVertexPartitionOf_subtype_sum_ncard_eq
    {X : Set V} [Finite V] {P : Finset (Set V)}
    (hP : IsVertexPartitionOf X P) :
    (∑ U : {U : Set V // U ∈ P}, U.1.ncard) = X.ncard := by
  classical
  calc
    (∑ U : {U : Set V // U ∈ P}, U.1.ncard) =
        ∑ U ∈ P, U.ncard := by
      rw [← Finset.sum_attach P (fun U : Set V => U.ncard)]
      rw [Finset.univ_eq_attach P]
    _ = X.ncard := isVertexPartitionOf_sum_ncard_eq hP

lemma liftQuotientEdgeSet_eq_image {G : MultiGraph V E} {P : Finset (Set V)}
    (Q : Set (G.CrossEdge P)) :
    G.liftQuotientEdgeSet Q = (fun q : G.CrossEdge P => q.1) '' Q := by
  ext e
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, rfl⟩

lemma liftQuotientEdgeSet_ncard {G : MultiGraph V E} {P : Finset (Set V)}
    (Q : Set (G.CrossEdge P)) :
    (G.liftQuotientEdgeSet Q).ncard = Q.ncard := by
  rw [liftQuotientEdgeSet_eq_image (G := G) Q]
  exact Set.ncard_image_of_injective Q Subtype.val_injective

lemma gluedTreeEdgeSet_reachable_inside_class
    {G : MultiGraph V E} {P : Finset (Set V)}
    {A : {U : Set V // U ∈ P} → Set E} {Q : Set (G.CrossEdge P)}
    (hA_tree : ∀ U : {U : Set V // U ∈ P}, G.IsSpanningTreeOn U.1 (A U))
    (U : {U : Set V // U ∈ P}) {x y : V}
    (hxU : x ∈ U.1) (hyU : y ∈ U.1) :
    ((G.edgeSubgraph (G.gluedTreeEdgeSet A Q)).induce G.vertexSet).Reachable
      (⟨x, (hA_tree U).1 hxU⟩ : G.vertexSet)
      (⟨y, (hA_tree U).1 hyU⟩ : G.vertexSet) := by
  classical
  have hconn :
      ((G.edgeSubgraph (A U)).induce U.1).Connected :=
    isSpanningTreeOn_connected_of_nonempty
      (G := G) (U := U.1) (F := A U) (hA_tree U) ⟨x, hxU⟩
  have hreachU :
      ((G.edgeSubgraph (A U)).induce U.1).Reachable
        (⟨x, hxU⟩ : U.1) (⟨y, hyU⟩ : U.1) :=
    hconn.preconnected _ _
  have hle :
      G.edgeSubgraph (A U) ≤ G.edgeSubgraph (G.gluedTreeEdgeSet A Q) := by
    intro a b hab
    rcases hab with ⟨hne, e, heA, heG, hlink⟩
    exact ⟨hne, e, mem_gluedTreeEdgeSet_internal (G := G) (A := A) (Q := Q) U heA,
      heG, hlink⟩
  have hreachLarge :
      (((G.edgeSubgraph (G.gluedTreeEdgeSet A Q)).induce U.1)).Reachable
        (⟨x, hxU⟩ : U.1) (⟨y, hyU⟩ : U.1) :=
    hreachU.mono (by
      intro a b hab
      exact hle hab)
  exact
    Diestel.Chapter02.SimpleGraph.reachable_induce_mono
      (H := G.edgeSubgraph (G.gluedTreeEdgeSet A Q))
      ((hA_tree U).1) hreachLarge

lemma gluedTreeEdgeSet_reachable_of_quotient_adj
    {G : MultiGraph V E} {P : Finset (Set V)}
    {A : {U : Set V // U ∈ P} → Set E} {Q : Set (G.CrossEdge P)}
    (hP : IsVertexPartitionOf G.vertexSet P)
    (hA_tree : ∀ U : {U : Set V // U ∈ P}, G.IsSpanningTreeOn U.1 (A U))
    {U W : {U : Set V // U ∈ P}} {x y : V}
    (hxU : x ∈ U.1) (hyW : y ∈ W.1)
    (hUW : (G.quotientEdgeSubgraph P Q).Adj U W) :
    ((G.edgeSubgraph (G.gluedTreeEdgeSet A Q)).induce G.vertexSet).Reachable
      (⟨x, (hA_tree U).1 hxU⟩ : G.vertexSet)
      (⟨y, (hA_tree W).1 hyW⟩ : G.vertexSet) := by
  rcases hUW with ⟨hne, q, hqQ, a, haU, b, hbW, hlink⟩
  have hxa :=
    gluedTreeEdgeSet_reachable_inside_class
      (G := G) (P := P) (A := A) (Q := Q) hA_tree U hxU haU
  have hAdj :
      ((G.edgeSubgraph (G.gluedTreeEdgeSet A Q)).induce G.vertexSet).Adj
        (⟨a, hlink.left_mem⟩ : G.vertexSet)
        (⟨b, hlink.right_mem⟩ : G.vertexSet) := by
    refine ⟨?_, q.1, mem_gluedTreeEdgeSet_quotient (G := G) (A := A) hqQ,
      q.2.1, hlink⟩
    intro hab
    have habv : a = b := by
      simpa using hab
    have hUW_eq : U = W := by
      apply Subtype.ext
      exact partitionClass_unique (X := G.vertexSet) (P := P)
        hP U.2 W.2 haU (by simpa [habv] using hbW)
    exact hne hUW_eq
  have hby :=
    gluedTreeEdgeSet_reachable_inside_class
      (G := G) (P := P) (A := A) (Q := Q) hA_tree W hbW hyW
  exact hxa.trans ((SimpleGraph.Adj.reachable hAdj).trans hby)

noncomputable def partitionClassRep
    {G : MultiGraph V E} {P : Finset (Set V)}
    (hP : IsVertexPartitionOf G.vertexSet P) (U : {U : Set V // U ∈ P}) : V :=
  Classical.choose (hP.1 U.1 U.2).1

lemma partitionClassRep_mem
    {G : MultiGraph V E} {P : Finset (Set V)}
    (hP : IsVertexPartitionOf G.vertexSet P) (U : {U : Set V // U ∈ P}) :
    partitionClassRep (G := G) hP U ∈ U.1 :=
  Classical.choose_spec (hP.1 U.1 U.2).1

lemma partitionClassRep_vertex_mem
    {G : MultiGraph V E} {P : Finset (Set V)}
    (hP : IsVertexPartitionOf G.vertexSet P) (U : {U : Set V // U ∈ P}) :
    partitionClassRep (G := G) hP U ∈ G.vertexSet :=
  (hP.1 U.1 U.2).2 (partitionClassRep_mem (G := G) hP U)

lemma gluedTreeEdgeSet_reachable_rep_of_quotient_adj
    {G : MultiGraph V E} {P : Finset (Set V)}
    {A : {U : Set V // U ∈ P} → Set E} {Q : Set (G.CrossEdge P)}
    (hP : IsVertexPartitionOf G.vertexSet P)
    (hA_tree : ∀ U : {U : Set V // U ∈ P}, G.IsSpanningTreeOn U.1 (A U))
    {U W : {U : Set V // U ∈ P}}
    (hUW : (G.quotientEdgeSubgraph P Q).Adj U W) :
    ((G.edgeSubgraph (G.gluedTreeEdgeSet A Q)).induce G.vertexSet).Reachable
      (⟨partitionClassRep (G := G) hP U,
        (hA_tree U).1 (partitionClassRep_mem (G := G) hP U)⟩ : G.vertexSet)
      (⟨partitionClassRep (G := G) hP W,
        (hA_tree W).1 (partitionClassRep_mem (G := G) hP W)⟩ : G.vertexSet) := by
  exact gluedTreeEdgeSet_reachable_of_quotient_adj
    (G := G) (P := P) (A := A) (Q := Q) hP hA_tree
    (partitionClassRep_mem (G := G) hP U)
    (partitionClassRep_mem (G := G) hP W) hUW

lemma gluedTreeEdgeSet_reachable_reps_of_quotient_reachable
    {G : MultiGraph V E} {P : Finset (Set V)}
    {A : {U : Set V // U ∈ P} → Set E} {Q : Set (G.CrossEdge P)}
    (hP : IsVertexPartitionOf G.vertexSet P)
    (hA_tree : ∀ U : {U : Set V // U ∈ P}, G.IsSpanningTreeOn U.1 (A U))
    {U W : {U : Set V // U ∈ P}}
    (hUW : (G.quotientEdgeSubgraph P Q).Reachable U W) :
    ((G.edgeSubgraph (G.gluedTreeEdgeSet A Q)).induce G.vertexSet).Reachable
      (⟨partitionClassRep (G := G) hP U,
        (hA_tree U).1 (partitionClassRep_mem (G := G) hP U)⟩ : G.vertexSet)
      (⟨partitionClassRep (G := G) hP W,
        (hA_tree W).1 (partitionClassRep_mem (G := G) hP W)⟩ : G.vertexSet) := by
  rcases hUW with ⟨w⟩
  induction w with
  | nil =>
      exact SimpleGraph.Reachable.refl _
  | cons hAdj _ ih =>
      exact (gluedTreeEdgeSet_reachable_rep_of_quotient_adj
        (G := G) (P := P) (A := A) (Q := Q) hP hA_tree hAdj).trans ih

lemma gluedTreeEdgeSet_connected_of_quotient_connected
    {G : MultiGraph V E} {P : Finset (Set V)}
    {A : {U : Set V // U ∈ P} → Set E} {Q : Set (G.CrossEdge P)}
    (hP : IsVertexPartitionOf G.vertexSet P)
    (hA_tree : ∀ U : {U : Set V // U ∈ P}, G.IsSpanningTreeOn U.1 (A U))
    (hQconn : (G.quotientEdgeSubgraph P Q).Connected) :
    ((G.edgeSubgraph (G.gluedTreeEdgeSet A Q)).induce G.vertexSet).Connected := by
  classical
  have hnonempty : Nonempty G.vertexSet := by
    rcases hQconn.nonempty with ⟨U⟩
    exact ⟨⟨partitionClassRep (G := G) hP U,
      partitionClassRep_vertex_mem (G := G) hP U⟩⟩
  letI : Nonempty G.vertexSet := hnonempty
  refine ⟨fun x y => ?_⟩
  rcases hP.2.2 x.1 x.2 with ⟨U, hU, hxU⟩
  rcases hP.2.2 y.1 y.2 with ⟨W, hW, hyW⟩
  let U' : {U : Set V // U ∈ P} := ⟨U, hU⟩
  let W' : {U : Set V // U ∈ P} := ⟨W, hW⟩
  have hxrep :=
    gluedTreeEdgeSet_reachable_inside_class
      (G := G) (P := P) (A := A) (Q := Q) hA_tree U' hxU
      (partitionClassRep_mem (G := G) hP U')
  have hrep :=
    gluedTreeEdgeSet_reachable_reps_of_quotient_reachable
      (G := G) (P := P) (A := A) (Q := Q) hP hA_tree
      (hQconn.preconnected U' W')
  have hrep_y :=
    gluedTreeEdgeSet_reachable_inside_class
      (G := G) (P := P) (A := A) (Q := Q) hA_tree W'
      (partitionClassRep_mem (G := G) hP W') hyW
  have hxrep' :
      ((G.edgeSubgraph (G.gluedTreeEdgeSet A Q)).induce G.vertexSet).Reachable x
        (⟨partitionClassRep (G := G) hP U',
          (hA_tree U').1 (partitionClassRep_mem (G := G) hP U')⟩ : G.vertexSet) := by
    simpa [U'] using hxrep
  have hrep_y' :
      ((G.edgeSubgraph (G.gluedTreeEdgeSet A Q)).induce G.vertexSet).Reachable
        (⟨partitionClassRep (G := G) hP W',
          (hA_tree W').1 (partitionClassRep_mem (G := G) hP W')⟩ : G.vertexSet) y := by
    simpa [W'] using hrep_y
  exact hxrep'.trans (hrep.trans hrep_y')

lemma gluedTreeEdgeSet_isSpanningTree
    {G : MultiGraph V E} [Finite V] [Finite E] {P : Finset (Set V)}
    {A : {U : Set V // U ∈ P} → Set E} {Q : Set (G.CrossEdge P)}
    (hP : IsVertexPartitionOf G.vertexSet P) (hPne : P.Nonempty)
    (hA_tree : ∀ U : {U : Set V // U ∈ P}, G.IsSpanningTreeOn U.1 (A U))
    (hQ_tree : G.IsQuotientSpanningTree P Q) :
    G.IsSpanningTree (G.gluedTreeEdgeSet A Q) := by
  classical
  let I : Set E := ⋃ U : {U : Set V // U ∈ P}, A U
  let L : Set E := G.liftQuotientEdgeSet Q
  have hpairA : Pairwise fun U W => Disjoint (A U) (A W) := by
    intro U W hUW
    rw [Set.disjoint_left]
    intro e heU heW
    have heUinside : e ∈ G.EdgeSetInside U.1 := (hA_tree U).2.2.1 heU
    have heWinside : e ∈ G.EdgeSetInside W.1 := (hA_tree W).2.2.1 heW
    exact Set.disjoint_left.mp
      (edgeSetInside_disjoint_of_ne_partitionClass
        (G := G) (P := P) hP U.2 W.2 (fun h => hUW (Subtype.ext h)))
      heUinside heWinside
  have hIcard : I.ncard = ∑ U : {U : Set V // U ∈ P}, (A U).ncard := by
    change (⋃ U : {U : Set V // U ∈ P}, A U).ncard =
      ∑ U : {U : Set V // U ∈ P}, (A U).ncard
    rw [Set.ncard_iUnion_of_finite]
    · exact finsum_eq_finset_sum_of_support_subset _ (by intro U _hU; simp)
    · intro U
      exact (hA_tree U).2.1
    · exact hpairA
  have hILdisj : Disjoint I L := by
    rw [Set.disjoint_left]
    intro e heI heL
    rcases Set.mem_iUnion.mp heI with ⟨U, heU⟩
    have heUinside : e ∈ G.EdgeSetInside U.1 := (hA_tree U).2.2.1 heU
    exact Set.disjoint_left.mp
      (liftQuotientEdgeSet_disjoint_edgeSetInside
        (G := G) (P := P) hP U.2 (Q := Q)).symm
      heUinside heL
  have hGcard :
      (G.gluedTreeEdgeSet A Q).ncard = I.ncard + L.ncard := by
    simpa [gluedTreeEdgeSet, I, L] using Set.ncard_union_eq hILdisj
  have hLcard : L.ncard = Q.ncard := by
    simpa [L] using liftQuotientEdgeSet_ncard (G := G) Q
  have hQcard : Q.ncard + 1 = P.card :=
    isQuotientSpanningTree_ncard_add_one_eq_of_partition_nonempty
      (G := G) (P := P) (Q := Q) hQ_tree hPne
  have hAcard : ∀ U : {U : Set V // U ∈ P}, (A U).ncard + 1 = U.1.ncard := by
    intro U
    exact isSpanningTreeOn_ncard_add_one_eq_of_nonempty
      (G := G) (U := U.1) (F := A U) (hA_tree U) (hP.1 U.1 U.2).1
  have hSubtypeCard : Fintype.card {U : Set V // U ∈ P} = P.card := by
    calc
      Fintype.card {U : Set V // U ∈ P} = Nat.card {U : Set V // U ∈ P} :=
        (Nat.card_eq_fintype_card).symm
      _ = P.card := partitionSubtype_natCard_eq (V := V) P
  have hsumA_add :
      (∑ U : {U : Set V // U ∈ P}, (A U).ncard) + P.card =
        G.vertexSet.ncard := by
    calc
      (∑ U : {U : Set V // U ∈ P}, (A U).ncard) + P.card =
          (∑ U : {U : Set V // U ∈ P}, (A U).ncard) +
            Fintype.card {U : Set V // U ∈ P} := by rw [hSubtypeCard]
      _ = ∑ U : {U : Set V // U ∈ P}, ((A U).ncard + 1) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ U : {U : Set V // U ∈ P}, U.1.ncard := by
        apply Finset.sum_congr rfl
        intro U _hU
        exact hAcard U
      _ = G.vertexSet.ncard :=
        isVertexPartitionOf_subtype_sum_ncard_eq (X := G.vertexSet) hP
  refine ⟨Set.toFinite _, ?_, Or.inr ?_⟩
  · exact gluedTreeEdgeSet_subset_edgeSet (G := G) (A := A) (Q := Q)
      (fun U e he => (hA_tree U).2.2.1 he |>.1)
  · constructor
    · exact gluedTreeEdgeSet_connected_of_quotient_connected
        (G := G) (P := P) (A := A) (Q := Q) hP hA_tree
        (isQuotientSpanningTree_connected_of_partition_nonempty
          (G := G) (P := P) (Q := Q) hQ_tree hPne)
    · rw [hGcard, hIcard, hLcard]
      omega

lemma gluedTreeEdgeSet_edgeDisjoint
    {G : MultiGraph V E} {P : Finset (Set V)} (hP : IsVertexPartitionOf G.vertexSet P)
    {k : ℕ} {A : {U : Set V // U ∈ P} → Fin k → Set E}
    {Q : Fin k → Set (G.CrossEdge P)}
    (hA_tree : ∀ U : {U : Set V // U ∈ P}, ∀ i : Fin k,
      G.IsSpanningTreeOn U.1 (A U i))
    (hA_disj : ∀ U : {U : Set V // U ∈ P}, EdgeDisjointFamily (A U))
    (hQ_disj : EdgeDisjointFamily Q) :
    EdgeDisjointFamily
      (fun i : Fin k => G.gluedTreeEdgeSet (fun U => A U i) (Q i)) := by
  classical
  intro i j hij
  rw [Set.disjoint_left]
  intro e hei hej
  rcases hei with heiA | heiQ <;> rcases hej with hejA | hejQ
  · rcases Set.mem_iUnion.mp heiA with ⟨U, heUi⟩
    rcases Set.mem_iUnion.mp hejA with ⟨W, heWj⟩
    by_cases hUW : U = W
    · subst W
      exact Set.disjoint_left.mp (hA_disj U hij) heUi heWj
    · have heUinside : e ∈ G.EdgeSetInside U.1 := (hA_tree U i).2.2.1 heUi
      have heWinside : e ∈ G.EdgeSetInside W.1 := (hA_tree W j).2.2.1 heWj
      exact Set.disjoint_left.mp
        (edgeSetInside_disjoint_of_ne_partitionClass
          (G := G) (P := P) hP U.2 W.2 (fun h => hUW (Subtype.ext h)))
        heUinside heWinside
  · rcases Set.mem_iUnion.mp heiA with ⟨U, heUi⟩
    have heUinside : e ∈ G.EdgeSetInside U.1 := (hA_tree U i).2.2.1 heUi
    exact Set.disjoint_left.mp
      (liftQuotientEdgeSet_disjoint_edgeSetInside
        (G := G) (P := P) hP U.2 (Q := Q j)).symm
      heUinside hejQ
  · rcases Set.mem_iUnion.mp hejA with ⟨U, heUj⟩
    have heUinside : e ∈ G.EdgeSetInside U.1 := (hA_tree U j).2.2.1 heUj
    exact Set.disjoint_left.mp
      (liftQuotientEdgeSet_disjoint_edgeSetInside
        (G := G) (P := P) hP U.2 (Q := Q i))
      heiQ heUinside
  · rcases heiQ with ⟨q, hqi, hqe⟩
    rcases hejQ with ⟨r, hrj, hre⟩
    have hqr : q = r := Subtype.ext (hqe.trans hre.symm)
    subst r
    exact Set.disjoint_left.mp (hQ_disj hij) hqi hrj

lemma packingCoveringPartition_hasKEdgeDisjointSpanningTrees_of_partition_bound
    {G : MultiGraph V E} [Finite V] [Finite E] {P : Finset (Set V)} {k : ℕ}
    (hVne : G.vertexSet.Nonempty)
    (hPack : G.PackingCoveringPartition P k)
    (hbound : k * (P.card - 1) ≤ G.crossEdgeCount P) :
    G.HasKEdgeDisjointSpanningTrees k := by
  classical
  rcases hPack with ⟨hP, hInside, hQuot⟩
  rcases hQuot with ⟨Q, hQtrees, hQcover⟩
  have hPne : P.Nonempty := by
    rcases hVne with ⟨v, hv⟩
    rcases hP.2.2 v hv with ⟨U, hU, _hvU⟩
    exact ⟨U, hU⟩
  let A : {U : Set V // U ∈ P} → Fin k → Set E :=
    fun U => Classical.choose (hInside U.1 U.2)
  have hA_tree :
      ∀ U : {U : Set V // U ∈ P}, ∀ i : Fin k,
        G.IsSpanningTreeOn U.1 (A U i) := by
    intro U
    exact (Classical.choose_spec (hInside U.1 U.2)).1
  have hA_disj :
      ∀ U : {U : Set V // U ∈ P}, EdgeDisjointFamily (A U) := by
    intro U
    exact (Classical.choose_spec (hInside U.1 U.2)).2
  have hQdisj : EdgeDisjointFamily Q :=
    quotient_cover_edgeDisjoint_of_partition_bound
      (G := G) (P := P) (k := k) hQtrees hQcover hbound
  refine ⟨fun i : Fin k => G.gluedTreeEdgeSet (fun U => A U i) (Q i), ?_, ?_⟩
  · intro i
    exact gluedTreeEdgeSet_isSpanningTree
      (G := G) (P := P) (A := fun U => A U i) (Q := Q i)
      hP hPne (fun U => hA_tree U i) (hQtrees i)
  · exact gluedTreeEdgeSet_edgeDisjoint
      (G := G) (P := P) (A := A) (Q := Q)
      hP hA_tree hA_disj hQdisj

end MultiGraph

end Chapter02
end Diestel
