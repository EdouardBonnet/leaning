import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

namespace TreeShadow

/-- The simple shadow of an edge set, restricted to the ambient vertex set. -/
abbrev Shadow (G : MultiGraph V E) (F : Set E) : SimpleGraph G.vertexSet :=
  (G.edgeSubgraph F).induce G.vertexSet

noncomputable def edgeLeft {G : MultiGraph V E} (e : E) (he : e ∈ G.edgeSet) : V :=
  Classical.choose (G.exists_isLink_of_mem_edgeSet he)

noncomputable def edgeRight {G : MultiGraph V E} (e : E) (he : e ∈ G.edgeSet) : V :=
  Classical.choose (Classical.choose_spec (G.exists_isLink_of_mem_edgeSet he))

lemma edgeLeft_isLink_edgeRight {G : MultiGraph V E} (e : E) (he : e ∈ G.edgeSet) :
    G.IsLink e (edgeLeft (G := G) e he) (edgeRight (G := G) e he) :=
  Classical.choose_spec (Classical.choose_spec (G.exists_isLink_of_mem_edgeSet he))

lemma edgeLeft_mem {G : MultiGraph V E} (e : E) (he : e ∈ G.edgeSet) :
    edgeLeft (G := G) e he ∈ G.vertexSet :=
  (edgeLeft_isLink_edgeRight (G := G) e he).left_mem

lemma edgeRight_mem {G : MultiGraph V E} (e : E) (he : e ∈ G.edgeSet) :
    edgeRight (G := G) e he ∈ G.vertexSet :=
  (edgeLeft_isLink_edgeRight (G := G) e he).right_mem

/-- The unordered pair of endpoints of an edge label, as an edge candidate of the simple shadow. -/
noncomputable def edgeSym2 {G : MultiGraph V E} (e : E) (he : e ∈ G.edgeSet) :
    Sym2 G.vertexSet :=
  s(⟨edgeLeft (G := G) e he, edgeLeft_mem (G := G) e he⟩,
    ⟨edgeRight (G := G) e he, edgeRight_mem (G := G) e he⟩)

lemma edgeSym2_eq_of_isLink {G : MultiGraph V E} {e : E} (he : e ∈ G.edgeSet)
    {x y : G.vertexSet} (hlink : G.IsLink e x.1 y.1) :
    edgeSym2 (G := G) e he = s(x, y) := by
  classical
  unfold edgeSym2
  have hchosen := edgeLeft_isLink_edgeRight (G := G) e he
  rcases hchosen.eq_and_eq_or_eq_and_eq hlink with h | h
  · rcases h with ⟨hx, hy⟩
    have hx' :
        (⟨edgeLeft (G := G) e he, edgeLeft_mem (G := G) e he⟩ : G.vertexSet) = x :=
      Subtype.ext hx
    have hy' :
        (⟨edgeRight (G := G) e he, edgeRight_mem (G := G) e he⟩ : G.vertexSet) = y :=
      Subtype.ext hy
    rw [hx', hy']
  · rcases h with ⟨hx, hy⟩
    have hx' :
        (⟨edgeLeft (G := G) e he, edgeLeft_mem (G := G) e he⟩ : G.vertexSet) = y :=
      Subtype.ext hx
    have hy' :
        (⟨edgeRight (G := G) e he, edgeRight_mem (G := G) e he⟩ : G.vertexSet) = x :=
      Subtype.ext hy
    rw [hx', hy']
    exact Sym2.eq_swap

lemma edgeSym2_mem_shadow {G : MultiGraph V E} {F : Set E} {e : E}
    (heF : e ∈ F) (heG : e ∈ G.edgeSet)
    (hLoopless : ∀ x : V, ¬ G.IsLoopAt e x) :
    edgeSym2 (G := G) e heG ∈ (Shadow G F).edgeSet := by
  classical
  unfold edgeSym2
  rw [SimpleGraph.mem_edgeSet]
  change (Shadow G F).Adj
    ⟨edgeLeft (G := G) e heG, edgeLeft_mem (G := G) e heG⟩
    ⟨edgeRight (G := G) e heG, edgeRight_mem (G := G) e heG⟩
  have hlink := edgeLeft_isLink_edgeRight (G := G) e heG
  refine ⟨?_, e, heF, heG, hlink⟩
  intro h
  exact hLoopless (edgeLeft (G := G) e heG) (by
    have hval :
        edgeLeft (G := G) e heG = edgeRight (G := G) e heG :=
      by simpa using h
    change G.IsLink e (edgeLeft (G := G) e heG) (edgeLeft (G := G) e heG)
    simpa [hval] using hlink)

lemma isSpanningTree_connected_card_of_mem {G : MultiGraph V E} {F : Set E} {e : E}
    (hT : G.IsSpanningTree F) (heF : e ∈ F) :
    (Shadow G F).Connected ∧ F.ncard + 1 = G.vertexSet.ncard := by
  rcases hT with ⟨_hfin, _hsub, hempty | hconn⟩
  · exact False.elim (by
      rcases hempty with ⟨_hV, hF⟩
      exact (by simpa [hF] using heF))
  · exact hconn

lemma isSpanningTree_connected_card_of_vertex_nonempty {G : MultiGraph V E} {F : Set E}
    (hT : G.IsSpanningTree F) (hv : G.vertexSet.Nonempty) :
    (Shadow G F).Connected ∧ F.ncard + 1 = G.vertexSet.ncard := by
  rcases hT with ⟨_hfin, _hsub, hempty | hconn⟩
  · exact False.elim (by
      rcases hempty with ⟨hV, _hF⟩
      rw [hV] at hv
      exact Set.not_nonempty_empty hv)
  · exact hconn

lemma shadow_edge_exists_label {G : MultiGraph V E} {F : Set E}
    (q : (Shadow G F).edgeSet) :
    ∃ e : E, e ∈ F ∧ e ∈ G.edgeSet ∧
      ∃ x y : G.vertexSet, (q : Sym2 G.vertexSet) = s(x, y) ∧
        G.IsLink e x.1 y.1 := by
  classical
  rcases q with ⟨qval, hq⟩
  change ∃ e : E, e ∈ F ∧ e ∈ G.edgeSet ∧
      ∃ x y : G.vertexSet, qval = s(x, y) ∧ G.IsLink e x.1 y.1
  induction qval using Sym2.inductionOn with
  | hf x y =>
      have hxy : (Shadow G F).Adj x y := by
        simpa [SimpleGraph.mem_edgeSet] using hq
      rcases hxy with ⟨_hne, e, heF, heG, hlink⟩
      exact ⟨e, heF, heG, x, y, rfl, hlink⟩

noncomputable def shadowEdgeLabel {G : MultiGraph V E} {F : Set E}
    (q : (Shadow G F).edgeSet) : E :=
  Classical.choose (shadow_edge_exists_label (G := G) (F := F) q)

lemma shadowEdgeLabel_mem {G : MultiGraph V E} {F : Set E}
    (q : (Shadow G F).edgeSet) :
    shadowEdgeLabel (G := G) (F := F) q ∈ F :=
  (Classical.choose_spec (shadow_edge_exists_label (G := G) (F := F) q)).1

lemma shadowEdgeLabel_edge_mem {G : MultiGraph V E} {F : Set E}
    (q : (Shadow G F).edgeSet) :
    shadowEdgeLabel (G := G) (F := F) q ∈ G.edgeSet :=
  (Classical.choose_spec (shadow_edge_exists_label (G := G) (F := F) q)).2.1

lemma shadowEdgeLabel_spec {G : MultiGraph V E} {F : Set E}
    (q : (Shadow G F).edgeSet) :
    ∃ x y : G.vertexSet, (q : Sym2 G.vertexSet) = s(x, y) ∧
      G.IsLink (shadowEdgeLabel (G := G) (F := F) q) x.1 y.1 :=
  (Classical.choose_spec (shadow_edge_exists_label (G := G) (F := F) q)).2.2

lemma shadowEdgeLabel_injective {G : MultiGraph V E} {F : Set E} :
    Function.Injective (fun q : (Shadow G F).edgeSet =>
      (⟨shadowEdgeLabel (G := G) (F := F) q,
        shadowEdgeLabel_mem (G := G) (F := F) q⟩ : F)) := by
  classical
  intro q r hqr
  apply Subtype.ext
  obtain ⟨x, y, hqval, hqLink⟩ := shadowEdgeLabel_spec (G := G) (F := F) q
  obtain ⟨x', y', hrval, hrLink⟩ := shadowEdgeLabel_spec (G := G) (F := F) r
  have hsame :
      shadowEdgeLabel (G := G) (F := F) q =
        shadowEdgeLabel (G := G) (F := F) r := by
    exact congrArg Subtype.val hqr
  have hrLink' :
      G.IsLink (shadowEdgeLabel (G := G) (F := F) q) x'.1 y'.1 := by
    simpa [hsame] using hrLink
  rw [hqval, hrval]
  rcases hqLink.eq_and_eq_or_eq_and_eq hrLink' with h | h
  · rcases h with ⟨hxx, hyy⟩
    have hx : x = x' := Subtype.ext hxx
    have hy : y = y' := Subtype.ext hyy
    subst x'
    subst y'
    rfl
  · rcases h with ⟨hxy, hyx⟩
    have hx : x = y' := Subtype.ext hxy
    have hy : y = x' := Subtype.ext hyx
    subst y'
    subst x'
    exact Sym2.eq_swap

lemma shadow_edgeSet_natCard_le {G : MultiGraph V E} [Finite E] {F : Set E} :
    Nat.card (Shadow G F).edgeSet ≤ Nat.card F :=
  Nat.card_le_card_of_injective
    (fun q : (Shadow G F).edgeSet =>
      (⟨shadowEdgeLabel (G := G) (F := F) q,
        shadowEdgeLabel_mem (G := G) (F := F) q⟩ : F))
    (shadowEdgeLabel_injective (G := G) (F := F))

lemma natCard_subtype_eq_ncard [Finite E] (F : Set E) :
    Nat.card F = F.ncard := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  calc
    Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
    _ = F.toFinset.card := (Set.toFinset_card F).symm
    _ = F.ncard := (Set.ncard_eq_toFinset_card' F).symm

lemma shadow_edgeSet_natCard_eq_of_isSpanningTree_of_mem
    {G : MultiGraph V E} [Finite V] [Finite E] {F : Set E} {e : E}
    (hT : G.IsSpanningTree F) (heF : e ∈ F) :
    Nat.card (Shadow G F).edgeSet = F.ncard := by
  classical
  obtain ⟨hconn, hcard⟩ :=
    isSpanningTree_connected_card_of_mem (G := G) (F := F) (e := e) hT heF
  have hVcard : Nat.card G.vertexSet = G.vertexSet.ncard := by simp
  have hconnBound :
      F.ncard + 1 ≤ Nat.card (Shadow G F).edgeSet + 1 := by
    simpa [hVcard, hcard] using hconn.card_vert_le_card_edgeSet_add_one
  have hFle :
      F.ncard ≤ Nat.card (Shadow G F).edgeSet := by
    exact Nat.succ_le_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using hconnBound)
  have hleF :
      Nat.card (Shadow G F).edgeSet ≤ F.ncard := by
    simpa [natCard_subtype_eq_ncard (F := F)] using
      shadow_edgeSet_natCard_le (G := G) (F := F)
  exact le_antisymm hleF hFle

lemma shadow_isTree_of_isSpanningTree_of_mem
    {G : MultiGraph V E} [Finite V] [Finite E] {F : Set E} {e : E}
    (hT : G.IsSpanningTree F) (heF : e ∈ F) :
    (Shadow G F).IsTree := by
  classical
  obtain ⟨hconn, hcard⟩ :=
    isSpanningTree_connected_card_of_mem (G := G) (F := F) (e := e) hT heF
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  calc
    Nat.card (Shadow G F).edgeSet + 1 = F.ncard + 1 := by
      rw [shadow_edgeSet_natCard_eq_of_isSpanningTree_of_mem
        (G := G) (F := F) (e := e) hT heF]
    _ = G.vertexSet.ncard := hcard
    _ = Nat.card G.vertexSet := by simp

/--
The endpoint pair of an edge label as an actual edge of the simple shadow.
The hypotheses are separated out because later replacement arguments reuse the same map.
-/
noncomputable def edgeSym2InShadow {G : MultiGraph V E} {F : Set E}
    (hLoopless : G.Loopless) (hsub : F ⊆ G.edgeSet) :
    F → (Shadow G F).edgeSet :=
  fun e =>
    ⟨edgeSym2 (G := G) e.1 (hsub e.2),
      edgeSym2_mem_shadow (G := G) (F := F) (e := e.1) e.2 (hsub e.2)
        (fun x => hLoopless (hsub e.2) x)⟩

lemma edgeSym2InShadow_surjective {G : MultiGraph V E} {F : Set E}
    (hLoopless : G.Loopless) (hsub : F ⊆ G.edgeSet) :
    Function.Surjective (edgeSym2InShadow (G := G) (F := F) hLoopless hsub) := by
  classical
  intro q
  rcases shadow_edge_exists_label (G := G) (F := F) q with
    ⟨e, heF, _heG, x, y, hq, hlink⟩
  refine ⟨⟨e, heF⟩, Subtype.ext ?_⟩
  exact (edgeSym2_eq_of_isLink (G := G) (e := e) (hsub heF) hlink).trans hq.symm

lemma edgeSym2InShadow_injective_of_isSpanningTree_of_mem
    {G : MultiGraph V E} [Finite V] [Finite E] {F : Set E} {a : E}
    (hLoopless : G.Loopless) (hT : G.IsSpanningTree F) (haF : a ∈ F) :
    Function.Injective
      (edgeSym2InShadow (G := G) (F := F) hLoopless hT.2.1) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (Shadow G F).edgeSet := Fintype.ofFinite (Shadow G F).edgeSet
  have hsurj :
      Function.Surjective
        (edgeSym2InShadow (G := G) (F := F) hLoopless hT.2.1) :=
    edgeSym2InShadow_surjective (G := G) (F := F) hLoopless hT.2.1
  have hcard : Fintype.card F = Fintype.card (Shadow G F).edgeSet := by
    calc
      Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
      _ = F.ncard := natCard_subtype_eq_ncard (F := F)
      _ = Nat.card (Shadow G F).edgeSet :=
        (shadow_edgeSet_natCard_eq_of_isSpanningTree_of_mem
          (G := G) (F := F) (e := a) hT haF).symm
      _ = Fintype.card (Shadow G F).edgeSet := Nat.card_eq_fintype_card
  exact
    ((Fintype.bijective_iff_surjective_and_card
      (edgeSym2InShadow (G := G) (F := F) hLoopless hT.2.1)).2
        ⟨hsurj, hcard⟩).1

lemma edge_eq_of_edgeSym2_eq_of_isSpanningTree
    {G : MultiGraph V E} [Finite V] [Finite E] {F : Set E} {a e f : E}
    (hLoopless : G.Loopless) (hT : G.IsSpanningTree F) (haF : a ∈ F)
    (heF : e ∈ F) (hfF : f ∈ F)
    (heq :
      edgeSym2 (G := G) e (hT.2.1 heF) =
        edgeSym2 (G := G) f (hT.2.1 hfF)) :
    e = f := by
  classical
  have hinj :=
    edgeSym2InShadow_injective_of_isSpanningTree_of_mem
      (G := G) (F := F) (a := a) hLoopless hT haF
  have hsubtype :
      edgeSym2InShadow (G := G) (F := F) hLoopless hT.2.1 ⟨e, heF⟩ =
        edgeSym2InShadow (G := G) (F := F) hLoopless hT.2.1 ⟨f, hfF⟩ :=
    Subtype.ext heq
  exact congrArg Subtype.val (hinj hsubtype)

end TreeShadow

end MultiGraph

end Chapter02
end Diestel
