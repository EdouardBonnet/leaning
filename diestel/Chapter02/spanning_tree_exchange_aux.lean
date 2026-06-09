import Chapter02.multigraph_tree_shadow_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

lemma exists_adj_crossing_of_walk {A : Set V} {x y : V}
    (p : G.Walk x y) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ u v : V, G.Adj u v ∧ u ∈ A ∧ v ∉ A := by
  induction p with
  | nil =>
      exact False.elim (hy hx)
  | @cons u v w h p ih =>
      by_cases hv : v ∈ A
      · exact ih hv hy
      · exact ⟨u, v, h, hx, hv⟩

lemma reachable_of_walk_of_adj_reachable {H K : SimpleGraph V} {x y : V}
    (p : K.Walk x y)
    (hAdj : ∀ ⦃u v : V⦄, K.Adj u v → H.Reachable u v) :
    H.Reachable x y := by
  induction p with
  | nil =>
      exact SimpleGraph.Reachable.refl (G := H) _
  | @cons u v w h p ih =>
      exact (hAdj h).trans ih

lemma exists_adj_not_reachable_of_walk {H K : SimpleGraph V} {x y : V}
    (p : K.Walk x y) (hnreach : ¬ H.Reachable x y) :
    ∃ u v : V, K.Adj u v ∧ ¬ H.Reachable u v := by
  by_contra hnone
  have hAdj : ∀ ⦃u v : V⦄, K.Adj u v → H.Reachable u v := by
    intro u v huv
    by_contra huvH
    exact hnone ⟨u, v, huv, huvH⟩
  exact hnreach (reachable_of_walk_of_adj_reachable p hAdj)

lemma delete_edge_endpoints_not_reachable [DecidableEq V]
    {T : SimpleGraph V} {x y : V} (hT : T.IsTree) (hxy : T.Adj x y) :
    ¬ (T.deleteEdges {s(x, y)}).Reachable x y := by
  intro hreach
  rcases hreach with ⟨q⟩
  let H := T.deleteEdges {s(x, y)}
  have hHleT : H ≤ T := by
    intro a b hab
    exact (SimpleGraph.deleteEdges_adj.mp hab).1
  let qT : T.Walk x y := q.mapLe hHleT
  let direct : T.Walk x y := SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil
  have hdirect_path : direct.IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
    simp [SimpleGraph.Walk.support_nil, hxy.ne]
  have hq_path : qT.bypass.IsPath := SimpleGraph.Walk.bypass_isPath qT
  obtain ⟨p, hp, hpuniq⟩ := hT.existsUnique_path x y
  have hdirect_eq : direct = qT.bypass := by
    exact (hpuniq direct hdirect_path).trans (hpuniq qT.bypass hq_path).symm
  have hdirect_edge : s(x, y) ∈ direct.edges := by
    simp [direct, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil]
  have hqT_edge_bypass : s(x, y) ∈ qT.bypass.edges := by
    simpa [hdirect_eq] using hdirect_edge
  have hqT_edge : s(x, y) ∈ qT.edges :=
    SimpleGraph.Walk.edges_bypass_subset qT hqT_edge_bypass
  have hq_edge : s(x, y) ∈ q.edges := by
    simpa [qT, H, SimpleGraph.Walk.edges_mapLe_eq_edges hHleT q] using hqT_edge
  have hHedge : s(x, y) ∈ H.edgeSet := q.edges_subset_edgeSet hq_edge
  have hHadj : H.Adj x y := (SimpleGraph.mem_edgeSet H).mp hHedge
  exact (SimpleGraph.deleteEdges_adj.mp hHadj).2 (by simp)

lemma IsTree.not_reachable_delete_edge_of_mem_path [DecidableEq V]
    {T : SimpleGraph V} (hT : T.IsTree) {u v a b : V}
    {p : T.Walk u v} (hp : p.IsPath) (hab : s(a, b) ∈ p.edges) :
    ¬ (T.deleteEdges {s(a, b)}).Reachable u v := by
  intro hreach
  rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk] at hreach
  rcases hreach with ⟨q, hqavoids⟩
  have hqpath : q.bypass.IsPath := SimpleGraph.Walk.bypass_isPath q
  obtain ⟨p0, _hp0, hpuniq⟩ := hT.existsUnique_path u v
  have hp_eq : p = q.bypass :=
    (hpuniq p hp).trans (hpuniq q.bypass hqpath).symm
  have hqb : s(a, b) ∈ q.bypass.edges := by
    simpa [hp_eq] using hab
  exact hqavoids (SimpleGraph.Walk.edges_bypass_subset q hqb)

lemma reachable_sup_edge_of_not_reachable_endpoints
    {H : SimpleGraph V} {x y z w : V}
    (hreach : (H ⊔ SimpleGraph.edge x y).Reachable z w)
    (hzx : ¬ H.Reachable z x) (hzy : ¬ H.Reachable z y) :
    H.Reachable z w := by
  classical
  by_contra hzw
  rcases hreach with ⟨p⟩
  let A : Set V := {t | H.Reachable z t}
  have hzA : z ∈ A := SimpleGraph.Reachable.refl (G := H) z
  have hwA : w ∉ A := hzw
  rcases exists_adj_crossing_of_walk (G := H ⊔ SimpleGraph.edge x y)
      (A := A) p hzA hwA with
    ⟨a, b, hab, haA, hbA⟩
  rw [SimpleGraph.sup_adj] at hab
  rcases hab with habH | habEdge
  · exact hbA (haA.trans habH.reachable)
  · rw [SimpleGraph.edge_adj] at habEdge
    rcases habEdge.1 with hxyab | hyxab
    · rcases hxyab with ⟨rfl, rfl⟩
      exact hzx haA
    · rcases hyxab with ⟨rfl, rfl⟩
      exact hzy haA

lemma le_delete_edge_sup_edge {T : SimpleGraph V} {x y : V} :
    T ≤ T.deleteEdges {s(x, y)} ⊔ SimpleGraph.edge x y := by
  classical
  intro a b hab
  rw [SimpleGraph.sup_adj]
  by_cases hsame : s(a, b) = s(x, y)
  · exact Or.inr ((SimpleGraph.adj_edge x y).mpr ⟨hsame.symm, hab.ne⟩)
  · exact Or.inl ((SimpleGraph.deleteEdges_adj).mpr ⟨hab, by
      simpa [Set.mem_singleton_iff] using hsame⟩)

lemma delete_edge_reachable_left_or_right
    {T : SimpleGraph V} {x y z : V} (hT : T.Connected) :
    (T.deleteEdges {s(x, y)}).Reachable z x ∨
      (T.deleteEdges {s(x, y)}).Reachable z y := by
  classical
  let H : SimpleGraph V := T.deleteEdges {s(x, y)}
  by_cases hzx : H.Reachable z x
  · exact Or.inl hzx
  · right
    by_contra hzy
    have hreachT : T.Reachable z x := hT.preconnected z x
    have hreachSup : (H ⊔ SimpleGraph.edge x y).Reachable z x := by
      simpa [H] using hreachT.mono
        (le_delete_edge_sup_edge (T := T) (x := x) (y := y))
    exact hzx
      (reachable_sup_edge_of_not_reachable_endpoints
        (H := H) (x := x) (y := y) hreachSup hzx hzy)

lemma sup_edge_connected_of_not_reachable_after_delete
    {T : SimpleGraph V} {x y u v : V} (hT : T.Connected)
    (hnot : ¬ (T.deleteEdges {s(x, y)}).Reachable u v) :
    (T.deleteEdges {s(x, y)} ⊔ SimpleGraph.edge u v).Connected := by
  classical
  let H : SimpleGraph V := T.deleteEdges {s(x, y)}
  let K : SimpleGraph V := H ⊔ SimpleGraph.edge u v
  have hHleK : H ≤ K := le_sup_left
  have huv_ne : u ≠ v := by
    intro huv
    exact hnot (huv ▸ SimpleGraph.Reachable.refl (G := H) u)
  have huvK : K.Reachable u v := by
    have huvAdj : K.Adj u v := by
      change (H ⊔ SimpleGraph.edge u v).Adj u v
      rw [SimpleGraph.sup_adj]
      exact Or.inr
        ((SimpleGraph.edge_adj u v u v).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv_ne⟩)
    exact huvAdj.reachable
  have hside_u :
      H.Reachable u x ∨ H.Reachable u y := by
    simpa [H] using
      delete_edge_reachable_left_or_right (T := T) (x := x) (y := y) (z := u) hT
  have hside_v :
      H.Reachable v x ∨ H.Reachable v y := by
    simpa [H] using
      delete_edge_reachable_left_or_right (T := T) (x := x) (y := y) (z := v) hT
  have horient :
      (H.Reachable u x ∧ H.Reachable v y) ∨
        (H.Reachable u y ∧ H.Reachable v x) := by
    rcases hside_u with hux | huy <;> rcases hside_v with hvx | hvy
    · exact False.elim (hnot (hux.trans hvx.symm))
    · exact Or.inl ⟨hux, hvy⟩
    · exact Or.inr ⟨huy, hvx⟩
    · exact False.elim (hnot (huy.trans hvy.symm))
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨u, ?_⟩
  intro z
  have hside_z :
      H.Reachable z x ∨ H.Reachable z y := by
    simpa [H] using
      delete_edge_reachable_left_or_right (T := T) (x := x) (y := y) (z := z) hT
  rcases horient with ⟨hux, hvy⟩ | ⟨huy, hvx⟩
  · rcases hside_z with hzx | hzy
    · exact (hux.mono hHleK).trans ((hzx.symm).mono hHleK)
    · exact huvK.trans ((hvy.mono hHleK).trans ((hzy.symm).mono hHleK))
  · rcases hside_z with hzx | hzy
    · exact huvK.trans ((hvx.mono hHleK).trans ((hzx.symm).mono hHleK))
    · exact (huy.mono hHleK).trans ((hzy.symm).mono hHleK)

end SimpleGraph

namespace MultiGraph

variable {V : Type u} {E : Type v}

namespace TreeShadow

lemma exists_label_not_reachable_after_delete
    {G : MultiGraph V E} [Finite V] [Finite E]
    (hLoopless : G.Loopless) {F F' : Set E} {e : E}
    (hF : G.IsSpanningTree F) (hF' : G.IsSpanningTree F')
    (heF : e ∈ F) (heF' : e ∉ F') :
    ∃ f : E, f ∈ F' ∧ f ∉ F ∧
      ∃ u v : G.vertexSet, G.IsLink f u.1 v.1 ∧
        ¬ ((Shadow G F).deleteEdges {edgeSym2 (G := G) e (hF.2.1 heF)}).Reachable u v := by
  classical
  let x : G.vertexSet :=
    ⟨edgeLeft (G := G) e (hF.2.1 heF),
      edgeLeft_mem (G := G) e (hF.2.1 heF)⟩
  let y : G.vertexSet :=
    ⟨edgeRight (G := G) e (hF.2.1 heF),
      edgeRight_mem (G := G) e (hF.2.1 heF)⟩
  let q : Sym2 G.vertexSet := edgeSym2 (G := G) e (hF.2.1 heF)
  let H : SimpleGraph G.vertexSet := (Shadow G F).deleteEdges {q}
  have hxyShadow : (Shadow G F).Adj x y := by
    have hqmem :
        q ∈ (Shadow G F).edgeSet :=
      edgeSym2_mem_shadow (G := G) (F := F) (e := e) heF (hF.2.1 heF)
        (fun z => hLoopless (hF.2.1 heF) z)
    simpa [q, x, y, edgeSym2, SimpleGraph.mem_edgeSet] using hqmem
  have hTreeF : (Shadow G F).IsTree :=
    shadow_isTree_of_isSpanningTree_of_mem (G := G) (F := F) (e := e) hF heF
  have hnotReachXY : ¬ H.Reachable x y := by
    simpa [H, q, x, y] using
      Diestel.Chapter02.SimpleGraph.delete_edge_endpoints_not_reachable
        (T := Shadow G F) hTreeF hxyShadow
  have hvNonempty : G.vertexSet.Nonempty := ⟨x.1, x.2⟩
  have hconnF' : (Shadow G F').Connected :=
    (isSpanningTree_connected_card_of_vertex_nonempty
      (G := G) (F := F') hF' hvNonempty).1
  rcases hconnF'.preconnected x y with ⟨p⟩
  rcases Diestel.Chapter02.SimpleGraph.exists_adj_not_reachable_of_walk
      (H := H) (K := Shadow G F') p hnotReachXY with
    ⟨u, v, huvF', huvNotH⟩
  rcases huvF' with ⟨_huvNe, f, hfF', hfG, hlinkf⟩
  refine ⟨f, hfF', ?_, u, v, hlinkf, huvNotH⟩
  intro hfF
  have hsf :
      edgeSym2 (G := G) f (hF.2.1 hfF) = s(u, v) :=
    edgeSym2_eq_of_isLink (G := G) (e := f) (hF.2.1 hfF) hlinkf
  by_cases hsame :
      edgeSym2 (G := G) f (hF.2.1 hfF) = q
  · have hfe : f = e :=
      edge_eq_of_edgeSym2_eq_of_isSpanningTree
        (G := G) (F := F) (a := e) (e := f) (f := e)
        hLoopless hF heF hfF heF hsame
    exact heF' (hfe ▸ hfF')
  · have hAdjF : (Shadow G F).Adj u v := by
      have hmem :
          edgeSym2 (G := G) f (hF.2.1 hfF) ∈ (Shadow G F).edgeSet :=
        edgeSym2_mem_shadow (G := G) (F := F) (e := f) hfF (hF.2.1 hfF)
          (fun z => hLoopless (hF.2.1 hfF) z)
      exact (SimpleGraph.mem_edgeSet (Shadow G F)).mp (by
        simpa [hsf] using hmem)
    have hAdjH : H.Adj u v := by
      change ((Shadow G F).deleteEdges {q}).Adj u v
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hAdjF, ?_⟩
      intro hsuv
      have hsuvq : s(u, v) = q := by
        simpa using hsuv
      exact hsame (hsf.trans hsuvq)
    exact huvNotH hAdjH.reachable

lemma delete_shadow_le_replacement_shadow
    {G : MultiGraph V E} [Finite V] [Finite E]
    (hLoopless : G.Loopless) {F : Set E} {e f : E}
    (hF : G.IsSpanningTree F) (heF : e ∈ F) :
    ((Shadow G F).deleteEdges {edgeSym2 (G := G) e (hF.2.1 heF)}) ≤
      Shadow G (insert f (F \ {e})) := by
  classical
  intro x y hxy
  have hxyF : (Shadow G F).Adj x y :=
    (SimpleGraph.deleteEdges_adj.mp hxy).1
  rcases hxyF with ⟨hxyne, g, hgF, hgG, hlinkg⟩
  have hge : g ≠ e := by
    intro h
    subst g
    have hsxy :
        s(x, y) = edgeSym2 (G := G) e (hF.2.1 heF) := by
      exact (edgeSym2_eq_of_isLink (G := G) (e := e) (hF.2.1 heF) hlinkg).symm
    exact (SimpleGraph.deleteEdges_adj.mp hxy).2 (by
      simp [hsxy])
  exact ⟨hxyne, g, by simp [hgF, hge], hgG, hlinkg⟩

lemma edge_le_replacement_shadow
    {G : MultiGraph V E} {F : Set E} {e f : E}
    {u v : G.vertexSet} (hfG : f ∈ G.edgeSet) (hfF : f ∉ F)
    (hlinkf : G.IsLink f u.1 v.1) :
    SimpleGraph.edge u v ≤ Shadow G (insert f (F \ {e})) := by
  classical
  rw [SimpleGraph.edge_le_iff]
  by_cases huv : u = v
  · exact Or.inl huv
  · have hval_ne : u.1 ≠ v.1 := by
      intro h
      exact huv (Subtype.ext h)
    exact Or.inr ⟨hval_ne, f, by simp [hfF], hfG, hlinkf⟩

lemma replacement_ncard_eq {F : Set E} {e f : E}
    (heF : e ∈ F) (hfF : f ∉ F) :
    (insert f (F \ {e})).ncard = F.ncard :=
  Set.ncard_exchange hfF heF

lemma isSpanningTree_insert_of_not_reachable_after_delete
    {G : MultiGraph V E} [Finite V] [Finite E]
    (hLoopless : G.Loopless) {F : Set E} {e f : E}
    (hF : G.IsSpanningTree F) (heF : e ∈ F)
    (hfG : f ∈ G.edgeSet) (hfF : f ∉ F)
    {u v : G.vertexSet} (hlinkf : G.IsLink f u.1 v.1)
    (hnotReach :
      ¬ ((Shadow G F).deleteEdges
          {edgeSym2 (G := G) e (hF.2.1 heF)}).Reachable u v) :
    G.IsSpanningTree (insert f (F \ {e})) := by
  classical
  let x : G.vertexSet :=
    ⟨edgeLeft (G := G) e (hF.2.1 heF),
      edgeLeft_mem (G := G) e (hF.2.1 heF)⟩
  let y : G.vertexSet :=
    ⟨edgeRight (G := G) e (hF.2.1 heF),
      edgeRight_mem (G := G) e (hF.2.1 heF)⟩
  have hnotReach' :
      ¬ ((Shadow G F).deleteEdges {s(x, y)}).Reachable u v := by
    simpa [x, y, edgeSym2] using hnotReach
  obtain ⟨hconnF, hcardF⟩ :=
    isSpanningTree_connected_card_of_mem (G := G) (F := F) (e := e) hF heF
  have hconnK :
      (((Shadow G F).deleteEdges
          {edgeSym2 (G := G) e (hF.2.1 heF)}) ⊔
        SimpleGraph.edge u v).Connected := by
    simpa [x, y, edgeSym2] using
      Diestel.Chapter02.SimpleGraph.sup_edge_connected_of_not_reachable_after_delete
        (T := Shadow G F) (x := x) (y := y) (u := u) (v := v)
        hconnF hnotReach'
  have hKle :
      (((Shadow G F).deleteEdges
          {edgeSym2 (G := G) e (hF.2.1 heF)}) ⊔
        SimpleGraph.edge u v) ≤
        Shadow G (insert f (F \ {e})) := by
    rw [sup_le_iff]
    exact ⟨delete_shadow_le_replacement_shadow
        (G := G) (F := F) (e := e) (f := f) hLoopless hF heF,
      edge_le_replacement_shadow (G := G) (F := F) (e := e) (f := f)
        hfG hfF hlinkf⟩
  have hconnReplace : (Shadow G (insert f (F \ {e}))).Connected :=
    hconnK.mono hKle
  have hfinDiff : (F \ {e}).Finite := hF.1.diff
  refine ⟨hfinDiff.insert f, ?_, ?_⟩
  · intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact hfG
    · exact hF.2.1 hg.1
  · right
    exact ⟨hconnReplace, by
      rw [replacement_ncard_eq (F := F) (e := e) (f := f) heF hfF, hcardF]⟩

lemma isSpanningTree_union_singleton_diff_of_mem_shadow_path
    {G : MultiGraph V E} [Finite V] [Finite E]
    (hLoopless : G.Loopless) {F : Set E} {e f : E}
    (hF : G.IsSpanningTree F) (heG : e ∈ G.edgeSet) (heF : e ∉ F)
    (hfF : f ∈ F) {x y : G.vertexSet} (hlinke : G.IsLink e x.1 y.1)
    {p : (Shadow G F).Walk x y} (hp : p.IsPath)
    (hfp : edgeSym2 (G := G) f (hF.2.1 hfF) ∈ p.edges) :
    G.IsSpanningTree ((F ∪ {e}) \ {f}) := by
  classical
  have hTreeF : (Shadow G F).IsTree :=
    shadow_isTree_of_isSpanningTree_of_mem
      (G := G) (F := F) (e := f) hF hfF
  have hnotReach :
      ¬ ((Shadow G F).deleteEdges
          {edgeSym2 (G := G) f (hF.2.1 hfF)}).Reachable x y :=
    Diestel.Chapter02.SimpleGraph.IsTree.not_reachable_delete_edge_of_mem_path
      (T := Shadow G F) hTreeF hp hfp
  have hInsert :
      G.IsSpanningTree (insert e (F \ {f})) :=
    isSpanningTree_insert_of_not_reachable_after_delete
      (G := G) (F := F) (e := f) (f := e)
      hLoopless hF hfF heG heF hlinke hnotReach
  have hne : e ≠ f := by
    intro hef
    exact heF (hef.symm ▸ hfF)
  have hEq : insert e F \ {f} = insert e (F \ {f}) := by
    ext g
    simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hge | hgF, hgf⟩
      · exact Or.inl hge
      · exact Or.inr ⟨hgF, hgf⟩
    · rintro (hge | ⟨hgF, hgf⟩)
      · exact ⟨Or.inl hge, by
          intro hgf
          exact hne (hge.symm.trans hgf)⟩
      · exact ⟨Or.inr hgF, hgf⟩
  simpa [hEq] using hInsert

lemma spanningTree_exchange_property
    {G : MultiGraph V E} [Finite V] [Finite E]
    (hLoopless : G.Loopless) :
    Matroid.ExchangeProperty (G.IsSpanningTree) := by
  classical
  intro F F' hF hF' e heDiff
  rcases heDiff with ⟨heF, heF'⟩
  rcases exists_label_not_reachable_after_delete
      (G := G) hLoopless hF hF' heF heF' with
    ⟨f, hfF', hfF, u, v, hlinkf, hnotReach⟩
  refine ⟨f, ⟨hfF', hfF⟩, ?_⟩
  exact isSpanningTree_insert_of_not_reachable_after_delete
    (G := G) (F := F) (e := e) (f := f) hLoopless hF heF
    (hF'.2.1 hfF') hfF hlinkf hnotReach

end TreeShadow

end MultiGraph

end Chapter02
end Diestel
