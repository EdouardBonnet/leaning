import Chapter01.topological_finite

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v w

noncomputable def topologicalWalkMap {A : Type u} {B : Type v}
    {Y : SimpleGraph A} {Z : SimpleGraph B} (M : TopologicalModel Y Z) :
    ∀ {a b : A}, Y.Walk a b → Z.Walk (M.vertexMap a) (M.vertexMap b) := by
  intro a b p
  induction p with
  | nil =>
      exact SimpleGraph.Walk.nil
  | cons h q ih =>
      exact (M.edgePath h).append ih

theorem topologicalWalkMap_nil {A : Type u} {B : Type v}
    {Y : SimpleGraph A} {Z : SimpleGraph B} (M : TopologicalModel Y Z) (a : A) :
    topologicalWalkMap M (SimpleGraph.Walk.nil : Y.Walk a a) =
      (SimpleGraph.Walk.nil : Z.Walk (M.vertexMap a) (M.vertexMap a)) := by
  rfl

theorem topologicalWalkMap_cons {A : Type u} {B : Type v}
    {Y : SimpleGraph A} {Z : SimpleGraph B} (M : TopologicalModel Y Z)
    {a b c : A} (h : Y.Adj a b) (q : Y.Walk b c) :
    topologicalWalkMap M (SimpleGraph.Walk.cons h q) =
      (M.edgePath h).append (topologicalWalkMap M q) := by
  rfl

theorem branch_vertex_mem_edgePath_support {A : Type u} {B : Type v}
    {Y : SimpleGraph A} {Z : SimpleGraph B} (M : TopologicalModel Y Z)
    {x y z : A} (hxy : Y.Adj x y) :
    M.vertexMap z ∈ (M.edgePath hxy).support → z = x ∨ z = y := by
  intro hz
  by_cases hx : M.vertexMap z = M.vertexMap x
  · exact Or.inl (M.vertexMap.injective hx)
  · by_cases hy : M.vertexMap z = M.vertexMap y
    · exact Or.inr (M.vertexMap.injective hy)
    · exfalso
      have hinner : M.vertexMap z ∈ walk_inner_vertices (M.edgePath hxy) :=
        ⟨hz, hx, hy⟩
      exact M.branch_not_inner hxy hinner

theorem edgePath_start_mem_support {A : Type u} {B : Type v}
    {Y : SimpleGraph A} {Z : SimpleGraph B} (M : TopologicalModel Y Z)
    {x y : A} (hxy : Y.Adj x y) :
    M.vertexMap x ∈ (M.edgePath hxy).support := by
  simpa [SimpleGraph.Walk.getVert_zero] using
    (SimpleGraph.Walk.getVert_mem_support (M.edgePath hxy) 0)

theorem edgePath_end_mem_support {A : Type u} {B : Type v}
    {Y : SimpleGraph A} {Z : SimpleGraph B} (M : TopologicalModel Y Z)
    {x y : A} (hxy : Y.Adj x y) :
    M.vertexMap y ∈ (M.edgePath hxy).support := by
  simpa [SimpleGraph.Walk.getVert_length] using
    (SimpleGraph.Walk.getVert_mem_support (M.edgePath hxy) (M.edgePath hxy).length)

theorem mem_support_topologicalWalkMap {A : Type u} {B : Type v}
    {Y : SimpleGraph A} {Z : SimpleGraph B} (M : TopologicalModel Y Z) :
    ∀ {a b : A} (p : Y.Walk a b) {z : B},
      z ∈ (topologicalWalkMap M p).support →
        (∃ y : A, y ∈ p.support ∧ z = M.vertexMap y) ∨
          ∃ x y : A, ∃ hxy : Y.Adj x y,
            s(x, y) ∈ p.edgeSet ∧ z ∈ walk_inner_vertices (M.edgePath hxy) := by
  intro a b p
  induction p with
  | nil =>
      rename_i a
      intro z hz
      left
      refine ⟨a, ?_, ?_⟩
      · simp [SimpleGraph.Walk.support_nil]
      · simpa [topologicalWalkMap_nil, SimpleGraph.Walk.support_nil] using hz
  | cons h q ih =>
      rename_i a b c
      intro z hz
      have hz' :
          z ∈ (M.edgePath h).support ∨ z ∈ (topologicalWalkMap M q).support := by
        have hz'' :
            z ∈ (M.edgePath h).support ++ (topologicalWalkMap M q).support.tail := by
          simpa [topologicalWalkMap_cons, SimpleGraph.Walk.support_append] using hz
        rcases List.mem_append.mp hz'' with hz1 | hz2
        · exact Or.inl hz1
        · exact Or.inr (List.mem_of_mem_tail hz2)
      rcases hz' with hzEdge | hzTail
      · by_cases hstart : z = M.vertexMap a
        · left
          refine ⟨a, ?_, hstart⟩
          simp [SimpleGraph.Walk.support_cons]
        · by_cases hend : z = M.vertexMap b
          · left
            refine ⟨b, ?_, hend⟩
            simp [SimpleGraph.Walk.support_cons]
          · right
            refine ⟨a, b, h, ?_, ?_⟩
            · rw [SimpleGraph.Walk.mem_edgeSet]
              simp [SimpleGraph.Walk.edges_cons]
            · exact ⟨hzEdge, hstart, hend⟩
      · rcases ih hzTail with hbranch | hinner
        · rcases hbranch with ⟨y, hy, rfl⟩
          left
          refine ⟨y, ?_, rfl⟩
          simp [SimpleGraph.Walk.support_cons, hy]
        · rcases hinner with ⟨x, y, hxy, hedge, hzin⟩
          right
          refine ⟨x, y, hxy, ?_, hzin⟩
          rw [SimpleGraph.Walk.mem_edgeSet] at hedge ⊢
          simp [SimpleGraph.Walk.edges_cons, hedge]

private theorem support_endpoint_or_inner {B : Type v} {G : SimpleGraph B}
    {a b z : B} {p : G.Walk a b} (hz : z ∈ p.support) :
    z = a ∨ z = b ∨ z ∈ walk_inner_vertices p := by
  by_cases ha : z = a
  · exact Or.inl ha
  · by_cases hb : z = b
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr ⟨hz, ha, hb⟩)

private theorem common_support_vertex_is_common_branch {A : Type u} {B : Type v}
    {X : SimpleGraph A} {Y : SimpleGraph B} (M : TopologicalModel X Y)
    {x y z w : A} (hxy : X.Adj x y) (hzw : X.Adj z w)
    (hne : s(x, y) ≠ s(z, w)) {a : B}
    (haP : a ∈ (M.edgePath hxy).support)
    (haQ : a ∈ (M.edgePath hzw).support) :
    ∃ r : A, a = M.vertexMap r ∧ (r = x ∨ r = y) ∧ (r = z ∨ r = w) := by
  have hP := support_endpoint_or_inner haP
  have hQ := support_endpoint_or_inner haQ
  rcases hP with hPx | hPy | hPinner
  · rcases hQ with hQz | hQw | hQinner
    · refine ⟨x, hPx, Or.inl rfl, Or.inl ?_⟩
      exact M.vertexMap.injective (hPx.symm.trans hQz)
    · refine ⟨x, hPx, Or.inl rfl, Or.inr ?_⟩
      exact M.vertexMap.injective (hPx.symm.trans hQw)
    · exfalso
      exact M.branch_not_inner hzw (by simpa [hPx] using hQinner)
  · rcases hQ with hQz | hQw | hQinner
    · refine ⟨y, hPy, Or.inr rfl, Or.inl ?_⟩
      exact M.vertexMap.injective (hPy.symm.trans hQz)
    · refine ⟨y, hPy, Or.inr rfl, Or.inr ?_⟩
      exact M.vertexMap.injective (hPy.symm.trans hQw)
    · exfalso
      exact M.branch_not_inner hzw (by simpa [hPy] using hQinner)
  · rcases hQ with hQz | hQw | hQinner
    · exfalso
      exact M.branch_not_inner hxy (by simpa [hQz] using hPinner)
    · exfalso
      exact M.branch_not_inner hxy (by simpa [hQw] using hPinner)
    · exfalso
      have hdisj := M.inner_disjoint hxy hzw hne
      rw [Set.disjoint_left] at hdisj
      exact hdisj hPinner hQinner

private theorem sym2_eq_of_distinct_common_endpoints {A : Type u}
    {x y a b : A} (ha : a = x ∨ a = y) (hb : b = x ∨ b = y)
    (hab : a ≠ b) :
    s(x, y) = s(a, b) := by
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · rfl
  · rcases hb with rfl | rfl
    · exact Sym2.eq_swap
    · exact False.elim (hab rfl)

theorem edgePath_edgeSet_disjoint {A : Type u} {B : Type v}
    {X : SimpleGraph A} {Y : SimpleGraph B} (M : TopologicalModel X Y)
    {x y z w : A} (hxy : X.Adj x y) (hzw : X.Adj z w)
    (hne : s(x, y) ≠ s(z, w)) :
    Disjoint (M.edgePath hxy).edgeSet (M.edgePath hzw).edgeSet := by
  rw [Set.disjoint_left]
  intro e heP heQ
  have he_repr : ∃ a b : B, e = s(a, b) := by
    simpa using
      (Sym2.exists.mp (show ∃ e' : Sym2 B, e = e' from ⟨e, rfl⟩))
  rcases he_repr with ⟨a, b, rfl⟩
  rw [SimpleGraph.Walk.mem_edgeSet] at heP heQ
  have haP : a ∈ (M.edgePath hxy).support :=
    (M.edgePath hxy).fst_mem_support_of_mem_edges heP
  have hbP : b ∈ (M.edgePath hxy).support :=
    (M.edgePath hxy).snd_mem_support_of_mem_edges heP
  have haQ : a ∈ (M.edgePath hzw).support :=
    (M.edgePath hzw).fst_mem_support_of_mem_edges heQ
  have hbQ : b ∈ (M.edgePath hzw).support :=
    (M.edgePath hzw).snd_mem_support_of_mem_edges heQ
  obtain ⟨ra, hra, hraP, hraQ⟩ :=
    common_support_vertex_is_common_branch M hxy hzw hne haP haQ
  obtain ⟨rb, hrb, hrbP, hrbQ⟩ :=
    common_support_vertex_is_common_branch M hxy hzw hne hbP hbQ
  have habY : Y.Adj a b :=
    (SimpleGraph.mem_edgeSet Y).mp ((M.edgePath hxy).edges_subset_edgeSet heP)
  have hrab : ra ≠ rb := by
    intro h
    exact habY.ne (by rw [hra, hrb, h])
  have hXY : s(x, y) = s(ra, rb) :=
    sym2_eq_of_distinct_common_endpoints hraP hrbP hrab
  have hZW : s(z, w) = s(ra, rb) :=
    sym2_eq_of_distinct_common_endpoints hraQ hrbQ hrab
  exact hne (hXY.trans hZW.symm)

theorem branch_not_inner_topologicalWalkMap_bypass {A : Type u} {B : Type v} {C : Type w}
    {X : SimpleGraph A} {Y : SimpleGraph B} {Z : SimpleGraph C}
    [DecidableEq C]
    (MXY : TopologicalModel X Y) (MYZ : TopologicalModel Y Z)
    {x y z : A} (hxy : X.Adj x y) :
    MYZ.vertexMap (MXY.vertexMap z) ∈
        walk_inner_vertices ((topologicalWalkMap MYZ (MXY.edgePath hxy)).bypass) →
      False := by
  intro hinner
  have hsupport :
      MYZ.vertexMap (MXY.vertexMap z) ∈
        (topologicalWalkMap MYZ (MXY.edgePath hxy)).support :=
    SimpleGraph.Walk.support_bypass_subset _ hinner.1
  rcases mem_support_topologicalWalkMap MYZ (MXY.edgePath hxy) hsupport with hbranch | hinnerEdge
  · rcases hbranch with ⟨y0, hy0, hzy0⟩
    have hz_y0 : MXY.vertexMap z = y0 := MYZ.vertexMap.injective hzy0
    have hz_support : MXY.vertexMap z ∈ (MXY.edgePath hxy).support := by
      rw [hz_y0]
      exact hy0
    have hy0xy := branch_vertex_mem_edgePath_support MXY hxy hz_support
    rcases hy0xy with rfl | rfl
    · exact hinner.2.1 rfl
    · exact hinner.2.2 rfl
  · rcases hinnerEdge with ⟨u, v, huv, hedge, hzinner⟩
    exact MYZ.branch_not_inner huv hzinner

theorem source_inner_of_branch_inner_topologicalWalkMap_bypass
    {A : Type u} {B : Type v} {C : Type w}
    {X : SimpleGraph A} {Y : SimpleGraph B} {Z : SimpleGraph C}
    [DecidableEq C]
    (MXY : TopologicalModel X Y) (MYZ : TopologicalModel Y Z)
    {x y : A} (hxy : X.Adj x y) {b : B}
    (hb_support : b ∈ (MXY.edgePath hxy).support)
    (hb_inner :
      MYZ.vertexMap b ∈
        walk_inner_vertices ((topologicalWalkMap MYZ (MXY.edgePath hxy)).bypass)) :
    b ∈ walk_inner_vertices (MXY.edgePath hxy) := by
  refine ⟨hb_support, ?_, ?_⟩
  · intro hb
    exact hb_inner.2.1 (by rw [hb])
  · intro hb
    exact hb_inner.2.2 (by rw [hb])

theorem inner_disjoint_topologicalWalkMap_bypass
    {A : Type u} {B : Type v} {C : Type w}
    {X : SimpleGraph A} {Y : SimpleGraph B} {Z : SimpleGraph C}
    [DecidableEq C]
    (MXY : TopologicalModel X Y) (MYZ : TopologicalModel Y Z)
    {x y z w : A} (hxy : X.Adj x y) (hzw : X.Adj z w)
    (hne : s(x, y) ≠ s(z, w)) :
    Disjoint
      (walk_inner_vertices ((topologicalWalkMap MYZ (MXY.edgePath hxy)).bypass))
      (walk_inner_vertices ((topologicalWalkMap MYZ (MXY.edgePath hzw)).bypass)) := by
  rw [Set.disjoint_left]
  intro r hrP hrQ
  have hrP_support :
      r ∈ (topologicalWalkMap MYZ (MXY.edgePath hxy)).support :=
    SimpleGraph.Walk.support_bypass_subset _ hrP.1
  have hrQ_support :
      r ∈ (topologicalWalkMap MYZ (MXY.edgePath hzw)).support :=
    SimpleGraph.Walk.support_bypass_subset _ hrQ.1
  rcases mem_support_topologicalWalkMap MYZ (MXY.edgePath hxy) hrP_support with
    hPbranch | hPinnerEdge
  · rcases hPbranch with ⟨a, ha_support, hra⟩
    rcases mem_support_topologicalWalkMap MYZ (MXY.edgePath hzw) hrQ_support with
      hQbranch | hQinnerEdge
    · rcases hQbranch with ⟨b, hb_support, hrb⟩
      have hab : a = b := MYZ.vertexMap.injective (hra.symm.trans hrb)
      subst b
      have ha_inner_P :
          a ∈ walk_inner_vertices (MXY.edgePath hxy) :=
        source_inner_of_branch_inner_topologicalWalkMap_bypass MXY MYZ hxy ha_support
          (by simpa [hra] using hrP)
      have ha_inner_Q :
          a ∈ walk_inner_vertices (MXY.edgePath hzw) :=
        source_inner_of_branch_inner_topologicalWalkMap_bypass MXY MYZ hzw hb_support
          (by simpa [hra] using hrQ)
      have hdisj := MXY.inner_disjoint hxy hzw hne
      rw [Set.disjoint_left] at hdisj
      exact hdisj ha_inner_P ha_inner_Q
    · rcases hQinnerEdge with ⟨b, c, hbc, _hbc_edge, hr_inner⟩
      exact MYZ.branch_not_inner hbc (by simpa [hra] using hr_inner)
  · rcases hPinnerEdge with ⟨a, b, hab, hab_edge, hr_inner_P⟩
    rcases mem_support_topologicalWalkMap MYZ (MXY.edgePath hzw) hrQ_support with
      hQbranch | hQinnerEdge
    · rcases hQbranch with ⟨c, _hc_support, hrc⟩
      exact MYZ.branch_not_inner hab (by simpa [hrc] using hr_inner_P)
    · rcases hQinnerEdge with ⟨c, d, hcd, hcd_edge, hr_inner_Q⟩
      by_cases hedges : s(a, b) = s(c, d)
      · have hsource_disj := edgePath_edgeSet_disjoint MXY hxy hzw hne
        rw [Set.disjoint_left] at hsource_disj
        exact hsource_disj hab_edge (by simpa [hedges] using hcd_edge)
      · have htarget_disj := MYZ.inner_disjoint hab hcd hedges
        rw [Set.disjoint_left] at htarget_disj
        exact htarget_disj hr_inner_P hr_inner_Q

noncomputable def composedTopologicalModel
    {A : Type u} {B : Type v} {C : Type w}
    {X : SimpleGraph A} {Y : SimpleGraph B} {Z : SimpleGraph C}
    [DecidableEq C]
    (MXY : TopologicalModel X Y) (MYZ : TopologicalModel Y Z) :
    TopologicalModel X Z where
  vertexMap := MXY.vertexMap.trans MYZ.vertexMap
  edgePath := fun _ _ hxy => (topologicalWalkMap MYZ (MXY.edgePath hxy)).bypass
  edgePath_isPath := fun _ _ hxy => SimpleGraph.Walk.bypass_isPath _
  inner_disjoint := fun _ _ _ _ hxy hzw hne =>
    inner_disjoint_topologicalWalkMap_bypass MXY MYZ hxy hzw hne
  branch_not_inner := fun _ _ _ hxy hz =>
    branch_not_inner_topologicalWalkMap_bypass MXY MYZ hxy hz

theorem isTopologicalMinor_trans {A : Type u} {B : Type v} {C : Type w}
    (X : SimpleGraph A) (Y : SimpleGraph B) (Z : SimpleGraph C) :
    IsTopologicalMinor X Y → IsTopologicalMinor Y Z → IsTopologicalMinor X Z := by
  classical
  rintro ⟨MXY⟩ ⟨MYZ⟩
  exact ⟨composedTopologicalModel MXY MYZ⟩

end Chapter01
end Diestel
