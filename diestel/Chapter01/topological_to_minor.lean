import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v

private theorem edge_out_adj {W : Type u} {X : SimpleGraph W} (e : X.edgeSet) :
    X.Adj (e : Sym2 W).out.1 (e : Sym2 W).out.2 := by
  have he : (e : Sym2 W) ∈ X.edgeSet := e.2
  rw [← (e : Sym2 W).out_eq] at he
  exact (SimpleGraph.mem_edgeSet X).mp he

private def topologicalBranchSet {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V}
    (M : TopologicalModel X G) (x : W) : Set V :=
  {z | z = M.vertexMap x ∨
    ∃ e : X.edgeSet, (e : Sym2 W).out.1 = x ∧
      z ∈ walk_inner_vertices (M.edgePath (edge_out_adj e))}

private theorem topologicalBranchSet_vertex {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V}
    (M : TopologicalModel X G) (x : W) :
    M.vertexMap x ∈ topologicalBranchSet M x := by
  exact Or.inl rfl

private theorem source_edge_eq_of_out_mk {W : Type u} {X : SimpleGraph W}
    {x y : W} (e : X.edgeSet) (he : (e : Sym2 W) = s(x, y)) :
    (e : Sym2 W).out.1 = x ∧ (e : Sym2 W).out.2 = y ∨
      (e : Sym2 W).out.1 = y ∧ (e : Sym2 W).out.2 = x := by
  have hout : s((e : Sym2 W).out.1, (e : Sym2 W).out.2) = s(x, y) := by
    rw [Sym2.mk, (e : Sym2 W).out_eq, he]
  simpa using Sym2.eq_iff.mp hout

private theorem edge_subtype_eq_of_out_mk_eq {W : Type u} {X : SimpleGraph W}
    (e f : X.edgeSet)
    (h :
      s((e : Sym2 W).out.1, (e : Sym2 W).out.2) =
        s((f : Sym2 W).out.1, (f : Sym2 W).out.2)) :
    e = f := by
  apply Subtype.ext
  rw [← (e : Sym2 W).out_eq, ← (f : Sym2 W).out_eq]
  exact h

private noncomputable def walk_induce_of_support {V : Type u} {G : SimpleGraph V}
    {S : Set V} {a b : V} (p : G.Walk a b) (ha : a ∈ S) (hb : b ∈ S)
    (hp : ∀ z : V, z ∈ p.support → z ∈ S) :
    (G.induce S).Walk ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction p with
  | nil =>
      have hEq : (⟨_, ha⟩ : S) = ⟨_, hb⟩ := Subtype.ext rfl
      simpa [hEq] using (SimpleGraph.Walk.nil : (G.induce S).Walk ⟨_, ha⟩ ⟨_, ha⟩)
  | cons hab q ih =>
      rename_i u v w
      have hv : v ∈ S := by
        apply hp v
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
      have htail :
          ∀ z : V, z ∈ q.support → z ∈ S := by
        intro z hz
        exact hp z (by simp [SimpleGraph.Walk.support_cons, hz])
      exact SimpleGraph.Walk.cons
        (show (G.induce S).Adj ⟨u, ha⟩ ⟨v, hv⟩ from hab)
        (ih hv hb htail)

private theorem prefix_support_mem_branchSet {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V}
    [DecidableEq V]
    (M : TopologicalModel X G) (x : W) (e : X.edgeSet)
    (he_left : (e : Sym2 W).out.1 = x)
    {z y : V}
    (hy_inner : y ∈ walk_inner_vertices (M.edgePath (edge_out_adj e)))
    (hz :
      z ∈
        ((M.edgePath (edge_out_adj e)).takeUntil y hy_inner.1).support) :
    z ∈ topologicalBranchSet M x := by
  classical
  let p := M.edgePath (edge_out_adj e)
  have hz_p : z ∈ p.support :=
    p.support_takeUntil_subset hy_inner.1 hz
  by_cases hz_start : z = M.vertexMap (e : Sym2 W).out.1
  · left
    simpa [he_left] using hz_start
  · right
    refine ⟨e, he_left, ?_⟩
    refine ⟨hz_p, hz_start, ?_⟩
    have hnot_end :
        M.vertexMap (e : Sym2 W).out.2 ∉
          (p.takeUntil y hy_inner.1).support :=
      SimpleGraph.Walk.endpoint_notMem_support_takeUntil
        (M.edgePath_isPath (edge_out_adj e)) hy_inner.1 hy_inner.2.2.symm
    exact fun hz_end => hnot_end (by simpa [p, hz_end] using hz)

private theorem branchSet_root_reaches {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V}
    (M : TopologicalModel X G) (x : W) {z : V}
    (hz : z ∈ topologicalBranchSet M x) :
    ∃ p : G.Walk (M.vertexMap x) z,
      ∀ y : V, y ∈ p.support → y ∈ topologicalBranchSet M x := by
  classical
  rcases hz with hz | hz
  · subst z
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro y hy
    have hyx : y = M.vertexMap x := by
      simpa [SimpleGraph.Walk.support_nil] using hy
    rw [hyx]
    exact topologicalBranchSet_vertex M x
  · rcases hz with ⟨e, he_left, hz_inner⟩
    let q := (M.edgePath (edge_out_adj e)).takeUntil z hz_inner.1
    have hstart : M.vertexMap (e : Sym2 W).out.1 = M.vertexMap x := by
      rw [he_left]
    refine ⟨q.copy hstart rfl, ?_⟩
    intro y hy
    have hyq : y ∈ q.support := by
      simpa [q, SimpleGraph.Walk.support_copy] using hy
    exact prefix_support_mem_branchSet M x e he_left hz_inner hyq

private theorem topologicalBranchSet_connected {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V}
    (M : TopologicalModel X G) (x : W) :
    (G.induce (topologicalBranchSet M x)).Connected := by
  classical
  let S := topologicalBranchSet M x
  let r : S := ⟨M.vertexMap x, topologicalBranchSet_vertex M x⟩
  letI : Nonempty S := ⟨r⟩
  refine SimpleGraph.Connected.mk ?_
  intro a b
  obtain ⟨pa, hpa⟩ := branchSet_root_reaches M x a.2
  obtain ⟨pb, hpb⟩ := branchSet_root_reaches M x b.2
  let qa : (G.induce S).Walk r a := walk_induce_of_support pa r.2 a.2 hpa
  let qb : (G.induce S).Walk r b := walk_induce_of_support pb r.2 b.2 hpb
  exact ⟨qa.reverse.append qb⟩

private theorem topologicalBranchSet_disjoint {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V}
    (M : TopologicalModel X G) :
    Pairwise fun x y : W => Disjoint (topologicalBranchSet M x) (topologicalBranchSet M y) := by
  intro x y hxy
  rw [Set.disjoint_left]
  intro z hz_x hz_y
  rcases hz_x with hz_x | hz_x
  · rcases hz_y with hz_y | hz_y
    · exact hxy (M.vertexMap.injective (hz_x.symm.trans hz_y))
    · rcases hz_y with ⟨e, _he_left, hz_inner⟩
      exact M.branch_not_inner (edge_out_adj e) (by simpa [hz_x] using hz_inner)
  · rcases hz_x with ⟨e, he_left, hz_inner⟩
    rcases hz_y with hz_y | hz_y
    · exact M.branch_not_inner (edge_out_adj e) (by simpa [hz_y] using hz_inner)
    · rcases hz_y with ⟨f, hf_left, hz_inner'⟩
      by_cases hef : e = f
      · subst f
        exact hxy (he_left.symm.trans hf_left)
      · have hne :
            s((e : Sym2 W).out.1, (e : Sym2 W).out.2) ≠
              s((f : Sym2 W).out.1, (f : Sym2 W).out.2) := by
          intro h
          exact hef (edge_subtype_eq_of_out_mk_eq e f h)
        have hdisj := M.inner_disjoint (edge_out_adj e) (edge_out_adj f) hne
        rw [Set.disjoint_left] at hdisj
        exact hdisj hz_inner hz_inner'

private theorem penultimate_mem_topologicalBranchSet {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V}
    (M : TopologicalModel X G) (e : X.edgeSet) :
    (M.edgePath (edge_out_adj e)).penultimate ∈
      topologicalBranchSet M (e : Sym2 W).out.1 := by
  let p := M.edgePath (edge_out_adj e)
  have hp_path : p.IsPath := M.edgePath_isPath (edge_out_adj e)
  have hp_non_nil : ¬ p.Nil := by
    exact SimpleGraph.Walk.not_nil_of_ne (by
      intro h
      exact (edge_out_adj e).ne (M.vertexMap.injective h))
  by_cases hstart : p.penultimate = M.vertexMap (e : Sym2 W).out.1
  · exact Or.inl hstart
  · right
    refine ⟨e, rfl, ?_⟩
    have hsupp : p.penultimate ∈ p.support := by
      exact List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hp_non_nil)
    have hend : p.penultimate ≠ M.vertexMap (e : Sym2 W).out.2 := by
      exact (p.adj_penultimate hp_non_nil).ne
    simpa [p, walk_inner_vertices] using (⟨hsupp, hstart, hend⟩ :
      p.penultimate ∈ walk_inner_vertices p)

private theorem topologicalModel_to_minor {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V}
    (M : TopologicalModel X G) : IsMinor X G := by
  classical
  refine ⟨{
    branchSet := topologicalBranchSet M
    nonempty := ?_
    pairwise_disjoint := ?_
    connected := ?_
    adjacent := ?_
  }⟩
  · intro x
    exact ⟨M.vertexMap x, topologicalBranchSet_vertex M x⟩
  · exact topologicalBranchSet_disjoint M
  · exact topologicalBranchSet_connected M
  · intro x y hxy
    let e : X.edgeSet := ⟨s(x, y), (SimpleGraph.mem_edgeSet X).mpr hxy⟩
    have he : (e : Sym2 W) = s(x, y) := rfl
    have horient := source_edge_eq_of_out_mk e he
    rcases horient with hxy_or | hyx_or
    · refine ⟨(M.edgePath (edge_out_adj e)).penultimate, ?_, M.vertexMap y, ?_, ?_⟩
      · simpa [hxy_or.1] using penultimate_mem_topologicalBranchSet M e
      · exact topologicalBranchSet_vertex M y
      · have hp_non_nil :
            ¬ (M.edgePath (edge_out_adj e)).Nil := by
          exact SimpleGraph.Walk.not_nil_of_ne (by
            intro h
            exact (edge_out_adj e).ne (M.vertexMap.injective h))
        simpa [hxy_or.2] using
          (M.edgePath (edge_out_adj e)).adj_penultimate hp_non_nil
    · refine ⟨M.vertexMap x, ?_, (M.edgePath (edge_out_adj e)).penultimate, ?_, ?_⟩
      · exact topologicalBranchSet_vertex M x
      · simpa [hyx_or.1] using penultimate_mem_topologicalBranchSet M e
      · have hp_non_nil :
            ¬ (M.edgePath (edge_out_adj e)).Nil := by
          exact SimpleGraph.Walk.not_nil_of_ne (by
            intro h
            exact (edge_out_adj e).ne (M.vertexMap.injective h))
        simpa [hyx_or.2] using
          ((M.edgePath (edge_out_adj e)).adj_penultimate hp_non_nil).symm

theorem isMinor_of_isTopologicalMinor {V : Type u} {W : Type v}
    (X : SimpleGraph W) (G : SimpleGraph V) :
    IsTopologicalMinor X G → IsMinor X G := by
  rintro ⟨M⟩
  exact topologicalModel_to_minor M

end Chapter01
end Diestel
