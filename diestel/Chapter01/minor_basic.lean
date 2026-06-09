import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

private lemma induced_singleton_connected {V : Type u} (G : SimpleGraph V) (x : V) :
    (G.induce ({x} : Set V)).Connected := by
  letI : Nonempty ({v : V // v ∈ ({x} : Set V)}) := ⟨⟨x, rfl⟩⟩
  refine SimpleGraph.Connected.mk ?_
  intro a b
  have ha : (a : V) = x := a.2
  have hb : (b : V) = x := b.2
  have hab : a = b := Subtype.ext (ha.trans hb.symm)
  subst hab
  exact ⟨SimpleGraph.Walk.nil⟩

private lemma direct_walk_no_inner {V : Type u} {G : SimpleGraph V} {x y : V}
    (hxy : G.Adj x y) :
    walk_inner_vertices (SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil) = ∅ := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzsup, hzx, hzy⟩
    simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hzsup
    rcases hzsup with rfl | hzsup
    · exact False.elim (hzx rfl)
    · exact False.elim (hzy hzsup)
  · intro hz
    exact False.elim hz

private lemma direct_walk_isPath {V : Type u} {G : SimpleGraph V} {x y : V}
    (hxy : G.Adj x y) :
    (SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil).IsPath := by
  rw [SimpleGraph.Walk.cons_isPath_iff]
  refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
  simp [SimpleGraph.Walk.support_nil, hxy.ne]

/-- The ordinary minor relation is reflexive. -/
theorem isMinor_refl {V : Type u} (X : SimpleGraph V) : IsMinor X X := by
  classical
  refine ⟨{
    branchSet := fun x => {x}
    nonempty := ?_
    pairwise_disjoint := ?_
    connected := ?_
    adjacent := ?_
  }⟩
  · intro x
    exact ⟨x, rfl⟩
  · intro x y hxy
    rw [Set.disjoint_singleton_left]
    exact hxy
  · intro x
    exact induced_singleton_connected X x
  · intro x y hxy
    exact ⟨x, rfl, y, rfl, hxy⟩

/-- The topological-minor relation is reflexive. -/
theorem isTopologicalMinor_refl {V : Type u} (X : SimpleGraph V) :
    IsTopologicalMinor X X := by
  classical
  refine ⟨{
    vertexMap := Function.Embedding.refl V
    edgePath := fun _ _ hxy => SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil
    edgePath_isPath := ?_
    inner_disjoint := ?_
    branch_not_inner := ?_
  }⟩
  · intro x y hxy
    exact direct_walk_isPath hxy
  · intro x y z w hxy hzw _hne
    simp [direct_walk_no_inner hxy, direct_walk_no_inner hzw, Set.disjoint_left]
  · intro x y z hxy hz
    simpa [direct_walk_no_inner hxy] using hz

end Chapter01
end Diestel
