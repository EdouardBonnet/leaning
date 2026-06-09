import Chapter01.finite_hom_iso

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v

private lemma adj_of_path_no_inner {V : Type u} {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} (hp : p.IsPath) (hxy : x ≠ y)
    (hno_inner : ∀ z : V, z ∈ walk_inner_vertices p → False) :
    G.Adj x y := by
  cases p with
  | nil =>
      exact False.elim (hxy rfl)
  | cons h q =>
      rename_i z
      by_cases hnext : z = y
      · simpa [hnext] using h
      · exfalso
        rw [SimpleGraph.Walk.cons_isPath_iff] at hp
        have hinner :
            z ∈ walk_inner_vertices (SimpleGraph.Walk.cons h q) := by
          refine ⟨?_, ?_, hnext⟩
          · simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
          · exact h.ne.symm
        exact hno_inner _ hinner

private lemma topologicalModel_vertexMap_bijective_of_card_eq {A : Type u} {B : Type v}
    {X : SimpleGraph A} {Y : SimpleGraph B} [Finite A] [Finite B]
    (M : TopologicalModel X Y) (hcard : Nat.card A = Nat.card B) :
    Function.Bijective M.vertexMap := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  have hcardF : Fintype.card A = Fintype.card B := by
    simpa [Nat.card_eq_fintype_card] using hcard
  exact (Fintype.bijective_iff_injective_and_card (M.vertexMap : A → B)).mpr
    ⟨M.vertexMap.injective, hcardF⟩

theorem topologicalModel_map_adj_of_card_eq {A : Type u} {B : Type v}
    {X : SimpleGraph A} {Y : SimpleGraph B} [Finite A] [Finite B]
    (M : TopologicalModel X Y) (hcard : Nat.card A = Nat.card B)
    {x y : A} (hxy : X.Adj x y) :
    Y.Adj (M.vertexMap x) (M.vertexMap y) := by
  classical
  have hbij := topologicalModel_vertexMap_bijective_of_card_eq M hcard
  let p := M.edgePath hxy
  have hp : p.IsPath := M.edgePath_isPath hxy
  have hend_ne : M.vertexMap x ≠ M.vertexMap y := by
    intro h
    exact hxy.ne (M.vertexMap.injective h)
  have hno_inner : ∀ z : B, z ∈ walk_inner_vertices p → False := by
    intro z hz
    obtain ⟨a, rfl⟩ := hbij.2 z
    exact M.branch_not_inner hxy hz
  exact adj_of_path_no_inner hp hend_ne hno_inner

theorem isTopologicalMinor_antisymm_iso {A : Type u} {B : Type v}
    (X : SimpleGraph A) (Y : SimpleGraph B) [Finite A] [Finite B] :
    IsTopologicalMinor X Y → IsTopologicalMinor Y X → Nonempty (X ≃g Y) := by
  intro hXY hYX
  rcases hXY with ⟨MXY⟩
  rcases hYX with ⟨MYX⟩
  have hcardXY := isTopologicalMinor_card_le X Y ⟨MXY⟩
  have hcardYX := isTopologicalMinor_card_le Y X ⟨MYX⟩
  have hcard : Nat.card A = Nat.card B := le_antisymm hcardXY hcardYX
  exact graph_iso_of_bijective_homs X Y MXY.vertexMap MYX.vertexMap
    (topologicalModel_vertexMap_bijective_of_card_eq MXY hcard)
    (topologicalModel_vertexMap_bijective_of_card_eq MYX hcard.symm)
    (fun h => topologicalModel_map_adj_of_card_eq MXY hcard h)
    (fun h => topologicalModel_map_adj_of_card_eq MYX hcard.symm h)

end Chapter01
end Diestel
