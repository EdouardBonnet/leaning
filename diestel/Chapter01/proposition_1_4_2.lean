import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.Data.Fintype.Card

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

private def liftSet {V : Type u} (S : Set V) (B : Set S) : Set V :=
  Subtype.val '' B

private noncomputable def induce_liftSet_iso {V : Type u} (G : SimpleGraph V)
    (S : Set V) (B : Set S) :
    G.induce (liftSet S B) ≃g (G.induce S).induce B where
  toEquiv := (Equiv.Set.image (fun x : S => (x : V)) B Subtype.val_injective).symm
  map_rel_iff' := by
    intro x y
    rcases x with ⟨_, ⟨x, hxB, rfl⟩⟩
    rcases y with ⟨_, ⟨y, hyB, rfl⟩⟩
    let e := Equiv.Set.image (fun x : S => (x : V)) B Subtype.val_injective
    have hx :
        e.symm ⟨(x : V), by exact ⟨x, hxB, rfl⟩⟩ = ⟨x, hxB⟩ :=
      Equiv.Set.image_symm_apply (fun x : S => (x : V)) B Subtype.val_injective x _
    have hy :
        e.symm ⟨(y : V), by exact ⟨y, hyB, rfl⟩⟩ = ⟨y, hyB⟩ :=
      Equiv.Set.image_symm_apply (fun x : S => (x : V)) B Subtype.val_injective y _
    change G.Adj (((e.symm ⟨(x : V), by exact ⟨x, hxB, rfl⟩⟩ : B) : S) : V)
        (((e.symm ⟨(y : V), by exact ⟨y, hyB, rfl⟩⟩ : B) : S) : V) ↔
      G.Adj (x : V) (y : V)
    rw [hx, hy]

private lemma connected_of_delete_empty {V : Type u} (G : SimpleGraph V) [Finite V]
    (h : (delete_vertices G (∅ : Set V)).Connected) : G.Connected := by
  classical
  have h' : (G.induce (Set.univ : Set V)).Connected := by
    rw [delete_vertices] at h
    rw [show (∅ : Set V)ᶜ = Set.univ by ext x; simp] at h
    exact h
  exact (SimpleGraph.induceUnivIso G).connected_iff.mp h'

private lemma isKConnected_connected {V : Type u} (G : SimpleGraph V) [Finite V]
    {k : ℕ} (hk : 0 < k) (h : IsKConnected G k) : G.Connected :=
  connected_of_delete_empty G (h.2 ∅ (by simpa using hk))

private lemma liftSet_compl_singleton {V : Type u} (A : Set V) (v : A) :
    liftSet A ({v}ᶜ : Set A) = A ∩ ({(v : V)} : Set V)ᶜ := by
  ext a
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, by
      intro hv
      exact hw (Subtype.ext hv)⟩
  · rintro ⟨haA, hav⟩
    exact ⟨⟨a, haA⟩, by
      intro h
      exact hav (by simpa using congrArg Subtype.val h), rfl⟩

private lemma liftSet_compl_singleton_compl {V : Type u} (S : Set V)
    (v : (Sᶜ : Set V)) :
    liftSet (Sᶜ : Set V) ({v}ᶜ : Set (Sᶜ : Set V)) =
      (S ∪ ({(v : V)} : Set V))ᶜ := by
  rw [liftSet_compl_singleton]
  ext a
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union,
    not_or]

private lemma induced_delete_singleton_connected {V : Type u} (G : SimpleGraph V)
    [Finite V] (S : Set V) (v : (Sᶜ : Set V))
    (h : (delete_vertices G (S ∪ ({(v : V)} : Set V))).Connected) :
    (delete_vertices (G.induce (Sᶜ : Set V)) ({v} : Set (Sᶜ : Set V))).Connected := by
  classical
  have hset := liftSet_compl_singleton_compl S v
  have hleft :
      (G.induce (liftSet (Sᶜ : Set V) ({v}ᶜ : Set (Sᶜ : Set V)))).Connected := by
    rw [hset]
    simpa [delete_vertices] using h
  exact (induce_liftSet_iso G (Sᶜ : Set V) ({v}ᶜ : Set (Sᶜ : Set V))).connected_iff.mp hleft

private lemma connected_delete_edge_of_singleton_deletions_connected {V : Type u}
    (H : SimpleGraph V) [Finite V] (hcard : 2 < Nat.card V) (hconn : H.Connected)
    (hdel : ∀ v : V, (delete_vertices H ({v} : Set V)).Connected) (x y : V) :
    (H.deleteEdges {s(x, y)}).Connected := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  refine hconn.connected_delete_edge_of_not_isBridge ?_
  rw [SimpleGraph.isBridge_iff]
  rintro ⟨hxy, hnotReach⟩
  have hcardV : 2 < Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using hcard
  let Xy : ({y}ᶜ : Set V) := ⟨x, by simp [hxy.ne]⟩
  have hcompY : 1 < Fintype.card ({y}ᶜ : Set V) := by
    rw [Fintype.card_compl_set ({y} : Set V)]
    simp
    omega
  obtain ⟨Zy, hZyne⟩ := Fintype.exists_ne_of_one_lt_card hcompY Xy
  have hHy : (delete_vertices H ({y} : Set V)).Connected := hdel y
  obtain ⟨py, _hpy⟩ := hHy.exists_isPath Xy Zy
  have hXyZy : Xy ≠ Zy := hZyne.symm
  have hpy_nonNil : ¬ py.Nil := py.not_nil_of_ne hXyZy
  let z : V := (py.snd : ({y}ᶜ : Set V))
  have hxz_sub : (H.induce ({y}ᶜ : Set V)).Adj Xy py.snd := py.adj_snd hpy_nonNil
  have hxz : H.Adj x z := by
    exact hxz_sub
  have hz_ne_y : z ≠ y := by
    exact py.snd.property
  have hz_ne_x : z ≠ x := hxz.ne.symm
  let Zx : ({x}ᶜ : Set V) := ⟨z, by simp [hz_ne_x]⟩
  let Yx : ({x}ᶜ : Set V) := ⟨y, by simp [hxy.ne.symm]⟩
  have hHx : (delete_vertices H ({x} : Set V)).Connected := hdel x
  obtain ⟨qx, _hqx⟩ := hHx.exists_isPath Zx Yx
  let inclHom : H.induce ({x}ᶜ : Set V) →g H :=
    { toFun := fun v => v.1, map_rel' := by intro a b h; exact h }
  have hstart : inclHom Zx = z := rfl
  have hend : inclHom Yx = y := rfl
  let qH : H.Walk z y := (qx.map inclHom).copy hstart hend
  have hq_support : ∀ v : V, v ∈ qH.support → v ≠ x := by
    intro v hv
    change v ∈ ((qx.map inclHom).copy hstart hend).support at hv
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at hv
    rcases List.mem_map.mp hv with ⟨vx, _hvx, rfl⟩
    exact vx.property
  have hq_avoid : s(x, y) ∉ qH.edges := by
    intro he
    exact (hq_support x (qH.fst_mem_support_of_mem_edges he)) rfl
  let r : H.Walk x y := SimpleGraph.Walk.cons hxz qH
  have hhead : s(x, y) ≠ s(x, z) := by
    intro h
    rcases Sym2.eq_iff.mp h with h' | h'
    · exact hz_ne_y h'.2.symm
    · exact hxy.ne h'.2.symm
  have hr_avoid : s(x, y) ∉ r.edges := by
    intro he
    simp [r, hhead, hq_avoid] at he
  exact hnotReach ⟨r.toDeleteEdges {s(x, y)} (by
    intro e he
    simp only [Set.mem_singleton_iff]
    intro heq
    exact hr_avoid (heq ▸ he))⟩

private lemma sym2_subtype_eq_iff {V : Type u} (S : Set V) {x y : V}
    (hx : x ∈ (Sᶜ : Set V)) (hy : y ∈ (Sᶜ : Set V))
    (a b : (Sᶜ : Set V)) :
    s((a : V), (b : V)) = s(x, y) ↔ s(a, b) = s(⟨x, hx⟩, ⟨y, hy⟩) := by
  constructor
  · intro h
    rcases Sym2.eq_iff.mp h with h' | h'
    · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h'.1, Subtype.ext h'.2⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h'.1, Subtype.ext h'.2⟩)
  · intro h
    rcases Sym2.eq_iff.mp h with h' | h'
    · exact Sym2.eq_iff.mpr (Or.inl ⟨congrArg Subtype.val h'.1, congrArg Subtype.val h'.2⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨congrArg Subtype.val h'.1, congrArg Subtype.val h'.2⟩)

private lemma delete_edges_induce_eq_delete_edges_induce {V : Type u}
    (G : SimpleGraph V) (S : Set V) {x y : V}
    (hx : x ∈ (Sᶜ : Set V)) (hy : y ∈ (Sᶜ : Set V)) :
    delete_vertices (G.deleteEdges {s(x, y)}) S =
      (G.induce (Sᶜ : Set V)).deleteEdges {s(⟨x, hx⟩, ⟨y, hy⟩)} := by
  ext a b
  have hiff := sym2_subtype_eq_iff S hx hy a b
  simp [delete_vertices, SimpleGraph.deleteEdges_adj, hiff]

private lemma delete_edges_induce_eq_self_of_left_notMem {V : Type u}
    (G : SimpleGraph V) (S : Set V) {x y : V} (hx : x ∉ (Sᶜ : Set V)) :
    delete_vertices (G.deleteEdges {s(x, y)}) S = G.induce (Sᶜ : Set V) := by
  ext a b
  simp only [delete_vertices, SimpleGraph.deleteEdges_adj, SimpleGraph.induce_adj,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hGab, _⟩
    exact hGab
  · intro hGab
    refine ⟨hGab, ?_⟩
    intro heq
    have hxedge : x ∈ s((a : V), (b : V)) := by
      rw [heq]
      simp [Sym2.mem_iff]
    rcases Sym2.mem_iff.mp hxedge with hxa | hxb
    · exact hx (hxa.symm ▸ a.2)
    · exact hx (hxb.symm ▸ b.2)

private lemma delete_edges_induce_eq_self_of_right_notMem {V : Type u}
    (G : SimpleGraph V) (S : Set V) {x y : V} (hy : y ∉ (Sᶜ : Set V)) :
    delete_vertices (G.deleteEdges {s(x, y)}) S = G.induce (Sᶜ : Set V) := by
  ext a b
  simp only [delete_vertices, SimpleGraph.deleteEdges_adj, SimpleGraph.induce_adj,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hGab, _⟩
    exact hGab
  · intro hGab
    refine ⟨hGab, ?_⟩
    intro heq
    have hyedge : y ∈ s((a : V), (b : V)) := by
      rw [heq]
      simp [Sym2.mem_iff]
    rcases Sym2.mem_iff.mp hyedge with hya | hyb
    · exact hy (hya.symm ▸ a.2)
    · exact hy (hyb.symm ▸ b.2)

private lemma isKConnected_delete_edge_pred {V : Type u} (G : SimpleGraph V)
    [Finite V] {k : ℕ} (hk : k ≠ 0)
    (hG : IsKConnected G (k + 1)) (e : Sym2 V) :
    IsKConnected (G.deleteEdges {e}) k := by
  classical
  constructor
  · exact lt_trans (Nat.lt_succ_self k) hG.1
  · intro S hS
    have hSsucc : S.ncard < k + 1 := by omega
    have hconnH : (G.induce (Sᶜ : Set V)).Connected := by
      simpa [delete_vertices] using hG.2 S hSsucc
    have hcardH : 2 < Nat.card (Sᶜ : Set V) := by
      letI : Fintype V := Fintype.ofFinite V
      rw [Nat.card_eq_fintype_card]
      rw [Fintype.card_compl_set S]
      have hS_card : Fintype.card S = S.ncard := by
        simpa [Nat.card_eq_fintype_card] using (Nat.card_coe_set_eq S)
      rw [hS_card]
      have hV' : k + 1 < Fintype.card V := by
        simpa [Nat.card_eq_fintype_card] using hG.1
      omega
    have hdelH :
        ∀ v : (Sᶜ : Set V),
          (delete_vertices (G.induce (Sᶜ : Set V)) ({v} : Set (Sᶜ : Set V))).Connected := by
      intro v
      apply induced_delete_singleton_connected G S v
      apply hG.2 (S ∪ ({(v : V)} : Set V))
      have hle : (S ∪ ({(v : V)} : Set V)).ncard ≤ S.ncard + 1 := by
        simpa using Set.ncard_union_le S ({(v : V)} : Set V)
      omega
    induction e using Sym2.inductionOn with
    | hf x y =>
        by_cases hx : x ∈ (Sᶜ : Set V)
        · by_cases hy : y ∈ (Sᶜ : Set V)
          · have hdel := connected_delete_edge_of_singleton_deletions_connected
                (G.induce (Sᶜ : Set V)) hcardH hconnH hdelH ⟨x, hx⟩ ⟨y, hy⟩
            rw [delete_edges_induce_eq_delete_edges_induce G S hx hy]
            exact hdel
          · rw [delete_edges_induce_eq_self_of_right_notMem G S hy]
            exact hconnH
        · rw [delete_edges_induce_eq_self_of_left_notMem G S hx]
          exact hconnH

private lemma isEdgeConnected_of_isKConnected {V : Type u} (G : SimpleGraph V)
    [Finite V] : ∀ k : ℕ, IsKConnected G k → G.IsEdgeConnected k
  | 0, _ => SimpleGraph.IsEdgeConnected.zero
  | k + 1, hG => by
      by_cases hk : k = 0
      · subst k
        rw [SimpleGraph.isEdgeConnected_one]
        exact (isKConnected_connected G (by omega) hG).1
      · rw [SimpleGraph.isEdgeConnected_add_one hk]
        intro e
        exact isEdgeConnected_of_isKConnected (G.deleteEdges {e}) k
          (isKConnected_delete_edge_pred G hk hG e)

private lemma edge_connectivity_le_minDegree {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
    1 < Fintype.card V → edge_connectivity G ≤ G.minDegree := by
  intro hcard
  classical
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard
  haveI : Nonempty V := inferInstance
  have hcardNat : 1 < Nat.card V := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hzero : IsLEdgeConnected G 0 := ⟨hcardNat, SimpleGraph.IsEdgeConnected.zero⟩
  have hconn : IsLEdgeConnected G (edge_connectivity G) := by
    unfold edge_connectivity
    exact Nat.findGreatest_spec (Nat.zero_le _) hzero
  exact G.le_minDegree_of_forall_le_degree (edge_connectivity G) fun v =>
    SimpleGraph.IsEdgeConnected.le_degree (u := v) hconn.2

/--
Diestel, Proposition 1.4.2.
If `G` is non-trivial, then `κ(G) ≤ λ(G) ≤ δ(G)`.
-/
theorem proposition_1_4_2 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
    1 < Fintype.card V →
      vertex_connectivity G ≤ edge_connectivity G ∧ edge_connectivity G ≤ G.minDegree := by
  intro hcard
  classical
  have hcardNat : 1 < Nat.card V := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hzeroK : IsKConnected G 0 := by
    exact ⟨by omega, fun S hS => False.elim (Nat.not_lt_zero _ hS)⟩
  have hK : IsKConnected G (vertex_connectivity G) := by
    unfold vertex_connectivity
    exact Nat.findGreatest_spec (Nat.zero_le _) hzeroK
  have hEdge : G.IsEdgeConnected (vertex_connectivity G) :=
    isEdgeConnected_of_isKConnected G (vertex_connectivity G) hK
  have hLEdge : IsLEdgeConnected G (vertex_connectivity G) := ⟨hcardNat, hEdge⟩
  have hbound : vertex_connectivity G ≤ G.edgeFinset.card + 1 := by
    by_cases hκ : vertex_connectivity G = 0
    · omega
    · haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard
      obtain ⟨v⟩ := (inferInstance : Nonempty V)
      have hdeg : vertex_connectivity G ≤ G.degree v :=
        SimpleGraph.IsEdgeConnected.le_degree (u := v) hEdge
      have hedge : G.degree v ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset (v := v)
      omega
  constructor
  · unfold edge_connectivity
    exact Nat.le_findGreatest hbound hLEdge
  · exact edge_connectivity_le_minDegree G hcard

end Chapter01
end Diestel
