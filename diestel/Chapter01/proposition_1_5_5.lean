import Chapter01.normal_tree
import Mathlib.Data.Fintype.Card

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

variable {V : Type u}

private structure RootedPartialNormalTree (G : SimpleGraph V) (r : V) where
  carrier : Set V
  tree : SimpleGraph V
  root_mem : r ∈ carrier
  le_graph : tree ≤ G
  edge_mem : ∀ ⦃x y : V⦄, tree.Adj x y → x ∈ carrier ∧ y ∈ carrier
  induced_isTree : (tree.induce carrier).IsTree
  normal :
    ∀ ⦃x y : V⦄ (hx : x ∈ carrier) (hy : y ∈ carrier)
      (p : G.Walk x y),
      p.IsPath →
        (∀ z : V, z ∈ walk_inner_vertices p → z ∉ carrier) →
          TreeComparable (tree.induce carrier)
            ⟨r, root_mem⟩ ⟨x, hx⟩ ⟨y, hy⟩

private def RootedPartialNormalTree.singleton (G : SimpleGraph V) (r : V) :
    RootedPartialNormalTree G r where
  carrier := {r}
  tree := ⊥
  root_mem := by simp
  le_graph := by intro x y h; exact h.elim
  edge_mem := by intro x y h; exact h.elim
  induced_isTree := by
    haveI : Nonempty ({r} : Set V) := ⟨⟨r, by simp⟩⟩
    haveI : Subsingleton ({r} : Set V) := Set.Subsingleton.coe_sort Set.subsingleton_singleton
    exact SimpleGraph.IsTree.of_subsingleton
  normal := by
    intro x y hx hy _p _hp _hinner
    haveI : Nonempty ({r} : Set V) := ⟨⟨r, by simp⟩⟩
    haveI : Subsingleton ({r} : Set V) := Set.Subsingleton.coe_sort Set.subsingleton_singleton
    have hT : (⊥ : SimpleGraph V).induce ({r} : Set V) |>.IsTree :=
      SimpleGraph.IsTree.of_subsingleton
    have hxy : (⟨x, hx⟩ : ({r} : Set V)) = ⟨y, hy⟩ := by
      exact Subsingleton.elim _ _
    rw [hxy]
    exact treeComparable_refl_of_isTree hT ⟨r, by simp⟩ ⟨y, hy⟩

private lemma exists_maximal_partial_normal_tree (G : SimpleGraph V) [Finite V] (r : V) :
    ∃ P : RootedPartialNormalTree G r,
      ∀ Q : RootedPartialNormalTree G r, Q.carrier.ncard ≤ P.carrier.ncard := by
  classical
  haveI : Finite (RootedPartialNormalTree G r) := by
    refine Finite.of_injective
      (fun P : RootedPartialNormalTree G r => (P.carrier, P.tree)) ?_
    intro P Q hPQ
    cases P
    cases Q
    simp only [Prod.mk.injEq] at hPQ
    rcases hPQ with ⟨rfl, rfl⟩
    rfl
  haveI : Nonempty (RootedPartialNormalTree G r) :=
    ⟨RootedPartialNormalTree.singleton G r⟩
  letI : Fintype (RootedPartialNormalTree G r) :=
    Fintype.ofFinite (RootedPartialNormalTree G r)
  obtain ⟨P, _hP, hPmax⟩ :=
    Finset.univ.exists_maximalFor
      (fun P : RootedPartialNormalTree G r => P.carrier.ncard)
      (Finset.univ_nonempty)
  refine ⟨P, ?_⟩
  intro Q
  rcases le_total Q.carrier.ncard P.carrier.ncard with hQP | hPQ
  · exact hQP
  · exact hPmax (j := Q) (by simp) hPQ

private lemma treeOrder_of_induce {T : SimpleGraph V} {S : Set V}
    {r x y : V} {hr : r ∈ S} {hx : x ∈ S} {hy : y ∈ S} :
    TreeOrder (T.induce S) ⟨r, hr⟩ ⟨x, hx⟩ ⟨y, hy⟩ →
      TreeOrder T r x y := by
  rintro ⟨p, hp, hxp⟩
  let f := (SimpleGraph.Embedding.induce (G := T) S).toHom
  refine ⟨p.map f, ?_, ?_⟩
  · exact p.map_isPath_of_injective Subtype.val_injective hp
  · have hxmap : x ∈ p.support.map f := by
      exact List.mem_map.mpr ⟨⟨x, hx⟩, hxp, rfl⟩
    change x ∈ (p.map f).support
    rw [SimpleGraph.Walk.support_map]
    exact hxmap

private lemma treeComparable_of_induce {T : SimpleGraph V} {S : Set V}
    {r x y : V} {hr : r ∈ S} {hx : x ∈ S} {hy : y ∈ S} :
    TreeComparable (T.induce S) ⟨r, hr⟩ ⟨x, hx⟩ ⟨y, hy⟩ →
      TreeComparable T r x y := by
  intro h
  rcases h with hxy | hyx
  · exact Or.inl (treeOrder_of_induce hxy)
  · exact Or.inr (treeOrder_of_induce hyx)

private lemma exists_greatest_of_finite_tree_chain {T : SimpleGraph V} {r : V}
    (hT : T.IsTree) {A : Set V} (hAfin : A.Finite) (hAnonempty : A.Nonempty)
    (hchain : ∀ ⦃x y : V⦄, x ∈ A → y ∈ A → TreeComparable T r x y) :
    ∃ m : V, m ∈ A ∧ ∀ ⦃x : V⦄, x ∈ A → TreeOrder T r x m := by
  classical
  let s : Finset V := hAfin.toFinset
  have hs : ∀ x : V, x ∈ s ↔ x ∈ A := by
    intro x
    exact hAfin.mem_toFinset
  have hs_nonempty : s.Nonempty := by
    rcases hAnonempty with ⟨x, hx⟩
    exact ⟨x, (hs x).mpr hx⟩
  have hmain :
      ∀ t : Finset V, t.Nonempty →
        (∀ ⦃x y : V⦄, x ∈ t → y ∈ t → TreeComparable T r x y) →
          ∃ m : V, m ∈ t ∧ ∀ ⦃x : V⦄, x ∈ t → TreeOrder T r x m := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro hne _hchain
      exact (Finset.not_nonempty_empty hne).elim
    · intro a t hat ih hne htchain
      by_cases htne : t.Nonempty
      · obtain ⟨m, hmt, hmmax⟩ := ih htne (by
          intro x y hx hy
          exact htchain (Finset.mem_insert.mpr (Or.inr hx))
            (Finset.mem_insert.mpr (Or.inr hy)))
        have ha_ins : a ∈ insert a t := Finset.mem_insert_self a t
        have hm_ins : m ∈ insert a t := Finset.mem_insert.mpr (Or.inr hmt)
        rcases htchain (x := a) (y := m) ha_ins hm_ins with ham | hma
        · refine ⟨m, by simp [hmt], ?_⟩
          intro x hx
          have hx' : x = a ∨ x ∈ t := by
            exact Finset.mem_insert.mp hx
          rcases hx' with rfl | hxt
          · exact ham
          · exact hmmax hxt
        · refine ⟨a, by simp, ?_⟩
          intro x hx
          have hx' : x = a ∨ x ∈ t := by
            exact Finset.mem_insert.mp hx
          rcases hx' with rfl | hxt
          · exact treeOrder_refl_of_isTree hT r x
          · exact treeOrder_trans_of_isTree hT (hmmax hxt) hma
      · have ht_empty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htne
        refine ⟨a, by simp, ?_⟩
        intro x hx
        have hx' : x = a := by
          simpa [ht_empty, hat] using hx
        subst x
        exact treeOrder_refl_of_isTree hT r a
  obtain ⟨m, hms, hmmax⟩ := hmain s hs_nonempty (by
    intro x y hx hy
    exact hchain ((hs x).mp hx) ((hs y).mp hy))
  exact ⟨m, (hs m).mp hms, fun {x} hx => hmmax ((hs x).mpr hx)⟩

private lemma normalSpanningTree_of_full_partial {G : SimpleGraph V} {r : V}
    (P : RootedPartialNormalTree G r) (hfull : P.carrier = Set.univ) :
    IsNormalSpanningTree G P.tree r := by
  classical
  refine ⟨P.le_graph, ?_, ?_⟩
  · have hInd : (P.tree.induce (Set.univ : Set V)).IsTree := by
      have h := P.induced_isTree
      rw [hfull] at h
      exact h
    exact (SimpleGraph.induceUnivIso P.tree).isTree_iff.mp hInd
  · intro x y hxy
    have hx : x ∈ P.carrier := by
      rw [hfull]
      exact Set.mem_univ x
    have hy : y ∈ P.carrier := by
      rw [hfull]
      exact Set.mem_univ y
    let p : G.Walk x y := SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil
    have hp : p.IsPath := by
      rw [SimpleGraph.Walk.cons_isPath_iff]
      exact ⟨SimpleGraph.Walk.IsPath.nil, by
        rw [SimpleGraph.Walk.mem_support_nil_iff]
        exact hxy.ne⟩
    have hinner : ∀ z : V, z ∈ walk_inner_vertices p → z ∉ P.carrier := by
      intro z hz
      simp [p, walk_inner_vertices] at hz
      rcases hz.1 with rfl | rfl
      · exact (hz.2.1 rfl).elim
      · exact (hz.2.2 rfl).elim
    have hcomp := P.normal hx hy p hp hinner
    exact treeComparable_of_induce hcomp

private lemma partial_tree_walk_support_mem {G : SimpleGraph V} {r a b : V}
    (P : RootedPartialNormalTree G r) (ha : a ∈ P.carrier)
    (p : P.tree.Walk a b) :
    ∀ z : V, z ∈ p.support → z ∈ P.carrier := by
  induction p with
  | nil =>
      intro z hz
      rw [SimpleGraph.Walk.mem_support_nil_iff] at hz
      exact hz ▸ ha
  | @cons u v w huv p ih =>
      intro z hz
      have hv : v ∈ P.carrier := (P.edge_mem huv).2
      have hz' : z = u ∨ z ∈ p.support := by
        simpa [SimpleGraph.Walk.support_cons] using hz
      rcases hz' with rfl | hz_tail
      · exact ha
      · exact ih hv z hz_tail

private lemma partial_tree_isAcyclic {G : SimpleGraph V} {r : V}
    (P : RootedPartialNormalTree G r) :
    P.tree.IsAcyclic := by
  intro v c hc
  have hc_not_nil : ¬ c.Nil := hc.not_nil
  have hv : v ∈ P.carrier := (P.edge_mem (c.adj_snd hc_not_nil)).1
  have hsupport : ∀ z : V, z ∈ c.support → z ∈ P.carrier :=
    partial_tree_walk_support_mem P hv c
  let cI : (P.tree.induce P.carrier).Walk ⟨v, hv⟩ ⟨v, hv⟩ :=
    c.induce P.carrier hsupport
  have hcI : cI.IsCycle := by
    have hmap : (cI.map (SimpleGraph.Embedding.induce P.carrier).toHom).IsCycle := by
      dsimp [cI]
      rw [SimpleGraph.Walk.map_induce]
      exact hc
    exact (SimpleGraph.Walk.map_isCycle_iff_of_injective Subtype.val_injective).mp hmap
  exact P.induced_isTree.isAcyclic cI hcI

private lemma mem_walk_inner_vertices_reverse {G : SimpleGraph V} {a b z : V}
    {p : G.Walk a b} :
    z ∈ walk_inner_vertices p.reverse ↔ z ∈ walk_inner_vertices p := by
  constructor
  · intro hz
    rcases hz with ⟨hz_support, hza, hzb⟩
    rw [SimpleGraph.Walk.support_reverse] at hz_support
    exact ⟨List.mem_reverse.mp hz_support, hzb, hza⟩
  · intro hz
    rcases hz with ⟨hz_support, hza, hzb⟩
    refine ⟨?_, hzb, hza⟩
    rw [SimpleGraph.Walk.support_reverse]
    exact List.mem_reverse.mpr hz_support

private lemma partial_tree_induce_insert_not_reachable_new {G : SimpleGraph V} {r x y : V}
    (P : RootedPartialNormalTree G r) (hx : x ∈ P.carrier) (hy : y ∉ P.carrier) :
    ¬ (P.tree.induce (insert y P.carrier)).Reachable
        ⟨x, Or.inr hx⟩ ⟨y, Or.inl rfl⟩ := by
  intro hreach
  exact hreach.elim fun p => by
    let pT : P.tree.Walk x y := p.map (SimpleGraph.Embedding.induce (insert y P.carrier)).toHom
    have hy_support : y ∈ pT.support := by
      change y ∈ (p.map (SimpleGraph.Embedding.induce (insert y P.carrier)).toHom).support
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨⟨y, Or.inl rfl⟩, p.end_mem_support, rfl⟩
    exact hy (partial_tree_walk_support_mem P hx pT y hy_support)

private lemma partial_tree_extend_induced_isAcyclic {G : SimpleGraph V} {r x y : V}
    (P : RootedPartialNormalTree G r) (hx : x ∈ P.carrier) (hy : y ∉ P.carrier) :
    ((P.tree ⊔ SimpleGraph.edge x y).induce (insert y P.carrier)).IsAcyclic := by
  classical
  let S' : Set V := insert y P.carrier
  let x' : S' := ⟨x, Or.inr hx⟩
  let y' : S' := ⟨y, Or.inl rfl⟩
  have hbase : (P.tree.induce S').IsAcyclic :=
    (partial_tree_isAcyclic P).induce S'
  have hnreach : ¬ (P.tree.induce S').Reachable x' y' :=
    partial_tree_induce_insert_not_reachable_new P hx hy
  have hacyc : (P.tree.induce S' ⊔ SimpleGraph.edge x' y').IsAcyclic :=
    hbase.sup_edge_of_not_reachable hnreach
  have hEq :
      P.tree.induce S' ⊔ SimpleGraph.edge x' y' =
        ((P.tree ⊔ SimpleGraph.edge x y).induce S') := by
    ext a b
    simp only [SimpleGraph.sup_adj, SimpleGraph.induce_adj, SimpleGraph.edge_adj]
    constructor
    · intro h
      rcases h with hT | hedge
      · exact Or.inl hT
      · rcases hedge with ⟨hcases, hne⟩
        refine Or.inr ⟨?_, ?_⟩
        · rcases hcases with hxy | hyx
          · rcases hxy with ⟨ha, hb⟩
            exact Or.inl ⟨congrArg Subtype.val ha, congrArg Subtype.val hb⟩
          · rcases hyx with ⟨ha, hb⟩
            exact Or.inr ⟨congrArg Subtype.val ha, congrArg Subtype.val hb⟩
        · intro hab
          exact hne (Subtype.ext hab)
    · intro h
      rcases h with hT | hedge
      · exact Or.inl hT
      · rcases hedge with ⟨hcases, hne⟩
        refine Or.inr ⟨?_, ?_⟩
        · rcases hcases with hxy | hyx
          · rcases hxy with ⟨ha, hb⟩
            exact Or.inl ⟨Subtype.ext ha, Subtype.ext hb⟩
          · rcases hyx with ⟨ha, hb⟩
            exact Or.inr ⟨Subtype.ext ha, Subtype.ext hb⟩
        · intro hab
          exact hne (congrArg Subtype.val hab)
  rwa [← hEq]

private lemma partial_tree_extend_induced_connected {G : SimpleGraph V} {r x y : V}
    (P : RootedPartialNormalTree G r) (hx : x ∈ P.carrier) (hy : y ∉ P.carrier) :
    ((P.tree ⊔ SimpleGraph.edge x y).induce (insert y P.carrier)).Connected := by
  classical
  let S' : Set V := insert y P.carrier
  let H' : SimpleGraph S' := (P.tree ⊔ SimpleGraph.edge x y).induce S'
  let oldToNew : (P.tree.induce P.carrier) →g H' :=
    { toFun := fun u => ⟨u.1, Or.inr u.2⟩
      map_rel' := by
        intro u v huv
        change (P.tree ⊔ SimpleGraph.edge x y).Adj u.1 v.1
        exact Or.inl huv }
  have h_old_reachable :
      ∀ ⦃u v : V⦄ (hu : u ∈ P.carrier) (hv : v ∈ P.carrier),
        H'.Reachable ⟨u, Or.inr hu⟩ ⟨v, Or.inr hv⟩ := by
    intro u v hu hv
    exact (P.induced_isTree.connected.preconnected ⟨u, hu⟩ ⟨v, hv⟩).map oldToNew
  have hyx_ne : y ≠ x := by
    intro hyx
    exact hy (hyx ▸ hx)
  have hxy_ne : x ≠ y := hyx_ne.symm
  have hyx : H'.Adj ⟨y, Or.inl rfl⟩ ⟨x, Or.inr hx⟩ := by
    change (P.tree ⊔ SimpleGraph.edge x y).Adj y x
    exact Or.inr ((SimpleGraph.edge_adj x y y x).mpr
      ⟨Or.inr ⟨rfl, rfl⟩, hyx_ne⟩)
  have hxy : H'.Adj ⟨x, Or.inr hx⟩ ⟨y, Or.inl rfl⟩ := by
    change (P.tree ⊔ SimpleGraph.edge x y).Adj x y
    exact Or.inr ((SimpleGraph.edge_adj x y x y).mpr
      ⟨Or.inl ⟨rfl, rfl⟩, hxy_ne⟩)
  refine ⟨?_⟩
  intro a b
  rcases a with ⟨a, ha'⟩
  rcases b with ⟨b, hb'⟩
  rcases ha' with rfl | ha
  · rcases hb' with rfl | hb
    · exact SimpleGraph.Reachable.rfl
    · exact (SimpleGraph.Adj.reachable hyx).trans (h_old_reachable hx hb)
  · rcases hb' with rfl | hb
    · exact (h_old_reachable ha hx).trans (SimpleGraph.Adj.reachable hxy)
    · exact h_old_reachable ha hb

private lemma partial_tree_extend_induced_isTree {G : SimpleGraph V} {r x y : V}
    (P : RootedPartialNormalTree G r) (hx : x ∈ P.carrier) (hy : y ∉ P.carrier) :
    ((P.tree ⊔ SimpleGraph.edge x y).induce (insert y P.carrier)).IsTree :=
  ⟨partial_tree_extend_induced_connected P hx hy,
    partial_tree_extend_induced_isAcyclic P hx hy⟩

private lemma treeOrder_old_to_extend {G : SimpleGraph V} {r x y a b : V}
    (P : RootedPartialNormalTree G r) (hx : x ∈ P.carrier)
    {ha : a ∈ P.carrier} {hb : b ∈ P.carrier}
    (h : TreeOrder (P.tree.induce P.carrier)
      ⟨r, P.root_mem⟩ ⟨a, ha⟩ ⟨b, hb⟩) :
    TreeOrder ((P.tree ⊔ SimpleGraph.edge x y).induce (insert y P.carrier))
      ⟨r, Or.inr P.root_mem⟩ ⟨a, Or.inr ha⟩ ⟨b, Or.inr hb⟩ := by
  classical
  let S' : Set V := insert y P.carrier
  let H' : SimpleGraph S' := (P.tree ⊔ SimpleGraph.edge x y).induce S'
  let oldToNew : (P.tree.induce P.carrier) →g H' :=
    { toFun := fun u => ⟨u.1, Or.inr u.2⟩
      map_rel' := by
        intro u v huv
        change (P.tree ⊔ SimpleGraph.edge x y).Adj u.1 v.1
        exact Or.inl huv }
  have oldToNew_inj : Function.Injective oldToNew := by
    intro u v huv
    exact Subtype.ext (congrArg (fun z : S' => (z : V)) huv)
  rcases h with ⟨p, hp, hap⟩
  refine ⟨p.map oldToNew, p.map_isPath_of_injective oldToNew_inj hp, ?_⟩
  change ⟨a, Or.inr ha⟩ ∈ (p.map oldToNew).support
  rw [SimpleGraph.Walk.support_map]
  exact List.mem_map.mpr ⟨⟨a, ha⟩, hap, rfl⟩

private lemma treeComparable_old_to_extend {G : SimpleGraph V} {r x y a b : V}
    (P : RootedPartialNormalTree G r) (hx : x ∈ P.carrier)
    {ha : a ∈ P.carrier} {hb : b ∈ P.carrier}
    (h : TreeComparable (P.tree.induce P.carrier)
      ⟨r, P.root_mem⟩ ⟨a, ha⟩ ⟨b, hb⟩) :
    TreeComparable ((P.tree ⊔ SimpleGraph.edge x y).induce (insert y P.carrier))
      ⟨r, Or.inr P.root_mem⟩ ⟨a, Or.inr ha⟩ ⟨b, Or.inr hb⟩ := by
  rcases h with h | h
  · exact Or.inl (treeOrder_old_to_extend P hx h)
  · exact Or.inr (treeOrder_old_to_extend P hx h)

private lemma treeOrder_attach_below_new_leaf {G : SimpleGraph V} {r x y : V}
    (P : RootedPartialNormalTree G r) (hx : x ∈ P.carrier) (hy : y ∉ P.carrier) :
    TreeOrder ((P.tree ⊔ SimpleGraph.edge x y).induce (insert y P.carrier))
      ⟨r, Or.inr P.root_mem⟩ ⟨x, Or.inr hx⟩ ⟨y, Or.inl rfl⟩ := by
  classical
  let S' : Set V := insert y P.carrier
  let H' : SimpleGraph S' := (P.tree ⊔ SimpleGraph.edge x y).induce S'
  let oldToNew : (P.tree.induce P.carrier) →g H' :=
    { toFun := fun u => ⟨u.1, Or.inr u.2⟩
      map_rel' := by
        intro u v huv
        change (P.tree ⊔ SimpleGraph.edge x y).Adj u.1 v.1
        exact Or.inl huv }
  have oldToNew_inj : Function.Injective oldToNew := by
    intro u v huv
    exact Subtype.ext (congrArg (fun z : S' => (z : V)) huv)
  obtain ⟨p, hp, hxp⟩ :=
    treeOrder_refl_of_isTree P.induced_isTree ⟨r, P.root_mem⟩ ⟨x, hx⟩
  let p' : H'.Walk ⟨r, Or.inr P.root_mem⟩ ⟨x, Or.inr hx⟩ := p.map oldToNew
  have hp' : p'.IsPath := p.map_isPath_of_injective oldToNew_inj hp
  have hy_not_support : ⟨y, Or.inl rfl⟩ ∉ p'.support := by
    intro hy_mem
    change ⟨y, Or.inl rfl⟩ ∈ (p.map oldToNew).support at hy_mem
    rw [SimpleGraph.Walk.support_map] at hy_mem
    rcases List.mem_map.mp hy_mem with ⟨u, _hu, hu_eq⟩
    have hyu : y = u.1 := (congrArg (fun z : S' => (z : V)) hu_eq).symm
    exact hy (hyu ▸ u.2)
  have hxy_ne : x ≠ y := by
    intro hxy
    exact hy (hxy ▸ hx)
  have hxy : H'.Adj ⟨x, Or.inr hx⟩ ⟨y, Or.inl rfl⟩ := by
    change (P.tree ⊔ SimpleGraph.edge x y).Adj x y
    exact Or.inr ((SimpleGraph.edge_adj x y x y).mpr
      ⟨Or.inl ⟨rfl, rfl⟩, hxy_ne⟩)
  refine ⟨p'.concat hxy, hp'.concat hy_not_support hxy, ?_⟩
  rw [SimpleGraph.Walk.support_concat]
  exact List.mem_append.mpr (Or.inl p'.end_mem_support)

private lemma deleted_root_component_natCard_lt (G : SimpleGraph V) [Finite V] (r : V)
    (C : (G.induce ({r}ᶜ : Set V)).ConnectedComponent) :
    Nat.card C < Nat.card V := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype C := Fintype.ofFinite C
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_lt_of_injective_of_notMem
    (fun x : C => (x.1.1 : V)) ?_ (b := r) ?_
  · intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  · rintro ⟨x, hx⟩
    have hx_ne : (x.1.1 : V) ≠ r := by
      have hx_compl : (x.1.1 : V) ∈ ({r}ᶜ : Set V) := x.1.2
      intro hxr
      exact hx_compl (by simpa [hxr])
    exact hx_ne hx

private lemma exists_root_adjacent_mem_deleted_component (G : SimpleGraph V)
    (hG : G.Connected) (r : V)
    (C : (G.induce ({r}ᶜ : Set V)).ConnectedComponent) :
    ∃ a : C, G.Adj r a.1.1 := by
  classical
  let S : Set V := {r}ᶜ
  let H : SimpleGraph S := G.induce S
  obtain ⟨c, hcC⟩ := C.nonempty_supp
  have hc_ne : (c.1 : V) ≠ r := by
    have hcS : (c.1 : V) ∈ S := c.2
    intro hcr
    exact hcS (by simp [S, hcr])
  obtain ⟨p, _hp⟩ := (hG.preconnected r c.1).exists_isPath
  obtain ⟨u, v, huv, _hu_mem, _hv_mem, hu_eq, hv_ne, q, hq⟩ :=
    exists_last_crossing_of_walk (G := G) (P := fun z => z = r) p rfl hc_ne
  subst u
  have hvS : v ∈ S := by
    simpa [S] using hv_ne
  have hqS : ∀ z : V, z ∈ q.support → z ∈ S := by
    intro z hz
    simpa [S] using hq z hz
  let qH : (G.induce S).Walk c ⟨v, hvS⟩ := q.induce S hqS
  have hvC : (⟨v, hvS⟩ : S) ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hcC ⊢
    exact (SimpleGraph.ConnectedComponent.sound qH.reachable).symm.trans hcC
  exact ⟨⟨⟨v, hvS⟩, hvC⟩, huv⟩

private lemma exists_adjacent_mem_compl_component (G : SimpleGraph V)
    (hG : G.Connected) {S : Set V} {r : V} (hrS : r ∈ S)
    (C : (G.induce (Sᶜ : Set V)).ConnectedComponent) :
    ∃ x : V, x ∈ S ∧ ∃ a : C, G.Adj x a.1.1 := by
  classical
  let H : SimpleGraph (Sᶜ : Set V) := G.induce (Sᶜ : Set V)
  obtain ⟨c, hcC⟩ := C.nonempty_supp
  have hc_notS : (c.1 : V) ∉ S := c.2
  obtain ⟨p, _hp⟩ := (hG.preconnected r c.1).exists_isPath
  obtain ⟨u, v, huv, _hu_mem, _hv_mem, huS, hv_notS, q, hq⟩ :=
    exists_last_crossing_of_walk (G := G) (P := fun z => z ∈ S) p hrS hc_notS
  have hvS : v ∈ (Sᶜ : Set V) := hv_notS
  have hqS : ∀ z : V, z ∈ q.support → z ∈ (Sᶜ : Set V) := by
    intro z hz
    exact hq z hz
  let qH : (G.induce (Sᶜ : Set V)).Walk c ⟨v, hvS⟩ := q.induce (Sᶜ : Set V) hqS
  have hvC : (⟨v, hvS⟩ : (Sᶜ : Set V)) ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hcC ⊢
    exact (SimpleGraph.ConnectedComponent.sound qH.reachable).symm.trans hcC
  exact ⟨u, huS, ⟨⟨⟨v, hvS⟩, hvC⟩, huv⟩⟩

private lemma component_neighbors_treeComparable {G : SimpleGraph V} {r : V}
    (P : RootedPartialNormalTree G r)
    (C : (G.induce (P.carrierᶜ : Set V)).ConnectedComponent)
    {x z : V} (hxS : x ∈ P.carrier) (hzS : z ∈ P.carrier)
    {a b : C} (hxa : G.Adj x a.1.1) (hzb : G.Adj z b.1.1) :
    TreeComparable (P.tree.induce P.carrier)
      ⟨r, P.root_mem⟩ ⟨x, hxS⟩ ⟨z, hzS⟩ := by
  classical
  let H : SimpleGraph (P.carrierᶜ : Set V) := G.induce (P.carrierᶜ : Set V)
  obtain ⟨qC, _hqC⟩ := (C.connected_toSimpleGraph.preconnected a b).exists_isPath
  let qH : H.Walk a.1 b.1 := qC.map C.toSimpleGraph_hom
  let incl := (SimpleGraph.Embedding.induce (G := G) (P.carrierᶜ : Set V)).toHom
  let qG : G.Walk a.1.1 b.1.1 := qH.map incl
  let tail : G.Walk a.1.1 z := qG.append (SimpleGraph.Walk.cons hzb.symm SimpleGraph.Walk.nil)
  let p0 : G.Walk x z := SimpleGraph.Walk.cons hxa tail
  have hqG_out : ∀ w : V, w ∈ qG.support → w ∉ P.carrier := by
    intro w hw
    change w ∈ (qH.map incl).support at hw
    rw [SimpleGraph.Walk.support_map] at hw
    rcases List.mem_map.mp hw with ⟨u, _hu, rfl⟩
    exact u.2
  have hp0_support :
      ∀ w : V, w ∈ p0.support → w = x ∨ w = z ∨ w ∉ P.carrier := by
    intro w hw
    have hw' : w = x ∨ w ∈ tail.support := by
      simpa [p0] using hw
    rcases hw' with rfl | hwtail
    · exact Or.inl rfl
    have htail' : w ∈ qG.support ∨ w ∈ (SimpleGraph.Walk.cons hzb.symm SimpleGraph.Walk.nil).support := by
      simpa [tail, SimpleGraph.Walk.mem_support_append_iff] using hwtail
    rcases htail' with hwq | hwlast
    · exact Or.inr (Or.inr (hqG_out w hwq))
    · have hwlast' : w = b.1.1 ∨ w = z := by
        simpa [SimpleGraph.Walk.support_cons] using hwlast
      rcases hwlast' with rfl | rfl
      · exact Or.inr (Or.inr b.1.2)
      · exact Or.inr (Or.inl rfl)
  let p : G.Walk x z := p0.toPath
  have hp : p.IsPath := SimpleGraph.Path.isPath p0.toPath
  have hinner : ∀ w : V, w ∈ walk_inner_vertices p → w ∉ P.carrier := by
    intro w hw
    have hwp0 : w ∈ p0.support := p0.support_toPath_subset hw.1
    rcases hp0_support w hwp0 with rfl | h
    · exact (hw.2.1 rfl).elim
    rcases h with rfl | hwout
    · exact (hw.2.2 rfl).elim
    · exact hwout
  exact P.normal hxS hzS p hp hinner

private lemma exists_greatest_component_neighbor {G : SimpleGraph V} {r : V} [Finite V]
    (hG : G.Connected) (P : RootedPartialNormalTree G r)
    (C : (G.induce (P.carrierᶜ : Set V)).ConnectedComponent) :
    ∃ x : V, ∃ hx : x ∈ P.carrier,
      (∃ a : C, G.Adj x a.1.1) ∧
        ∀ ⦃z : V⦄ (hz : z ∈ P.carrier),
          (∃ b : C, G.Adj z b.1.1) →
            TreeOrder (P.tree.induce P.carrier)
              ⟨r, P.root_mem⟩ ⟨z, hz⟩ ⟨x, hx⟩ := by
  classical
  let A : Set P.carrier := {x | ∃ a : C, G.Adj x.1 a.1.1}
  have hAnonempty : A.Nonempty := by
    obtain ⟨x, hxP, hxa⟩ :=
      exists_adjacent_mem_compl_component G hG P.root_mem C
    exact ⟨⟨x, hxP⟩, hxa⟩
  have hchain :
      ∀ ⦃x y : P.carrier⦄, x ∈ A → y ∈ A →
        TreeComparable (P.tree.induce P.carrier)
          ⟨r, P.root_mem⟩ x y := by
    intro x y hxA hyA
    rcases hxA with ⟨a, hxa⟩
    rcases hyA with ⟨b, hyb⟩
    exact component_neighbors_treeComparable P C x.2 y.2 hxa hyb
  obtain ⟨m, hmA, hmmax⟩ :=
    exists_greatest_of_finite_tree_chain
      (T := P.tree.induce P.carrier) (r := ⟨r, P.root_mem⟩)
      P.induced_isTree (Set.toFinite A) hAnonempty hchain
  refine ⟨m.1, m.2, hmA, ?_⟩
  intro z hz hzb
  exact hmmax (x := ⟨z, hz⟩) hzb

private lemma endpoint_neighbor_of_component_of_new_path {G : SimpleGraph V} {r y z : V}
    (P : RootedPartialNormalTree G r)
    (C : (G.induce (P.carrierᶜ : Set V)).ConnectedComponent)
    (hy : y ∉ P.carrier)
    (hyC : (⟨y, hy⟩ : (P.carrierᶜ : Set V)) ∈ C.supp)
    (hz : z ∈ P.carrier)
    (p : G.Walk y z)
    (hinner : ∀ w : V, w ∈ walk_inner_vertices p → w ∉ insert y P.carrier) :
    ∃ b : C, G.Adj z b.1.1 := by
  classical
  obtain ⟨u, v, huv, q, _s, _hp_decomp, _hu_mem, hv_mem, hu_out, hv_not_out,
      hq_out⟩ :=
    exists_first_crossing_of_walk (G := G) (P := fun w => w ∉ P.carrier)
      p hy (by exact fun hz_out => hz_out hz)
  have hv_carrier : v ∈ P.carrier := Classical.byContradiction hv_not_out
  have hv_ne_y : v ≠ y := by
    intro hvy
    exact hy (hvy ▸ hv_carrier)
  have hv_eq_z : v = z := by
    by_contra hv_ne_z
    have hv_not_insert : v ∉ insert y P.carrier :=
      hinner v ⟨hv_mem, hv_ne_y, hv_ne_z⟩
    exact hv_not_insert (Or.inr hv_carrier)
  subst v
  have hq_compl : ∀ w : V, w ∈ q.support → w ∈ (P.carrierᶜ : Set V) := by
    intro w hw
    exact hq_out w hw
  let qH : (G.induce (P.carrierᶜ : Set V)).Walk ⟨y, hy⟩ ⟨u, hu_out⟩ :=
    q.induce (P.carrierᶜ : Set V) hq_compl
  have huC : (⟨u, hu_out⟩ : (P.carrierᶜ : Set V)) ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hyC ⊢
    exact (SimpleGraph.ConnectedComponent.sound qH.reachable).symm.trans hyC
  exact ⟨⟨⟨u, hu_out⟩, huC⟩, huv.symm⟩

private def RootedPartialNormalTree.extend {G : SimpleGraph V} {r x : V}
    (P : RootedPartialNormalTree G r)
    (C : (G.induce (P.carrierᶜ : Set V)).ConnectedComponent)
    (hx : x ∈ P.carrier)
    (hx_greatest :
      ∀ ⦃z : V⦄ (hz : z ∈ P.carrier),
        (∃ b : C, G.Adj z b.1.1) →
          TreeOrder (P.tree.induce P.carrier)
            ⟨r, P.root_mem⟩ ⟨z, hz⟩ ⟨x, hx⟩)
    (a : C) (hxa : G.Adj x a.1.1) :
    RootedPartialNormalTree G r := by
  classical
  let y : V := a.1.1
  have hy : y ∉ P.carrier := a.1.2
  have hyC : (⟨y, hy⟩ : (P.carrierᶜ : Set V)) ∈ C.supp := a.2
  let T' : SimpleGraph V := P.tree ⊔ SimpleGraph.edge x y
  let S' : Set V := insert y P.carrier
  have hT' : (T'.induce S').IsTree := by
    dsimp [T', S']
    exact partial_tree_extend_induced_isTree P hx hy
  refine
    { carrier := S'
      tree := T'
      root_mem := Or.inr P.root_mem
      le_graph := ?_
      edge_mem := ?_
      induced_isTree := hT'
      normal := ?_ }
  · intro u v huv
    dsimp [T'] at huv
    rw [SimpleGraph.sup_adj] at huv
    rcases huv with huv | huv
    · exact P.le_graph huv
    · have hedge := (SimpleGraph.edge_adj x y u v).mp huv
      rcases hedge.1 with hxy | hyx
      · rcases hxy with ⟨rfl, rfl⟩
        exact hxa
      · rcases hyx with ⟨rfl, rfl⟩
        exact hxa.symm
  · intro u v huv
    dsimp [T', S'] at huv ⊢
    rw [SimpleGraph.sup_adj] at huv
    rcases huv with huv | huv
    · exact ⟨Or.inr (P.edge_mem huv).1, Or.inr (P.edge_mem huv).2⟩
    · have hedge := (SimpleGraph.edge_adj x y u v).mp huv
      rcases hedge.1 with hxy | hyx
      · rcases hxy with ⟨rfl, rfl⟩
        exact ⟨Or.inr hx, Or.inl rfl⟩
      · rcases hyx with ⟨rfl, rfl⟩
        exact ⟨Or.inl rfl, Or.inr hx⟩
  · intro u v hu hv p hp hinner
    dsimp [T', S'] at hu hv hinner ⊢
    rcases hu with rfl | hu_old
    · rcases hv with rfl | hv_old
      · exact treeComparable_refl_of_isTree hT' ⟨r, Or.inr P.root_mem⟩
          ⟨y, Or.inl rfl⟩
      · have hv_neighbor :
            ∃ b : C, G.Adj v b.1.1 :=
          endpoint_neighbor_of_component_of_new_path P C hy hyC hv_old p hinner
        have hvx_old := hx_greatest hv_old hv_neighbor
        have hvx_ext :
            TreeOrder (T'.induce S') ⟨r, Or.inr P.root_mem⟩
              ⟨v, Or.inr hv_old⟩ ⟨x, Or.inr hx⟩ := by
          dsimp [T', S']
          exact treeOrder_old_to_extend P hx hvx_old
        have hxy_ext :
            TreeOrder (T'.induce S') ⟨r, Or.inr P.root_mem⟩
              ⟨x, Or.inr hx⟩ ⟨y, Or.inl rfl⟩ := by
          dsimp [T', S']
          exact treeOrder_attach_below_new_leaf P hx hy
        exact Or.inr (treeOrder_trans_of_isTree hT' hvx_ext hxy_ext)
    · rcases hv with rfl | hv_old
      · have hinner_rev :
            ∀ w : V, w ∈ walk_inner_vertices p.reverse → w ∉ insert y P.carrier := by
          intro w hw
          exact hinner w (mem_walk_inner_vertices_reverse.mp hw)
        have hu_neighbor :
            ∃ b : C, G.Adj u b.1.1 :=
          endpoint_neighbor_of_component_of_new_path P C hy hyC hu_old p.reverse hinner_rev
        have hux_old := hx_greatest hu_old hu_neighbor
        have hux_ext :
            TreeOrder (T'.induce S') ⟨r, Or.inr P.root_mem⟩
              ⟨u, Or.inr hu_old⟩ ⟨x, Or.inr hx⟩ := by
          dsimp [T', S']
          exact treeOrder_old_to_extend P hx hux_old
        have hxy_ext :
            TreeOrder (T'.induce S') ⟨r, Or.inr P.root_mem⟩
              ⟨x, Or.inr hx⟩ ⟨y, Or.inl rfl⟩ := by
          dsimp [T', S']
          exact treeOrder_attach_below_new_leaf P hx hy
        exact Or.inl (treeOrder_trans_of_isTree hT' hux_ext hxy_ext)
      · have hinner_old :
            ∀ w : V, w ∈ walk_inner_vertices p → w ∉ P.carrier := by
          intro w hw hw_old
          exact hinner w hw (Or.inr hw_old)
        have hcomp_old := P.normal hu_old hv_old p hp hinner_old
        exact treeComparable_old_to_extend P hx hcomp_old

private lemma maximal_partial_carrier_eq_univ {G : SimpleGraph V} [Finite V]
    (hG : G.Connected) {r : V} (P : RootedPartialNormalTree G r)
    (hmax : ∀ Q : RootedPartialNormalTree G r, Q.carrier.ncard ≤ P.carrier.ncard) :
    P.carrier = Set.univ := by
  classical
  by_contra hnot_univ
  have hout : ∃ y : V, y ∉ P.carrier := by
    by_contra h
    apply hnot_univ
    ext v
    constructor
    · intro _hv
      exact Set.mem_univ v
    · intro _hv
      exact Classical.byContradiction fun hv_not => h ⟨v, hv_not⟩
  obtain ⟨y₀, hy₀⟩ := hout
  let C : (G.induce (P.carrierᶜ : Set V)).ConnectedComponent :=
    (G.induce (P.carrierᶜ : Set V)).connectedComponentMk ⟨y₀, hy₀⟩
  obtain ⟨x, hx, hx_neighbor, hx_greatest⟩ :=
    exists_greatest_component_neighbor hG P C
  obtain ⟨a, hxa⟩ := hx_neighbor
  let Q : RootedPartialNormalTree G r :=
    P.extend C hx hx_greatest a hxa
  have hle := hmax Q
  have hlt : P.carrier.ncard < Q.carrier.ncard := by
    change P.carrier.ncard < (insert a.1.1 P.carrier).ncard
    rw [Set.ncard_insert_of_notMem a.1.2 (Set.toFinite P.carrier)]
    exact Nat.lt_succ_self _
  exact (Nat.not_lt_of_ge hle) hlt

theorem proposition_1_5_5 {V : Type u} (G : SimpleGraph V) [Finite V] :
    G.Connected → ∃ T : SimpleGraph V, ∃ r : V, IsNormalSpanningTree G T r := by
  intro hG
  obtain ⟨r⟩ := hG.nonempty
  obtain ⟨P, hmax⟩ := exists_maximal_partial_normal_tree G r
  have hfull : P.carrier = Set.univ :=
    maximal_partial_carrier_eq_univ hG P hmax
  exact ⟨P.tree, r, normalSpanningTree_of_full_partial P hfull⟩

end Chapter01
end Diestel
