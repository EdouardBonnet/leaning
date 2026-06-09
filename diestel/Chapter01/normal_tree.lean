import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

variable {V : Type u}
variable {G T : SimpleGraph V} {r x y z : V}

lemma exists_first_crossing_of_walk {P : V → Prop}
    {a b : V} (p : G.Walk a b) (ha : P a) (hb : ¬ P b) :
    ∃ u v : V, ∃ huv : G.Adj u v, ∃ q : G.Walk a u, ∃ s : G.Walk v b,
      p = q.append (SimpleGraph.Walk.cons huv s) ∧
        u ∈ p.support ∧ v ∈ p.support ∧
          P u ∧ ¬ P v ∧ ∀ w : V, w ∈ q.support → P w := by
  induction p with
  | nil =>
      exact (hb ha).elim
  | @cons a c b hac p ih =>
      by_cases hc : P c
      · obtain ⟨u, v, huv, q, s, hp, hu_mem, hv_mem, hu, hv, hq⟩ := ih hc hb
        refine ⟨u, v, huv, SimpleGraph.Walk.cons hac q, s, ?_, ?_, ?_, hu, hv, ?_⟩
        · rw [hp]
          rfl
        · simpa [SimpleGraph.Walk.support_cons] using
            (Or.inr hu_mem : u = a ∨ u ∈ p.support)
        · simpa [SimpleGraph.Walk.support_cons] using
            (Or.inr hv_mem : v = a ∨ v ∈ p.support)
        · intro w hw
          have hw' : w = a ∨ w ∈ q.support := by
            simpa [SimpleGraph.Walk.support_cons] using hw
          rcases hw' with rfl | hw
          · exact ha
          · exact hq w hw
      · refine ⟨a, c, hac, SimpleGraph.Walk.nil, p, ?_, ?_, ?_, ha, hc, ?_⟩
        · rfl
        · exact SimpleGraph.Walk.start_mem_support _
        · simpa [SimpleGraph.Walk.support_cons] using
            (Or.inr p.start_mem_support : c = a ∨ c ∈ p.support)
        · intro w hw
          rw [SimpleGraph.Walk.mem_support_nil_iff] at hw
          exact hw ▸ ha

lemma exists_last_crossing_of_walk {P : V → Prop}
    {a b : V} (p : G.Walk a b) (ha : P a) (hb : ¬ P b) :
    ∃ u v : V, G.Adj u v ∧ u ∈ p.support ∧ v ∈ p.support ∧ P u ∧ ¬ P v ∧
      ∃ q : G.Walk b v, ∀ w : V, w ∈ q.support → ¬ P w := by
  classical
  obtain ⟨v, u, huv, q, _s, _hp, hv_mem, hu_mem, hv, hu, hq⟩ :=
    exists_first_crossing_of_walk (G := G) (P := fun w => ¬ P w) p.reverse hb (by
      simpa using ha)
  have hv_mem' : v ∈ p.support := by
    rw [SimpleGraph.Walk.support_reverse] at hv_mem
    exact List.mem_reverse.mp hv_mem
  have hu_mem' : u ∈ p.support := by
    rw [SimpleGraph.Walk.support_reverse] at hu_mem
    exact List.mem_reverse.mp hu_mem
  refine ⟨u, v, huv.symm, hu_mem', hv_mem', ?_, hv, q, hq⟩
  exact Classical.byContradiction hu

lemma treeOrder_root_of_isTree (hT : T.IsTree) (r x : V) :
    TreeOrder T r r x := by
  obtain ⟨p, hp⟩ := (hT.connected.preconnected r x).exists_isPath
  exact ⟨p, hp, p.start_mem_support⟩

lemma treeOrder_refl_of_isTree (hT : T.IsTree) (r x : V) :
    TreeOrder T r x x := by
  obtain ⟨p, hp⟩ := (hT.connected.preconnected r x).exists_isPath
  exact ⟨p, hp, p.end_mem_support⟩

lemma treeComparable_root_left_of_isTree (hT : T.IsTree) (r x : V) :
    TreeComparable T r r x :=
  Or.inl (treeOrder_root_of_isTree hT r x)

lemma treeComparable_root_right_of_isTree (hT : T.IsTree) (r x : V) :
    TreeComparable T r x r :=
  Or.inr (treeOrder_root_of_isTree hT r x)

lemma treeComparable_refl_of_isTree (hT : T.IsTree) (r x : V) :
    TreeComparable T r x x :=
  Or.inl (treeOrder_refl_of_isTree hT r x)

lemma treeOrder_trans_of_isTree (hT : T.IsTree)
    (hxy : TreeOrder T r x y) (hyz : TreeOrder T r y z) :
    TreeOrder T r x z := by
  rcases hxy with ⟨p, hp, hxp⟩
  rcases hyz with ⟨q, hq, hyq⟩
  obtain ⟨q₀, q₁, hq₀, _hq₁, hq_eq⟩ := hq.mem_support_iff_exists_append.mp hyq
  have hp_eq : p = q₀ := by
    exact (hT.existsUnique_path r y).unique hp hq₀
  refine ⟨q, hq, ?_⟩
  rw [hq_eq, SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inl (by simpa [hp_eq] using hxp)

lemma treeOrder_antisymm_of_isTree (hT : T.IsTree)
    (hxy : TreeOrder T r x y) (hyx : TreeOrder T r y x) :
    x = y := by
  rcases hxy with ⟨p, hp, hxp⟩
  rcases hyx with ⟨q, hq, hyq⟩
  obtain ⟨_p₀, _p₁, _hp₀, _hp₁, _hp_eq⟩ := hp.mem_support_iff_exists_append.mp hxp
  obtain ⟨q₀, q₁, hq₀, _hq₁, hq_eq⟩ := hq.mem_support_iff_exists_append.mp hyq
  have hp_eq_q₀ : p = q₀ := by
    exact (hT.existsUnique_path r y).unique hp hq₀
  by_contra hne
  have hxq₀ : x ∈ q₀.support := by
    simpa [hp_eq_q₀] using hxp
  have hxq₁ : x ∈ q₁.support := q₁.end_mem_support
  have hq_append : (q₀.append q₁).IsPath := by
    simpa [← hq_eq] using hq
  exact (hq_append.ne_of_mem_support_of_append hne hxq₀ hxq₁ rfl).elim

lemma treeComparable_of_mem_support_of_isPath
    {p : T.Walk r z} (hp : p.IsPath)
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    TreeComparable T r x y := by
  classical
  by_cases hxy : p.support.idxOf x ≤ p.support.idxOf y
  · let py := p.takeUntil y hy
    have hlen : p.support.idxOf x ≤ py.length := by
      simpa [py, SimpleGraph.Walk.length_takeUntil] using hxy
    have hget : py.getVert (p.support.idxOf x) = x := by
      rw [SimpleGraph.Walk.getVert_takeUntil hy hlen]
      exact p.getVert_support_idxOf hx
    have hxpy : x ∈ py.support := by
      rw [← hget]
      exact py.getVert_mem_support (p.support.idxOf x)
    exact Or.inl ⟨py, hp.takeUntil hy, hxpy⟩
  · let px := p.takeUntil x hx
    have hyx : p.support.idxOf y ≤ p.support.idxOf x := Nat.le_of_not_ge hxy
    have hlen : p.support.idxOf y ≤ px.length := by
      simpa [px, SimpleGraph.Walk.length_takeUntil] using hyx
    have hget : px.getVert (p.support.idxOf y) = y := by
      rw [SimpleGraph.Walk.getVert_takeUntil hx hlen]
      exact p.getVert_support_idxOf hy
    have hypx : y ∈ px.support := by
      rw [← hget]
      exact px.getVert_mem_support (p.support.idxOf y)
    exact Or.inr ⟨px, hp.takeUntil hx, hypx⟩

lemma treeComparable_of_le_of_le_of_isTree (hT : T.IsTree)
    (hxz : TreeOrder T r x z) (hyz : TreeOrder T r y z) :
    TreeComparable T r x y := by
  rcases hxz with ⟨p, hp, hxp⟩
  rcases hyz with ⟨q, hq, hyq⟩
  have hp_eq_q : p = q := by
    exact (hT.existsUnique_path r z).unique hp hq
  exact treeComparable_of_mem_support_of_isPath hp hxp (by simpa [← hp_eq_q] using hyq)

lemma treeOrder_of_comparable_of_treeOrder_of_not_treeOrder
    (hT : T.IsTree) {a b x : V}
    (hab : TreeComparable T r a b)
    (hxa : TreeOrder T r x a)
    (hxb : ¬ TreeOrder T r x b) :
    TreeOrder T r b x := by
  rcases hab with hab | hba
  · exact (hxb (treeOrder_trans_of_isTree hT hxa hab)).elim
  · have hcmp : TreeComparable T r b x :=
      treeComparable_of_le_of_le_of_isTree hT hba hxa
    rcases hcmp with hbx | hxb'
    · exact hbx
    · exact (hxb hxb').elim

lemma down_closure_self_of_isTree (hT : T.IsTree) (r x : V) :
    x ∈ down_closure T r x :=
  treeOrder_refl_of_isTree hT r x

lemma root_mem_down_closure_of_isTree (hT : T.IsTree) (r x : V) :
    r ∈ down_closure T r x :=
  treeOrder_root_of_isTree hT r x

lemma up_closure_root_of_isTree (hT : T.IsTree) (r : V) :
    up_closure T r r = Set.univ := by
  ext x
  exact ⟨fun _ => Set.mem_univ x, fun _ => treeOrder_root_of_isTree hT r x⟩

lemma down_closure_trans_of_isTree (hT : T.IsTree)
    (hxy : x ∈ down_closure T r y) (hyz : y ∈ down_closure T r z) :
    x ∈ down_closure T r z :=
  treeOrder_trans_of_isTree hT hxy hyz

lemma eq_empty_of_down_closed_of_root_notMem
    (hT : T.IsTree) {S : Set V}
    (hS : ∀ x ∈ S, down_closure T r x ⊆ S) (hrS : r ∉ S) :
    S = ∅ := by
  ext x
  constructor
  · intro hxS
    exact (hrS (hS x hxS (root_mem_down_closure_of_isTree hT r x))).elim
  · intro hx
    exact hx.elim

lemma not_treeComparable_ne_of_isTree (hT : T.IsTree)
    (hxy : ¬ TreeComparable T r x y) :
    x ≠ y := by
  intro h
  subst y
  exact hxy (treeComparable_refl_of_isTree hT r x)

lemma left_notMem_common_down_of_not_treeComparable (hT : T.IsTree)
    (hxy : ¬ TreeComparable T r x y) :
    x ∉ down_closure T r x ∩ down_closure T r y := by
  intro hx
  exact hxy (Or.inl hx.2)

lemma right_notMem_common_down_of_not_treeComparable (hT : T.IsTree)
    (hxy : ¬ TreeComparable T r x y) :
    y ∉ down_closure T r x ∩ down_closure T r y := by
  intro hy
  exact hxy (Or.inr hy.1)

lemma normal_adj_comparable (h : IsNormalSpanningTree G T r)
    (hxy : G.Adj x y) :
    TreeComparable T r x y :=
  h.2.2 hxy

lemma normal_tree_isTree (h : IsNormalSpanningTree G T r) : T.IsTree :=
  h.2.1

lemma normal_tree_le (h : IsNormalSpanningTree G T r) : T ≤ G :=
  h.1

lemma normal_graph_connected (h : IsNormalSpanningTree G T r) : G.Connected := by
  exact (normal_tree_isTree h).connected.map
    (SimpleGraph.Hom.ofLE (normal_tree_le h)) (fun v => ⟨v, rfl⟩)

lemma normal_walk_meets_common_down
    (h : IsNormalSpanningTree G T r)
    (hxy : ¬ TreeComparable T r x y) (p : G.Walk x y) :
    ∃ w : V, w ∈ p.support ∧
      w ∈ down_closure T r x ∩ down_closure T r y := by
  classical
  let P : V → Prop := fun w => TreeOrder T r w x
  have hT : T.IsTree := normal_tree_isTree h
  have hx : P x := treeOrder_refl_of_isTree hT r x
  have hy : ¬ P y := fun hyx => hxy (Or.inr hyx)
  obtain ⟨u, v, huv, hu_mem, _hv_mem, hu_le_x, hv_not_le_x, q, hq⟩ :=
    exists_last_crossing_of_walk (G := G) (P := P) p hx hy
  have huv_comp : TreeComparable T r u v := normal_adj_comparable h huv
  have hu_le_v : TreeOrder T r u v := by
    rcases huv_comp with huv' | hvu
    · exact huv'
    · exact (hv_not_le_x (treeOrder_trans_of_isTree hT hvu hu_le_x)).elim
  have hu_le_y : TreeOrder T r u y := by
    by_contra hu_not_y
    obtain ⟨a, b, hab, _q₀, _s, _hdecomp, _ha_mem, hb_mem,
        ha_le, hb_not, _hprefix⟩ :=
      exists_first_crossing_of_walk (G := G) (P := fun w => TreeOrder T r u w)
        q.reverse hu_le_v hu_not_y
    have hbq : b ∈ q.support := by
      rw [SimpleGraph.Walk.support_reverse] at hb_mem
      exact List.mem_reverse.mp hb_mem
    have hb_not_down_x : ¬ P b := hq b hbq
    have hb_le_u : TreeOrder T r b u :=
      treeOrder_of_comparable_of_treeOrder_of_not_treeOrder hT
        (normal_adj_comparable h hab) ha_le hb_not
    exact hb_not_down_x (treeOrder_trans_of_isTree hT hb_le_u hu_le_x)
  exact ⟨u, hu_mem, ⟨hu_le_x, hu_le_y⟩⟩

lemma normal_vertexSetSeparates_incomparable
    (h : IsNormalSpanningTree G T r) :
    ∀ x y : V,
      ¬ TreeComparable T r x y →
        SeparatesVertices G (down_closure T r x ∩ down_closure T r y) x y := by
  intro x y hxy
  have hT : T.IsTree := normal_tree_isTree h
  refine ⟨left_notMem_common_down_of_not_treeComparable hT hxy,
    right_notMem_common_down_of_not_treeComparable hT hxy, ?_⟩
  intro a b p hp
  rcases hp with ⟨_hp_path, ha, hb, _hA, _hB⟩
  rw [Set.mem_singleton_iff] at ha hb
  subst a
  subst b
  exact normal_walk_meets_common_down h hxy p

lemma not_vertexSetSeparates_of_connected_induce_subset_compl
    {S C : Set V} {x y : V}
    (hC : (G.induce C).Connected) (hxC : x ∈ C) (hyC : y ∈ C)
    (hCS : C ⊆ Sᶜ) :
    ¬ VertexSetSeparates G S {x} {y} := by
  classical
  intro hsep
  obtain ⟨pC, hpC⟩ :=
    (hC.preconnected ⟨x, hxC⟩ ⟨y, hyC⟩).exists_isPath
  let f := (SimpleGraph.Embedding.induce (G := G) C).toHom
  let pG : G.Walk x y := pC.map f
  have hpG : pG.IsPath := by
    dsimp [pG, f]
    exact pC.map_isPath_of_injective Subtype.val_injective hpC
  have hsupportC : ∀ z : V, z ∈ pG.support → z ∈ C := by
    intro z hz
    have hz0 : z ∈ (pC.map f).support := by
      change z ∈ (pC.map f).support at hz
      exact hz
    have hsupp_eq : (pC.map f).support = pC.support.map f :=
      SimpleGraph.Walk.support_map f pC
    rw [hsupp_eq] at hz0
    rcases List.mem_map.mp hz0 with ⟨w, _hw, hwz⟩
    have hwz' : (w : V) = z := by
      simpa [f] using hwz
    subst z
    exact w.2
  have hAB : IsABPath G pG {x} {y} := by
    refine ⟨hpG, by simp, by simp, ?_, ?_⟩
    · intro z _hz hz
      simpa using hz
    · intro z _hz hz
      simpa using hz
  obtain ⟨z, hz_support, hzS⟩ := hsep pG hAB
  exact hCS (hsupportC z hz_support) hzS

lemma normal_component_root_case
    (h : IsNormalSpanningTree G T r) {S C : Set V}
    (hS : ∀ x ∈ S, down_closure T r x ⊆ S)
    (hrS : r ∉ S)
    (_hC_sub : C ⊆ Sᶜ)
    (_hC_conn : (G.induce C).Connected)
    (hC_max : ∀ D : Set V, C ⊂ D → D ⊆ Sᶜ → ¬ (G.induce D).Connected) :
    r ∉ S ∧
      (∀ y : V, y ∉ S → TreeOrder T r y r → y = r) ∧
        C = up_closure T r r := by
  classical
  have hT : T.IsTree := normal_tree_isTree h
  have hS_empty : S = ∅ :=
    eq_empty_of_down_closed_of_root_notMem hT hS hrS
  have hC_univ : C = Set.univ := by
    by_contra hne
    have hproper : C ⊂ Set.univ := by
      refine ⟨Set.subset_univ C, ?_⟩
      intro huniv
      exact hne (Set.Subset.antisymm (Set.subset_univ C) huniv)
    have hDsub : (Set.univ : Set V) ⊆ Sᶜ := by
      intro v _
      rw [hS_empty]
      simp
    have hGuniv : (G.induce (Set.univ : Set V)).Connected :=
      (SimpleGraph.induceUnivIso G).connected_iff.mpr (normal_graph_connected h)
    exact hC_max Set.univ hproper hDsub hGuniv
  refine ⟨hrS, ?_, ?_⟩
  · intro y _hyS hyr
    exact treeOrder_antisymm_of_isTree hT hyr
      (treeOrder_root_of_isTree hT r y)
  · rw [hC_univ, up_closure_root_of_isTree hT r]

lemma first_outside_minimal_of_prefix
    (hT : T.IsTree) {S : Set V} {u v : V}
    {q : T.Walk r u} (hq_path : q.IsPath)
    (huv : T.Adj u v)
    (hqS : ∀ w : V, w ∈ q.support → w ∈ S)
    (hvS : v ∉ S) :
    ∀ y : V, y ∉ S → TreeOrder T r y v → y = v := by
  intro y hyS hyv
  rcases hyv with ⟨py, hpy, hypy⟩
  have hvq : v ∉ q.support := fun hvq => hvS (hqS v hvq)
  have hqv_path : (q.concat huv).IsPath :=
    hq_path.concat hvq huv
  have hpy_eq : py = q.concat huv := by
    exact (hT.existsUnique_path r v).unique hpy hqv_path
  have hy_mem : y ∈ (q.concat huv).support := by
    simpa [hpy_eq] using hypy
  rw [SimpleGraph.Walk.support_concat] at hy_mem
  have hy_or : y ∈ q.support ∨ y = v := by
    simpa using hy_mem
  rcases hy_or with hyq | rfl
  · exact (hyS (hqS y hyq)).elim
  · rfl

lemma walk_support_subset_of_maximal_connected_compl
    {S C : Set V} {x y : V}
    (hC_sub : C ⊆ Sᶜ)
    (hC_conn : (G.induce C).Connected)
    (hC_max : ∀ D : Set V, C ⊂ D → D ⊆ Sᶜ → ¬ (G.induce D).Connected)
    (hxC : x ∈ C) (p : G.Walk x y)
    (hpS : ∀ z : V, z ∈ p.support → z ∉ S) :
    ∀ z : V, z ∈ p.support → z ∈ C := by
  classical
  let Pset : Set V := {z | z ∈ p.support}
  let D : Set V := C ∪ Pset
  have hD_conn : (G.induce D).Connected := by
    have hP_conn : (G.induce Pset).Connected := by
      simpa [Pset] using p.connected_induce_support
    have hinter : (C ∩ Pset).Nonempty := by
      exact ⟨x, hxC, by exact p.start_mem_support⟩
    exact SimpleGraph.induce_union_connected hC_conn.preconnected hP_conn.preconnected hinter
  have hD_sub : D ⊆ Sᶜ := by
    intro z hz
    rcases hz with hzC | hzP
    · exact hC_sub hzC
    · exact hpS z hzP
  have hD_subset_C : D ⊆ C := by
    intro z hzD
    by_contra hzC
    have hstrict : C ⊂ D := by
      refine ⟨?_, ?_⟩
      · intro w hw
        exact Or.inl hw
      · intro hD_C
        exact hzC (hD_C hzD)
    exact hC_max D hstrict hD_sub hD_conn
  intro z hz
  exact hD_subset_C (Or.inr hz)

lemma exists_tree_path_support_compl_of_treeOrder
    (hT : T.IsTree) {S : Set V}
    (hS : ∀ x ∈ S, down_closure T r x ⊆ S)
    (hxS : x ∉ S) (hxy : TreeOrder T r x y) :
    ∃ p : T.Walk x y, p.IsPath ∧ ∀ z : V, z ∈ p.support → z ∉ S := by
  classical
  have hxy₀ : TreeOrder T r x y := hxy
  rcases hxy with ⟨p, hp, hxp⟩
  obtain ⟨q, s, hq, hs, hp_eq⟩ := hp.mem_support_iff_exists_append.mp hxp
  refine ⟨s, hs, ?_⟩
  intro z hzs hzS
  have hzy : TreeOrder T r z y := by
    refine ⟨p, hp, ?_⟩
    rw [hp_eq, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hzs
  have hx_or_zx : TreeComparable T r x z :=
    treeComparable_of_le_of_le_of_isTree hT hxy₀ hzy
  have hxz : TreeOrder T r x z := by
    rcases hx_or_zx with hxz | hzx
    · exact hxz
    · by_cases hzx_eq : z = x
      · subst z
        exact treeOrder_refl_of_isTree hT r x
      · have hzq : z ∈ q.support := by
          rcases hzx with ⟨qz, hqz, hzqz⟩
          have hqz_eq : qz = q := by
            exact (hT.existsUnique_path r x).unique hqz hq
          simpa [hqz_eq] using hzqz
        have hp_append : (q.append s).IsPath := by
          simpa [← hp_eq] using hp
        exact ((hp_append.ne_of_mem_support_of_append hzx_eq hzq hzs rfl).elim)
  exact hxS (hS z hzS hxz)

lemma up_closure_subset_of_component
    (h : IsNormalSpanningTree G T r) {S C : Set V} {x : V}
    (hS : ∀ x ∈ S, down_closure T r x ⊆ S)
    (hC_sub : C ⊆ Sᶜ)
    (hC_conn : (G.induce C).Connected)
    (hC_max : ∀ D : Set V, C ⊂ D → D ⊆ Sᶜ → ¬ (G.induce D).Connected)
    (hxC : x ∈ C) (hxS : x ∉ S) :
    up_closure T r x ⊆ C := by
  intro y hxy
  obtain ⟨pT, _hpT, hpT_S⟩ :=
    exists_tree_path_support_compl_of_treeOrder (normal_tree_isTree h) hS hxS hxy
  let pG : G.Walk x y := pT.mapLe (normal_tree_le h)
  have hpG_S : ∀ z : V, z ∈ pG.support → z ∉ S := by
    intro z hz
    have hzT : z ∈ pT.support := by
      simpa [pG, SimpleGraph.Walk.support_mapLe_eq_support] using hz
    exact hpT_S z hzT
  have hsupp :=
    walk_support_subset_of_maximal_connected_compl hC_sub hC_conn hC_max hxC pG hpG_S
  exact hsupp y pG.end_mem_support

lemma component_subset_up_closure_of_minimal
    (h : IsNormalSpanningTree G T r) {S C : Set V} {x : V}
    (hC_sub : C ⊆ Sᶜ)
    (hC_conn : (G.induce C).Connected)
    (hxC : x ∈ C)
    (hx_min : ∀ y : V, y ∉ S → TreeOrder T r y x → y = x) :
    C ⊆ up_closure T r x := by
  classical
  intro y hyC
  by_cases hxy : TreeOrder T r x y
  · exact hxy
  have hcomp : TreeComparable T r x y := by
    by_contra hncomp
    have hsep :=
      normal_vertexSetSeparates_incomparable h x y hncomp
    have hcommon_sub_S :
        down_closure T r x ∩ down_closure T r y ⊆ S := by
      intro z hz
      by_contra hzS
      have hzx : z = x := hx_min z hzS hz.1
      exact hncomp (Or.inl (by simpa [hzx] using hz.2))
    have hC_sub_common_compl :
        C ⊆ (down_closure T r x ∩ down_closure T r y)ᶜ := by
      intro z hzC hzcommon
      exact hC_sub hzC (hcommon_sub_S hzcommon)
    exact not_vertexSetSeparates_of_connected_induce_subset_compl
      hC_conn hxC hyC hC_sub_common_compl hsep.2.2
  rcases hcomp with hxy' | hyx
  · exact hxy'
  · have hyS : y ∉ S := hC_sub hyC
    have hy_eq : y = x := hx_min y hyS hyx
    subst y
    exact treeOrder_refl_of_isTree (normal_tree_isTree h) r x

lemma normal_component_nonroot_case
    (h : IsNormalSpanningTree G T r) {S C : Set V}
    (hS : ∀ x ∈ S, down_closure T r x ⊆ S)
    (hrS : r ∈ S)
    (hC_sub : C ⊆ Sᶜ)
    (hC_conn : (G.induce C).Connected)
    (hC_max : ∀ D : Set V, C ⊂ D → D ⊆ Sᶜ → ¬ (G.induce D).Connected) :
    ∃ x : V,
      x ∉ S ∧
        (∀ y : V, y ∉ S → TreeOrder T r y x → y = x) ∧
          C = up_closure T r x := by
  classical
  have hT : T.IsTree := normal_tree_isTree h
  obtain ⟨c⟩ := hC_conn.nonempty
  have hcS : c.1 ∉ S := hC_sub c.2
  obtain ⟨p, hp⟩ := (hT.connected.preconnected r c.1).exists_isPath
  obtain ⟨u, v, huv, q, s, hp_decomp, _hu_mem, hv_mem, huS, hvS, hqS⟩ :=
    exists_first_crossing_of_walk (G := T) (P := fun z => z ∈ S) p hrS hcS
  have hq_path : q.IsPath := by
    have happ : (q.append (SimpleGraph.Walk.cons huv s)).IsPath := by
      simpa [← hp_decomp] using hp
    exact happ.of_append_left
  have hv_min : ∀ y : V, y ∉ S → TreeOrder T r y v → y = v :=
    first_outside_minimal_of_prefix hT hq_path huv hqS hvS
  have hv_c : TreeOrder T r v c.1 := ⟨p, hp, hv_mem⟩
  obtain ⟨pT, _hpT, hpT_S⟩ :=
    exists_tree_path_support_compl_of_treeOrder hT hS hvS hv_c
  let pG : G.Walk c.1 v := (pT.mapLe (normal_tree_le h)).reverse
  have hpG_S : ∀ z : V, z ∈ pG.support → z ∉ S := by
    intro z hz
    have hzT : z ∈ pT.support := by
      dsimp [pG] at hz
      rw [SimpleGraph.Walk.support_reverse] at hz
      have hz' := List.mem_reverse.mp hz
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hz'
    exact hpT_S z hzT
  have hsupp :=
    walk_support_subset_of_maximal_connected_compl hC_sub hC_conn hC_max c.2 pG hpG_S
  have hvC : v ∈ C := hsupp v pG.end_mem_support
  have hupC : up_closure T r v ⊆ C :=
    up_closure_subset_of_component h hS hC_sub hC_conn hC_max hvC hvS
  have hCup : C ⊆ up_closure T r v :=
    component_subset_up_closure_of_minimal h hC_sub hC_conn hvC hv_min
  exact ⟨v, hvS, hv_min, Set.Subset.antisymm hCup hupC⟩

end Chapter01
end Diestel
