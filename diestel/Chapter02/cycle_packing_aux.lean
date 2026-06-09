import Chapter02.multigraph_spanning_tree_aux
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Combinatorics.Graph.Subgraph

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma CycleIn.support_subset_vertexSet {G : MultiGraph V E} (C : G.CycleIn) :
    C.support ⊆ G.vertexSet := by
  intro v hv
  have hcard := C.degree_two v hv
  have hpos : 0 < Nat.card {e : C.edgeSupport // G.Inc e.1 v} := by
    omega
  haveI : Finite C.edgeSupport := Set.Finite.to_subtype C.edgeSupport_finite
  haveI : Finite {e : C.edgeSupport // G.Inc e.1 v} := inferInstance
  have hnonempty : Nonempty {e : C.edgeSupport // G.Inc e.1 v} :=
    (Finite.card_pos_iff).mp hpos
  rcases hnonempty with ⟨e⟩
  rcases e.2 with ⟨w, hlink⟩
  exact hlink.left_mem

lemma inc_iff_of_subgraph_edge {H G : MultiGraph V E} (hHG : H ≤ G)
    {e : E} (heH : e ∈ H.edgeSet) {v : V} :
    H.Inc e v ↔ G.Inc e v := by
  constructor
  · intro h
    rcases h with ⟨w, hlink⟩
    exact ⟨w, hlink.mono hHG⟩
  · intro h
    rcases h with ⟨w, hlink⟩
    exact ⟨w, (Graph.IsSubgraph.isLink_iff (H := H) (G := G) hHG heH).mpr hlink⟩

def cycleIn_of_subgraph {H G : MultiGraph V E} (hHG : H ≤ G)
    (C : H.CycleIn) : G.CycleIn where
  support := C.support
  edgeSupport := C.edgeSupport
  edgeSupport_finite := C.edgeSupport_finite
  edges_inside := by
    intro e heC
    have heInside := C.edges_inside heC
    refine ⟨hHG.edgeSet_mono heInside.1, ?_⟩
    intro v hv
    exact heInside.2 v ((inc_iff_of_subgraph_edge hHG heInside.1).mpr hv)
  support_nonempty := C.support_nonempty
  connected := by
    rcases C.connected with ⟨hpre⟩
    refine ⟨?_⟩
    intro a b
    exact (hpre a b).mono fun x y hxy => by
      rcases hxy with ⟨hne, e, heC, heH, hlinkH⟩
      exact ⟨hne, e, heC, hHG.edgeSet_mono heH, hlinkH.mono hHG⟩
  degree_two := by
    intro v hv
    let φ :
        {e : C.edgeSupport // G.Inc e.1 v} ≃
          {e : C.edgeSupport // H.Inc e.1 v} := by
      refine
        { toFun := fun e =>
            ⟨e.1, (inc_iff_of_subgraph_edge hHG ((C.edges_inside e.1.2).1)).mpr e.2⟩
          invFun := fun e =>
            ⟨e.1, (inc_iff_of_subgraph_edge hHG ((C.edges_inside e.1.2).1)).mp e.2⟩
          left_inv := ?_
          right_inv := ?_ }
      · intro e
        rfl
      · intro e
        rfl
    rw [Nat.card_congr φ]
    exact C.degree_two v hv

lemma hasKDisjointCycles_of_subgraph {H G : MultiGraph V E}
    {k : ℕ} (hHG : H ≤ G) :
    H.HasKDisjointCycles k → G.HasKDisjointCycles k := by
  rintro ⟨C, hdisj⟩
  exact ⟨fun i => cycleIn_of_subgraph hHG (C i), hdisj⟩

lemma disjoint_cycle_of_deleteVerts {G : MultiGraph V E}
    (C : G.CycleIn) (D : CycleIn (G.deleteVerts C.support)) :
    Disjoint C.support (cycleIn_of_subgraph (Graph.deleteVerts_le (G := G)
      (X := C.support)) D).support := by
  rw [Set.disjoint_left]
  intro v hvC hvD
  have hvDelete :
      v ∈ (G.deleteVerts C.support).vertexSet :=
    D.support_subset_vertexSet hvD
  simpa using hvDelete.2 hvC

lemma hasKDisjointCycles_succ_of_deleteVerts {G : MultiGraph V E}
    {k : ℕ} (C : G.CycleIn) :
    HasKDisjointCycles (G.deleteVerts C.support) k →
      G.HasKDisjointCycles (k + 1) := by
  intro hpack
  rcases hpack with ⟨D, hDdisj⟩
  let liftD (i : Fin k) : G.CycleIn :=
    cycleIn_of_subgraph (Graph.deleteVerts_le (G := G) (X := C.support)) (D i)
  refine ⟨Fin.cases C liftD, ?_⟩
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          exact (hij rfl).elim
      | succ j =>
          simpa [liftD] using disjoint_cycle_of_deleteVerts (G := G) C (D j)
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have hdisj := disjoint_cycle_of_deleteVerts (G := G) C (D i)
          simpa [liftD, disjoint_comm] using hdisj
      | succ j =>
          have hij' : i ≠ j := by
            intro h
            exact hij (by simp [h])
          exact hDdisj hij'

lemma isLink_ne_of_loopless {G : MultiGraph V E} (hloopless : G.Loopless)
    {e : E} {x y : V} (hxy : G.IsLink e x y) : x ≠ y := by
  intro h
  exact hloopless hxy.edge_mem x (h ▸ hxy)

private lemma parallel_edge_cycle_connected {G : MultiGraph V E}
    {e f : E} {x y : V} (hxy : x ≠ y)
    (he : G.IsLink e x y) :
    ((G.edgeSubgraph ({e, f} : Set E)).induce ({x, y} : Set V)).Connected := by
  classical
  refine ⟨?_⟩
  intro a b
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    change (G.edgeSubgraph ({e, f} : Set E)).Adj a b
    have hlink : G.IsLink e a b := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact (hab (ha.trans hb.symm)).elim
      · rw [ha, hb]
        exact he
      · rw [ha, hb]
        exact he.symm
      · exact (hab (ha.trans hb.symm)).elim
    exact ⟨hab, e, by simp, he.edge_mem, hlink⟩

private noncomputable def parallelIncidenceEquivLeft {G : MultiGraph V E}
    {e f : E} {x y : V} (hef : e ≠ f)
    (he : G.IsLink e x y) (hf : G.IsLink f x y) :
    {g : ({e, f} : Set E) // G.Inc g.1 x} ≃ Bool := by
  classical
  refine
    { toFun := fun g => if g.1.1 = e then false else true
      invFun := fun b =>
        cond b ⟨⟨f, by simp⟩, hf.inc_left⟩ ⟨⟨e, by simp⟩, he.inc_left⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro g
    rcases g with ⟨⟨g, hgmem⟩, hginc⟩
    by_cases hge : g = e
    · subst g
      simp
    · have hgf : g = f := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hge] using hgmem
      subst g
      simp [hef.symm]
  · intro b
    have hfe : f ≠ e := hef.symm
    cases b <;> simp [hef, hfe]

private noncomputable def parallelIncidenceEquivRight {G : MultiGraph V E}
    {e f : E} {x y : V} (hef : e ≠ f)
    (he : G.IsLink e x y) (hf : G.IsLink f x y) :
    {g : ({e, f} : Set E) // G.Inc g.1 y} ≃ Bool := by
  classical
  refine
    { toFun := fun g => if g.1.1 = e then false else true
      invFun := fun b =>
        cond b ⟨⟨f, by simp⟩, hf.inc_right⟩ ⟨⟨e, by simp⟩, he.inc_right⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro g
    rcases g with ⟨⟨g, hgmem⟩, hginc⟩
    by_cases hge : g = e
    · subst g
      simp
    · have hgf : g = f := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hge] using hgmem
      subst g
      simp [hef.symm]
  · intro b
    have hfe : f ≠ e := hef.symm
    cases b <;> simp [hef, hfe]

lemma parallel_incidence_card_left {G : MultiGraph V E}
    {e f : E} {x y : V} (hef : e ≠ f)
    (he : G.IsLink e x y) (hf : G.IsLink f x y) :
    Nat.card {g : ({e, f} : Set E) // G.Inc g.1 x} = 2 := by
  classical
  rw [Nat.card_congr (parallelIncidenceEquivLeft (G := G) hef he hf)]
  rw [Nat.card_eq_fintype_card, Fintype.card_bool]

lemma parallel_incidence_card_right {G : MultiGraph V E}
    {e f : E} {x y : V} (hef : e ≠ f)
    (he : G.IsLink e x y) (hf : G.IsLink f x y) :
    Nat.card {g : ({e, f} : Set E) // G.Inc g.1 y} = 2 := by
  classical
  rw [Nat.card_congr (parallelIncidenceEquivRight (G := G) hef he hf)]
  rw [Nat.card_eq_fintype_card, Fintype.card_bool]

/--
Two distinct parallel non-loop edges form a multigraph cycle of length two.
This is the first concrete `CycleIn` constructor needed for the Chapter 2
cycle-packing proof.
-/
def cycleOfParallelEdges {G : MultiGraph V E}
    {e f : E} {x y : V} (hef : e ≠ f) (hxy : x ≠ y)
    (he : G.IsLink e x y) (hf : G.IsLink f x y) : G.CycleIn where
  support := ({x, y} : Set V)
  edgeSupport := ({e, f} : Set E)
  edgeSupport_finite := by
    simp
  edges_inside := by
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨he.edge_mem, by
        intro v hv
        rcases hv.eq_or_eq_of_isLink he with rfl | rfl <;> simp⟩
    · exact ⟨hf.edge_mem, by
        intro v hv
        rcases hv.eq_or_eq_of_isLink hf with rfl | rfl <;> simp⟩
  support_nonempty := by
    exact ⟨x, by simp⟩
  connected := parallel_edge_cycle_connected (G := G) (e := e) (f := f) hxy he
  degree_two := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact parallel_incidence_card_left (G := G) hef he hf
    · exact parallel_incidence_card_right (G := G) hef he hf

lemma hasOneDisjointCycle_of_parallel_edges {G : MultiGraph V E}
    {e f : E} {x y : V} (hef : e ≠ f) (hxy : x ≠ y)
    (he : G.IsLink e x y) (hf : G.IsLink f x y) :
    G.HasKDisjointCycles 1 := by
  classical
  refine ⟨fun _ : Fin 1 => cycleOfParallelEdges (G := G) hef hxy he hf, ?_⟩
  intro i j hij
  fin_cases i
  fin_cases j
  exact (hij rfl).elim

lemma cycleOfParallelEdges_support_ncard {G : MultiGraph V E}
    {e f : E} {x y : V} (hef : e ≠ f) (hxy : x ≠ y)
    (he : G.IsLink e x y) (hf : G.IsLink f x y) :
    (cycleOfParallelEdges (G := G) hef hxy he hf).support.ncard = 2 := by
  exact Set.ncard_pair hxy

lemma liftedTreeEdge_isLink_of_adj {G : MultiGraph V E}
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph)
    {x y : G.vertexSet} (hxy : T.Adj x y) :
    G.IsLink
      (liftedTreeEdge (G := G) hTG
        ⟨s(x, y), by simpa [SimpleGraph.mem_edgeSet] using hxy⟩)
      x.1 y.1 := by
  classical
  let q : T.edgeSet := ⟨s(x, y), by simpa [SimpleGraph.mem_edgeSet] using hxy⟩
  obtain ⟨a, b, hqval, hlink⟩ := liftedTreeEdge_spec (G := G) hTG q
  have hsym : s(a.1, b.1) = s(x.1, y.1) := by
    have hqval' : s(x, y) = s(a, b) := by
      simpa [q] using hqval
    rcases Sym2.eq_iff.mp hqval' with hsame | hswap
    · rcases hsame with ⟨hxa, hyb⟩
      subst a
      subst b
      rfl
    · rcases hswap with ⟨hxb, hya⟩
      subst b
      subst a
      exact Sym2.eq_swap
  exact (hlink.isLink_iff_sym2_eq).2 hsym

/-- The original-vertex support of a simple cycle in the shadow graph. -/
def simpleCycleSupport {G : MultiGraph V E} {r : G.vertexSet}
    (p : G.toSimpleGraph.Walk r r) : Set V :=
  {v | ∃ hv : v ∈ G.vertexSet, (⟨v, hv⟩ : G.vertexSet) ∈ p.support}

/-- Multiedges selected over the simple edges of a shadow-graph cycle. -/
noncomputable def liftedSimpleCycleEdgeSet {G : MultiGraph V E} {r : G.vertexSet}
    (p : G.toSimpleGraph.Walk r r) : Set E :=
  liftedTreeEdgeSet (G := G) (T := p.toSubgraph.spanningCoe) p.toSubgraph.spanningCoe_le

lemma liftedSimpleCycleEdgeSet_subset {G : MultiGraph V E} {r : G.vertexSet}
    (p : G.toSimpleGraph.Walk r r) :
    liftedSimpleCycleEdgeSet (G := G) p ⊆ G.edgeSet :=
  liftedTreeEdgeSet_subset (G := G) p.toSubgraph.spanningCoe_le

lemma liftedSimpleCycleEdgeSet_finite {G : MultiGraph V E} [Finite E] {r : G.vertexSet}
    (p : G.toSimpleGraph.Walk r r) :
    (liftedSimpleCycleEdgeSet (G := G) p).Finite :=
  liftedTreeEdgeSet_finite (G := G) p.toSubgraph.spanningCoe_le

private lemma liftedSimpleCycle_hom_adj {G : MultiGraph V E} {r : G.vertexSet}
    (p : G.toSimpleGraph.Walk r r)
    {a b : p.toSubgraph.verts} (hab : p.toSubgraph.coe.Adj a b) :
    ((G.edgeSubgraph (liftedSimpleCycleEdgeSet (G := G) p)).induce
        (simpleCycleSupport (G := G) p)).Adj
      ⟨a.1.1, ⟨a.1.2, (p.mem_verts_toSubgraph).mp a.2⟩⟩
      ⟨b.1.1, ⟨b.1.2, (p.mem_verts_toSubgraph).mp b.2⟩⟩ := by
  classical
  have habSub : p.toSubgraph.Adj a.1 b.1 := by
    simpa using hab
  let q : p.toSubgraph.spanningCoe.edgeSet :=
    ⟨s(a.1, b.1), by
      have hmemSub : s(a.1, b.1) ∈ p.toSubgraph.edgeSet := habSub
      change s(a.1, b.1) ∈ p.toSubgraph.edgeSet
      exact hmemSub⟩
  change (G.edgeSubgraph (liftedSimpleCycleEdgeSet (G := G) p)).Adj a.1.1 b.1.1
  have hlink :
      G.IsLink (liftedTreeEdge (G := G) p.toSubgraph.spanningCoe_le q) a.1.1 b.1.1 := by
    simpa [q] using
      liftedTreeEdge_isLink_of_adj (G := G) p.toSubgraph.spanningCoe_le habSub
  refine ⟨?_, liftedTreeEdge (G := G) p.toSubgraph.spanningCoe_le q, ?_, ?_, hlink⟩
  · intro hv
    exact hab.ne (Subtype.ext (Subtype.ext hv))
  · exact ⟨q, rfl⟩
  · exact liftedTreeEdge_mem (G := G) p.toSubgraph.spanningCoe_le q

lemma liftedSimpleCycle_connected {G : MultiGraph V E} {r : G.vertexSet}
    (p : G.toSimpleGraph.Walk r r) :
    ((G.edgeSubgraph (liftedSimpleCycleEdgeSet (G := G) p)).induce
        (simpleCycleSupport (G := G) p)).Connected := by
  classical
  let φ :
      p.toSubgraph.coe →g
        ((G.edgeSubgraph (liftedSimpleCycleEdgeSet (G := G) p)).induce
          (simpleCycleSupport (G := G) p)) :=
    { toFun := fun a => ⟨a.1.1, ⟨a.1.2, (p.mem_verts_toSubgraph).mp a.2⟩⟩
      map_rel' := by
        intro a b hab
        exact liftedSimpleCycle_hom_adj (G := G) p hab }
  have hsurj : Function.Surjective φ := by
    intro z
    rcases z with ⟨z, hz⟩
    rcases hz with ⟨hzG, hzp⟩
    refine ⟨⟨⟨z, hzG⟩, (p.mem_verts_toSubgraph).mpr hzp⟩, ?_⟩
    rfl
  exact (p.toSubgraph_connected : p.toSubgraph.coe.Connected).map φ hsurj

lemma liftedTreeEdge_inc_iff_mem_incidence {G : MultiGraph V E}
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph)
    (q : T.edgeSet) (v : G.vertexSet) :
    G.Inc (liftedTreeEdge (G := G) hTG q) v.1 ↔
      (q : Sym2 G.vertexSet) ∈ T.incidenceSet v := by
  classical
  obtain ⟨a, b, hq, hlink⟩ := liftedTreeEdge_spec (G := G) hTG q
  constructor
  · intro hinc
    have hvabV : v.1 = a.1 ∨ v.1 = b.1 := hinc.eq_or_eq_of_isLink hlink
    have hvab : v = a ∨ v = b := by
      rcases hvabV with hv | hv
      · exact Or.inl (Subtype.ext hv)
      · exact Or.inr (Subtype.ext hv)
    rcases hvab with rfl | rfl
    · exact ⟨q.2, by rw [hq]; simp⟩
    · exact ⟨q.2, by rw [hq]; simp⟩
  · intro hqinc
    have hvq : v ∈ (q : Sym2 G.vertexSet) := hqinc.2
    rw [hq] at hvq
    rcases Sym2.mem_iff.mp hvq with rfl | rfl
    · exact hlink.inc_left
    · exact hlink.inc_right

private noncomputable def liftedIncidentEquivIncidenceSet {G : MultiGraph V E}
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph)
    (v : G.vertexSet) :
    {e : (liftedTreeEdgeSet (G := G) hTG) // G.Inc e.1 v.1} ≃
      T.incidenceSet v := by
  classical
  refine
    { toFun := fun e =>
        let q : T.edgeSet := Classical.choose e.1.2
        ⟨(q : Sym2 G.vertexSet), by
          have hqe : liftedTreeEdge (G := G) hTG q = e.1.1 :=
            Classical.choose_spec e.1.2
          have hinc : G.Inc (liftedTreeEdge (G := G) hTG q) v.1 := by
            simpa [hqe] using e.2
          exact (liftedTreeEdge_inc_iff_mem_incidence (G := G) hTG q v).mp hinc⟩
      invFun := fun q =>
        let qEdge : T.edgeSet := ⟨q.1, q.2.1⟩
        ⟨⟨liftedTreeEdge (G := G) hTG qEdge, ⟨qEdge, rfl⟩⟩,
          (liftedTreeEdge_inc_iff_mem_incidence (G := G) hTG qEdge v).mpr q.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    rcases e with ⟨⟨e, heF⟩, heInc⟩
    dsimp
    let q : T.edgeSet := Classical.choose heF
    have hqe : liftedTreeEdge (G := G) hTG q = e := Classical.choose_spec heF
    apply Subtype.ext
    apply Subtype.ext
    exact hqe
  · intro q
    rcases q with ⟨q, hqinc⟩
    dsimp
    let qEdge : T.edgeSet := ⟨q, hqinc.1⟩
    let qChosen : T.edgeSet :=
      Classical.choose (show liftedTreeEdge (G := G) hTG qEdge ∈
        liftedTreeEdgeSet (G := G) hTG from ⟨qEdge, rfl⟩)
    have hqChosen :
        liftedTreeEdge (G := G) hTG qChosen = liftedTreeEdge (G := G) hTG qEdge :=
      Classical.choose_spec (show liftedTreeEdge (G := G) hTG qEdge ∈
        liftedTreeEdgeSet (G := G) hTG from ⟨qEdge, rfl⟩)
    have hqq : qChosen = qEdge :=
      liftedTreeEdge_injective (G := G) hTG hqChosen
    apply Subtype.ext
    simpa [qEdge, qChosen, hqq]

lemma liftedSimpleCycle_incidence_card {G : MultiGraph V E} {r : G.vertexSet}
    {p : G.toSimpleGraph.Walk r r} (hp : p.IsCycle)
    {v : V} (hv : v ∈ simpleCycleSupport (G := G) p) :
    Nat.card {e : (liftedSimpleCycleEdgeSet (G := G) p) // G.Inc e.1 v} = 2 := by
  classical
  rcases hv with ⟨hvG, hvp⟩
  let vv : G.vertexSet := ⟨v, hvG⟩
  have hsimple :
      Nat.card (p.toSubgraph.spanningCoe.incidenceSet vv) = 2 := by
    rw [Nat.card_congr ((p.toSubgraph.spanningCoe).incidenceSetEquivNeighborSet vv)]
    change Nat.card (p.toSubgraph.neighborSet vv) = 2
    simpa using hp.ncard_neighborSet_toSubgraph_eq_two hvp
  simpa [liftedSimpleCycleEdgeSet, vv] using
    (Nat.card_congr
      (liftedIncidentEquivIncidenceSet (G := G) p.toSubgraph.spanningCoe_le vv)).trans
        hsimple

private lemma walk_isCycle_support_set_ncard_eq_length {α : Type u}
    {G : SimpleGraph α} {r : α} {p : G.Walk r r} (hp : p.IsCycle) :
    ({v : α | v ∈ p.support} : Set α).ncard = p.length := by
  classical
  have hsupport_eq_tail :
      ({v : α | v ∈ p.support} : Set α) = {v : α | v ∈ p.support.tail} := by
    ext v
    constructor
    · intro hv
      have hv' : v ∈ r :: p.support.tail := by
        simpa [SimpleGraph.Walk.cons_tail_support] using hv
      rcases List.mem_cons.mp hv' with hvHead | hvTail
      · subst v
        exact p.end_mem_tail_support hp.not_nil
      · exact hvTail
    · intro hv
      exact List.mem_of_mem_tail hv
  have hfiniteTail : ({v : α | v ∈ p.support.tail} : Set α).Finite :=
    Set.Finite.ofFinset p.support.tail.toFinset (by intro v; simp)
  rw [hsupport_eq_tail, Set.ncard_eq_toFinset_card _ hfiniteTail]
  have htoFinset : hfiniteTail.toFinset = p.support.tail.toFinset := by
    ext v
    simp
  rw [htoFinset]
  rw [List.toFinset_card_of_nodup hp.support_nodup]
  rw [List.length_tail, SimpleGraph.Walk.length_support]
  omega

lemma simpleCycleSupport_ncard_eq_length {G : MultiGraph V E} {r : G.vertexSet}
    {p : G.toSimpleGraph.Walk r r} (hp : p.IsCycle) :
    (simpleCycleSupport (G := G) p).ncard = p.length := by
  classical
  let f :
      (simpleCycleSupport (G := G) p) ≃
        ({x : G.vertexSet | x ∈ p.support} : Set G.vertexSet) :=
    { toFun := fun v =>
        ⟨⟨v.1, Classical.choose v.2⟩, Classical.choose_spec v.2⟩
      invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      left_inv := by
        intro v
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl }
  have hcard :
      Nat.card (simpleCycleSupport (G := G) p) =
        Nat.card {x : G.vertexSet | x ∈ p.support} := Nat.card_congr f
  have hset :
      ({x : G.vertexSet | x ∈ p.support} : Set G.vertexSet).ncard = p.length :=
    walk_isCycle_support_set_ncard_eq_length (G := G.toSimpleGraph) hp
  simpa using hcard.trans hset

noncomputable def cycleOfSimpleCycle {G : MultiGraph V E} [Finite E] {r : G.vertexSet}
    {p : G.toSimpleGraph.Walk r r} (hp : p.IsCycle) : G.CycleIn where
  support := simpleCycleSupport (G := G) p
  edgeSupport := liftedSimpleCycleEdgeSet (G := G) p
  edgeSupport_finite := liftedSimpleCycleEdgeSet_finite (G := G) p
  edges_inside := by
    classical
    intro e heF
    rcases heF with ⟨q, rfl⟩
    obtain ⟨a, b, hq, hlink⟩ :=
      liftedTreeEdge_spec (G := G) p.toSubgraph.spanningCoe_le q
    refine ⟨liftedTreeEdge_mem (G := G) p.toSubgraph.spanningCoe_le q, ?_⟩
    intro v hv
    have hqEdge : (q : Sym2 G.vertexSet) ∈ p.toSubgraph.edgeSet := by
      simpa using q.2
    have haSupp : a ∈ p.support := by
      apply (p.mem_verts_toSubgraph).mp
      exact p.toSubgraph.mem_verts_of_mem_edge hqEdge (by rw [hq]; simp)
    have hbSupp : b ∈ p.support := by
      apply (p.mem_verts_toSubgraph).mp
      exact p.toSubgraph.mem_verts_of_mem_edge hqEdge (by rw [hq]; simp)
    rcases hv.eq_or_eq_of_isLink hlink with rfl | rfl
    · exact ⟨a.2, haSupp⟩
    · exact ⟨b.2, hbSupp⟩
  support_nonempty := by
    exact ⟨r.1, r.2, p.start_mem_support⟩
  connected := liftedSimpleCycle_connected (G := G) p
  degree_two := by
    intro v hv
    exact liftedSimpleCycle_incidence_card (G := G) hp hv

lemma cycleOfSimpleCycle_support_ncard_eq_length {G : MultiGraph V E} [Finite E]
    {r : G.vertexSet} {p : G.toSimpleGraph.Walk r r} (hp : p.IsCycle) :
    (cycleOfSimpleCycle (G := G) hp).support.ncard = p.length :=
  simpleCycleSupport_ncard_eq_length (G := G) hp

lemma hasOneDisjointCycle_of_simpleCycle {G : MultiGraph V E} [Finite E] {r : G.vertexSet}
    {p : G.toSimpleGraph.Walk r r} (hp : p.IsCycle) :
    G.HasKDisjointCycles 1 := by
  classical
  refine ⟨fun _ : Fin 1 => cycleOfSimpleCycle (G := G) hp, ?_⟩
  intro i j hij
  fin_cases i
  fin_cases j
  exact (hij rfl).elim

private noncomputable def incidentEdgeNeighbor {G : MultiGraph V E}
    (hloopless : G.Loopless) {x : V} (hx : x ∈ G.vertexSet)
    (e : {e : E // G.Incident x e}) :
    G.toSimpleGraph.neighborSet ⟨x, hx⟩ := by
  classical
  let hinc : G.Inc e.1 x := e.2.2
  let y : V := hinc.other
  have hlink : G.IsLink e.1 x y := hinc.isLink_other
  have hne : x ≠ y := isLink_ne_of_loopless (G := G) hloopless hlink
  have hne' : (⟨x, hx⟩ : G.vertexSet) ≠ ⟨y, hlink.right_mem⟩ := by
    intro h
    exact hne (congrArg Subtype.val h)
  exact ⟨⟨y, hlink.right_mem⟩, ⟨hne', e.1, hlink⟩⟩

lemma exists_parallel_edges_of_simple_degree_le_two {G : MultiGraph V E}
    [Finite E] [Fintype G.vertexSet] [DecidableRel G.toSimpleGraph.Adj]
    (hloopless : G.Loopless) {x : V} (hx : x ∈ G.vertexSet)
    (hdeg : G.degree x = 3)
    (hshadow : G.toSimpleGraph.degree ⟨x, hx⟩ ≤ 2) :
    ∃ e f : E, ∃ y : V, e ≠ f ∧ x ≠ y ∧
      G.IsLink e x y ∧ G.IsLink f x y := by
  classical
  have hnotinj :
      ¬ Function.Injective (incidentEdgeNeighbor (G := G) hloopless hx) := by
    intro hinj
    have hcardle :=
      Nat.card_le_card_of_injective (incidentEdgeNeighbor (G := G) hloopless hx) hinj
    have hcardIncident : Nat.card {e : E // G.Incident x e} = 3 := hdeg
    have hcardNeighbor : Nat.card (G.toSimpleGraph.neighborSet ⟨x, hx⟩) ≤ 2 := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
      exact hshadow
    omega
  obtain ⟨a, b, hab, hneab⟩ := Function.not_injective_iff.mp hnotinj
  let y : V := a.2.2.other
  have hlinka : G.IsLink a.1 x y := by
    exact a.2.2.isLink_other
  have hyb : b.2.2.other = y := by
    have h := congrArg (fun z : G.toSimpleGraph.neighborSet ⟨x, hx⟩ => z.1.1) hab
    simpa [incidentEdgeNeighbor, y] using h.symm
  have hlinkb : G.IsLink b.1 x y := by
    simpa [hyb] using b.2.2.isLink_other
  have hneEdges : a.1 ≠ b.1 := by
    intro h
    exact hneab (Subtype.ext h)
  have hxy : x ≠ y := isLink_ne_of_loopless (G := G) hloopless hlinka
  exact ⟨a.1, b.1, y, hneEdges, hxy, hlinka, hlinkb⟩

lemma exists_parallel_edges_of_simple_degree_le_one {G : MultiGraph V E}
    [Finite E] [Fintype G.vertexSet] [DecidableRel G.toSimpleGraph.Adj]
    (hloopless : G.Loopless) {x : V} (hx : x ∈ G.vertexSet)
    (hdeg : G.degree x = 3)
    (hshadow : G.toSimpleGraph.degree ⟨x, hx⟩ ≤ 1) :
    ∃ e f : E, ∃ y : V, e ≠ f ∧ x ≠ y ∧
      G.IsLink e x y ∧ G.IsLink f x y :=
  exists_parallel_edges_of_simple_degree_le_two (G := G) hloopless hx hdeg (by omega)

end MultiGraph

end Chapter02
end Diestel
