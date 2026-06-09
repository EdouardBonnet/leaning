import Chapter01.proposition_1_3_1
import Chapter02.lemma_2_3_1

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

open scoped BigOperators

namespace ErdosPosa

variable {V : Type u} {G : SimpleGraph V}

/-- A convenient explicit Erdős-Pósa bound for the final theorem. -/
noncomputable def bound (k : ℕ) : ℕ :=
  Nat.ceil (erdosPosaS k) + k

/-- The canonical loopless multigraph carried by a simple subgraph. -/
def subgraphMulti (H : G.Subgraph) : MultiGraph V H.edgeSet where
  vertexSet := H.verts
  edgeSet := Set.univ
  IsLink e x y := (e : Sym2 V) = s(x, y)
  isLink_symm := by
    intro e _ x y h
    rw [h]
    exact Sym2.eq_swap
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w hxy hvw
    rw [hxy] at hvw
    rcases Sym2.eq_iff.mp hvw with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · intro _he
      induction e.1 using Sym2.ind with
      | h x y =>
          exact ⟨x, y, rfl⟩
    · intro _h
      simp
  left_mem_of_isLink := by
    intro e x y h
    have he : (e : Sym2 V) ∈ H.edgeSet := e.2
    rw [h] at he
    exact H.edge_vert he

@[simp]
lemma subgraphMulti_vertexSet (H : G.Subgraph) :
    (subgraphMulti H).vertexSet = H.verts := rfl

@[simp]
lemma subgraphMulti_edgeSet (H : G.Subgraph) :
    (subgraphMulti H).edgeSet = Set.univ := rfl

lemma subgraphMulti_isLink_iff {H : G.Subgraph} {e : H.edgeSet} {x y : V} :
    (subgraphMulti H).IsLink e x y ↔ (e : Sym2 V) = s(x, y) := Iff.rfl

lemma subgraphMulti_loopless (H : G.Subgraph) :
    (subgraphMulti H).Loopless := by
  intro e _he x hloop
  have he : (e : Sym2 V) ∈ H.edgeSet := e.2
  rw [subgraphMulti_isLink_iff.mp hloop] at he
  exact H.loopless.irrefl x he

noncomputable def subgraphMultiIncidentEquivIncidenceSet
    (H : G.Subgraph) (v : V) :
    {e : H.edgeSet // (subgraphMulti H).Incident v e} ≃
      H.spanningCoe.incidenceSet v where
  toFun e := by
    rcases e with ⟨⟨e, heH⟩, _heEdge, hinc⟩
    refine ⟨e, ?_⟩
    refine ⟨heH, ?_⟩
    rcases hinc with ⟨w, hw⟩
    have hes : e = s(v, w) := hw
    simp [hes]
  invFun e := by
    refine ⟨⟨e.1, e.2.1⟩, ?_⟩
    refine ⟨by simp, ?_⟩
    rcases e with ⟨e, heH, hev⟩
    induction e using Sym2.ind with
    | h x y =>
        rw [Sym2.mem_iff] at hev
        rcases hev with rfl | rfl
        · exact ⟨y, rfl⟩
        · exact ⟨x, Sym2.eq_swap⟩
  left_inv := by
    intro e
    rcases e with ⟨⟨e, heH⟩, heEdge, hinc⟩
    rcases hinc with ⟨w, hw⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro e
    rcases e with ⟨e, he⟩
    apply Subtype.ext
    rfl

noncomputable def subgraphMultiIncidentEquivNeighborSet
    (H : G.Subgraph) [DecidableEq V] (v : V) :
    {e : H.edgeSet // (subgraphMulti H).Incident v e} ≃ H.neighborSet v :=
  (subgraphMultiIncidentEquivIncidenceSet H v).trans
    ((H.spanningCoe).incidenceSetEquivNeighborSet v)

lemma subgraphMulti_loopSetAt_eq_empty (H : G.Subgraph) (v : V) :
    (subgraphMulti H).loopSetAt v = ∅ := by
  exact MultiGraph.loopSetAt_eq_empty_of_loopless (G := subgraphMulti H)
    (subgraphMulti_loopless H) v

lemma subgraphMulti_diestelDegree_eq
    (H : G.Subgraph) [DecidableEq V] [Finite H.edgeSet] (v : V)
    [Fintype (H.neighborSet v)] :
    (subgraphMulti H).diestelDegree v = H.degree v := by
  classical
  change
    Nat.card {e : H.edgeSet // (subgraphMulti H).Incident v e} +
        Nat.card {e : H.edgeSet // e ∈ (subgraphMulti H).loopSetAt v} =
      H.degree v
  rw [Nat.card_congr (subgraphMultiIncidentEquivNeighborSet H v)]
  have hloop :
      Nat.card {e : H.edgeSet // e ∈ (subgraphMulti H).loopSetAt v} = 0 := by
    simp [subgraphMulti_loopSetAt_eq_empty]
  rw [hloop, add_zero]
  exact Nat.card_eq_fintype_card.trans rfl

/-- The degree of a vertex in a subgraph, stated with `ncard` to avoid local typeclass baggage. -/
noncomputable def subgraphDegree (H : G.Subgraph) (v : V) : ℕ :=
  (H.neighborSet v).ncard

lemma subgraphDegree_eq_degree
    (H : G.Subgraph) (v : V) [Fintype (H.neighborSet v)] :
    subgraphDegree H v = H.degree v := by
  rw [subgraphDegree, Set.ncard_eq_toFinset_card']
  exact SimpleGraph.Subgraph.finset_card_neighborSet_eq_degree

/-- Diestel's maximal auxiliary subgraphs have every vertex of degree two or three. -/
def DegreeTwoOrThreeSubgraph (H : G.Subgraph) : Prop :=
  ∀ v : V, v ∈ H.verts → subgraphDegree H v = 2 ∨ subgraphDegree H v = 3

/-- The degree-three vertices of a 2/3-degree subgraph. -/
def branchSet (H : G.Subgraph) : Set V :=
  {v | v ∈ H.verts ∧ subgraphDegree H v = 3}

lemma subgraphDegree_eq_two_of_mem_not_branch
    {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    {v : V} (hv : v ∈ H.verts) (hvU : v ∉ branchSet H) :
    subgraphDegree H v = 2 := by
  rcases hH v hv with hdeg | hdeg
  · exact hdeg
  · exact (hvU ⟨hv, hdeg⟩).elim

lemma not_exists_strict_degreeTwoOrThreeSubgraph_of_maximal
    {H : G.Subgraph} (hmax : Maximal DegreeTwoOrThreeSubgraph H) :
    ¬ ∃ K : G.Subgraph, H < K ∧ DegreeTwoOrThreeSubgraph K := by
  rw [maximal_iff_forall_gt] at hmax
  rintro ⟨K, hHK, hK⟩
  exact hmax.2 hHK hK

lemma subgraph_neighborSet_eq_empty_of_not_mem_verts
    (H : G.Subgraph) {v : V} (hv : v ∉ H.verts) :
    H.neighborSet v = ∅ := by
  ext w
  constructor
  · intro h
    exact (hv (H.edge_vert h)).elim
  · intro h
    simp at h

lemma walk_toSubgraph_neighborSet_eq_empty_of_not_mem_support
    {x y v : V} (p : G.Walk x y) (hv : v ∉ p.support) :
    p.toSubgraph.neighborSet v = ∅ := by
  ext w
  constructor
  · intro h
    exact (hv (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert h))).elim
  · intro h
    simp at h

/--
An `H`-path in the sense needed in Diestel's proof: its only vertices in
`H` are its two distinct ends, no edge of the path is already an edge of
`H`, and both ends are degree-two vertices of `H`.
-/
def IsCleanHPath (H : G.Subgraph) {x y : V} (p : G.Walk x y) : Prop :=
  p.IsPath ∧
    x ∈ H.verts ∧ y ∈ H.verts ∧ x ≠ y ∧
      (∀ v : V, v ∈ p.support → v ∈ H.verts → v = x ∨ v = y) ∧
        (∀ ⦃a b : V⦄, p.toSubgraph.Adj a b → ¬ H.Adj a b) ∧
          x ∉ branchSet H ∧ y ∉ branchSet H

lemma IsCleanHPath.isPath {H : G.Subgraph} {x y : V}
    {p : G.Walk x y} (hp : IsCleanHPath H p) : p.IsPath :=
  hp.1

lemma IsCleanHPath.left_mem {H : G.Subgraph} {x y : V}
    {p : G.Walk x y} (hp : IsCleanHPath H p) : x ∈ H.verts :=
  hp.2.1

lemma IsCleanHPath.right_mem {H : G.Subgraph} {x y : V}
    {p : G.Walk x y} (hp : IsCleanHPath H p) : y ∈ H.verts :=
  hp.2.2.1

lemma IsCleanHPath.ne {H : G.Subgraph} {x y : V}
    {p : G.Walk x y} (hp : IsCleanHPath H p) : x ≠ y :=
  hp.2.2.2.1

lemma IsCleanHPath.only_ends {H : G.Subgraph} {x y : V}
    {p : G.Walk x y} (hp : IsCleanHPath H p) :
    ∀ v : V, v ∈ p.support → v ∈ H.verts → v = x ∨ v = y :=
  hp.2.2.2.2.1

lemma IsCleanHPath.edge_disjoint {H : G.Subgraph} {x y : V}
    {p : G.Walk x y} (hp : IsCleanHPath H p) :
    ∀ ⦃a b : V⦄, p.toSubgraph.Adj a b → ¬ H.Adj a b :=
  hp.2.2.2.2.2.1

lemma IsCleanHPath.left_not_branch {H : G.Subgraph} {x y : V}
    {p : G.Walk x y} (hp : IsCleanHPath H p) : x ∉ branchSet H :=
  hp.2.2.2.2.2.2.1

lemma IsCleanHPath.right_not_branch {H : G.Subgraph} {x y : V}
    {p : G.Walk x y} (hp : IsCleanHPath H p) : y ∉ branchSet H :=
  hp.2.2.2.2.2.2.2

lemma IsCleanHPath.not_nil {H : G.Subgraph} {x y : V}
    {p : G.Walk x y} (hp : IsCleanHPath H p) : ¬ p.Nil :=
  SimpleGraph.Walk.not_nil_of_ne hp.ne

lemma IsCleanHPath.lt_sup_toSubgraph {H : G.Subgraph} {x y : V}
    {p : G.Walk x y} (hp : IsCleanHPath H p) :
    H < H ⊔ p.toSubgraph := by
  refine lt_of_le_of_ne le_sup_left ?_
  intro hEq
  have hP_le_H : p.toSubgraph ≤ H := by
    rw [hEq]
    exact le_sup_right
  have hAdjP : p.toSubgraph.Adj x p.snd :=
    p.toSubgraph_adj_snd hp.not_nil
  exact hp.edge_disjoint hAdjP (hP_le_H.2 hAdjP)

lemma IsCleanHPath.subgraphDegree_sup_left_eq_three
    {H : G.Subgraph} {x y : V} {p : G.Walk x y}
    (hH : DegreeTwoOrThreeSubgraph H) (hp : IsCleanHPath H p) :
    subgraphDegree (H ⊔ p.toSubgraph) x = 3 := by
  classical
  have hdegH : subgraphDegree H x = 2 :=
    subgraphDegree_eq_two_of_mem_not_branch hH hp.left_mem hp.left_not_branch
  have hHfin : (H.neighborSet x).Finite := by
    apply Set.finite_of_ncard_pos
    have hxcard : (H.neighborSet x).ncard = 2 := by
      simpa [subgraphDegree] using hdegH
    omega
  have hdisj : Disjoint (H.neighborSet x) ({p.snd} : Set V) := by
    rw [Set.disjoint_left]
    intro w hwH hwP
    rw [Set.mem_singleton_iff] at hwP
    subst w
    exact hp.edge_disjoint (p.toSubgraph_adj_snd hp.not_nil) hwH
  rw [subgraphDegree, SimpleGraph.Subgraph.neighborSet_sup,
    hp.isPath.neighborSet_toSubgraph_startpoint hp.not_nil]
  rw [Set.ncard_union_eq hdisj hHfin (Set.finite_singleton p.snd)]
  simpa [subgraphDegree, hdegH]

lemma IsCleanHPath.subgraphDegree_sup_right_eq_three
    {H : G.Subgraph} {x y : V} {p : G.Walk x y}
    (hH : DegreeTwoOrThreeSubgraph H) (hp : IsCleanHPath H p) :
    subgraphDegree (H ⊔ p.toSubgraph) y = 3 := by
  classical
  have hdegH : subgraphDegree H y = 2 :=
    subgraphDegree_eq_two_of_mem_not_branch hH hp.right_mem hp.right_not_branch
  have hHfin : (H.neighborSet y).Finite := by
    apply Set.finite_of_ncard_pos
    have hycard : (H.neighborSet y).ncard = 2 := by
      simpa [subgraphDegree] using hdegH
    omega
  have hdisj : Disjoint (H.neighborSet y) ({p.penultimate} : Set V) := by
    rw [Set.disjoint_left]
    intro w hwH hwP
    rw [Set.mem_singleton_iff] at hwP
    subst w
    exact hp.edge_disjoint (p.toSubgraph_adj_penultimate hp.not_nil) hwH.symm
  rw [subgraphDegree, SimpleGraph.Subgraph.neighborSet_sup,
    hp.isPath.neighborSet_toSubgraph_endpoint hp.not_nil]
  rw [Set.ncard_union_eq hdisj hHfin (Set.finite_singleton p.penultimate)]
  simpa [subgraphDegree, hdegH]

lemma IsCleanHPath.subgraphDegree_sup_eq_left_of_mem_H_not_endpoint
    {H : G.Subgraph} {x y v : V} {p : G.Walk x y}
    (hp : IsCleanHPath H p) (hvH : v ∈ H.verts)
    (hvx : v ≠ x) (hvy : v ≠ y) :
    subgraphDegree (H ⊔ p.toSubgraph) v = subgraphDegree H v := by
  have hvNotSupp : v ∉ p.support := by
    intro hvSupp
    rcases hp.only_ends v hvSupp hvH with h | h
    · exact hvx h
    · exact hvy h
  simp [subgraphDegree, walk_toSubgraph_neighborSet_eq_empty_of_not_mem_support p hvNotSupp]

lemma IsCleanHPath.subgraphDegree_sup_eq_two_of_not_mem_H
    {H : G.Subgraph} {x y v : V} {p : G.Walk x y}
    (hp : IsCleanHPath H p) (hvH : v ∉ H.verts) (hvSupp : v ∈ p.support) :
    subgraphDegree (H ⊔ p.toSubgraph) v = 2 := by
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvSupp with
    ⟨i, rfl, hi_le⟩
  have hi_ne_zero : i ≠ 0 := by
    intro hi
    apply hvH
    simpa [hi] using hp.left_mem
  have hi_ne_length : i ≠ p.length := by
    intro hi
    apply hvH
    simpa [hi] using hp.right_mem
  have hi_lt : i < p.length := by omega
  have hHempty :
      H.neighborSet (p.getVert i) = ∅ :=
    subgraph_neighborSet_eq_empty_of_not_mem_verts H hvH
  rw [subgraphDegree, SimpleGraph.Subgraph.neighborSet_sup, hHempty]
  simpa using
    hp.isPath.ncard_neighborSet_toSubgraph_internal_eq_two hi_ne_zero hi_lt

lemma IsCleanHPath.degreeTwoOrThree_sup_toSubgraph
    {H : G.Subgraph} {x y : V} {p : G.Walk x y}
    (hH : DegreeTwoOrThreeSubgraph H) (hp : IsCleanHPath H p) :
    DegreeTwoOrThreeSubgraph (H ⊔ p.toSubgraph) := by
  intro v hv
  rw [SimpleGraph.Subgraph.verts_sup] at hv
  by_cases hvH : v ∈ H.verts
  · by_cases hvx : v = x
    · subst v
      exact Or.inr (hp.subgraphDegree_sup_left_eq_three hH)
    · by_cases hvy : v = y
      · subst v
        exact Or.inr (hp.subgraphDegree_sup_right_eq_three hH)
      · have hdeg :
            subgraphDegree (H ⊔ p.toSubgraph) v = subgraphDegree H v :=
          hp.subgraphDegree_sup_eq_left_of_mem_H_not_endpoint hvH hvx hvy
        rcases hH v hvH with htwo | hthree
        · exact Or.inl (hdeg.trans htwo)
        · exact Or.inr (hdeg.trans hthree)
  · rcases hv with hvH' | hvP
    · exact (hvH hvH').elim
    · have hvSupp : v ∈ p.support := p.mem_verts_toSubgraph.mp hvP
      exact Or.inl (hp.subgraphDegree_sup_eq_two_of_not_mem_H hvH hvSupp)

lemma IsCleanHPath.exists_strict_degreeTwoOrThree_extension
    {H : G.Subgraph} {x y : V} {p : G.Walk x y}
    (hH : DegreeTwoOrThreeSubgraph H) (hp : IsCleanHPath H p) :
    ∃ K : G.Subgraph, H < K ∧ DegreeTwoOrThreeSubgraph K :=
  ⟨H ⊔ p.toSubgraph, hp.lt_sup_toSubgraph,
    hp.degreeTwoOrThree_sup_toSubgraph hH⟩

lemma no_cleanHPath_of_maximal
    {H : G.Subgraph} (hmax : Maximal DegreeTwoOrThreeSubgraph H)
    {x y : V} {p : G.Walk x y} :
    ¬ IsCleanHPath H p := by
  intro hp
  exact not_exists_strict_degreeTwoOrThreeSubgraph_of_maximal hmax
    (hp.exists_strict_degreeTwoOrThree_extension hmax.1)

lemma one_edge_cleanHPath
    {H : G.Subgraph} {x y : V} (hxy : G.Adj x y)
    (hxH : x ∈ H.verts) (hyH : y ∈ H.verts) (hxy_notH : ¬ H.Adj x y)
    (hxB : x ∉ branchSet H) (hyB : y ∉ branchSet H) :
    IsCleanHPath H (hxy.toWalk) := by
  classical
  have hxy_ne : x ≠ y := hxy.ne
  refine ⟨?_, hxH, hyH, hxy_ne, ?_, ?_, hxB, hyB⟩
  · rw [SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨SimpleGraph.Walk.IsPath.nil, by simp [hxy.ne]⟩
  · intro v hv hvH
    simp [SimpleGraph.Adj.toWalk] at hv
    rcases hv with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro b c hbc hHbc
    have hbc' : (G.subgraphOfAdj hxy).Adj b c := by
      simpa [SimpleGraph.Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
        using hbc
    simp only [SimpleGraph.subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, Prod.swap_prod_mk] at hbc'
    rcases hbc' with hbc' | hbc'
    · exact hxy_notH (by simpa [hbc'.1, hbc'.2] using hHbc)
    · exact hxy_notH (by
        have hHxy : H.Adj y x := by simpa [hbc'.1, hbc'.2] using hHbc
        exact hHxy.symm)

lemma mapped_subgraph_walk_toSubgraph_le
    (K : G.Subgraph) {x y : K.verts} (p : K.coe.Walk x y) :
    (p.map K.hom).toSubgraph ≤ K := by
  induction p with
  | nil =>
      simpa using (SimpleGraph.Subgraph.singletonSubgraph_le_iff x.1 K).mpr x.2
  | cons h p ih =>
      rw [SimpleGraph.Walk.map_cons, SimpleGraph.Walk.toSubgraph]
      exact sup_le
        (SimpleGraph.subgraphOfAdj_le_of_adj K h)
        ih

lemma mapped_subgraph_walk_support_subset_verts'
    (K : G.Subgraph) {x y : K.verts} (p : K.coe.Walk x y) :
    ∀ ⦃v : V⦄, v ∈ (p.map K.hom).support → v ∈ K.verts := by
  intro v hv
  rw [SimpleGraph.Walk.support_map] at hv
  rcases List.mem_map.mp hv with ⟨w, _hw, rfl⟩
  exact w.2

lemma cycle_toSubgraph_verts (C : CycleIn G) :
    C.walk.toSubgraph.verts = C.support := by
  ext v
  exact C.walk.mem_verts_toSubgraph

def CycleIn.reverse (C : CycleIn G) : CycleIn G where
  root := C.root
  walk := C.walk.reverse
  isCycle := C.isCycle.reverse

lemma CycleIn.reverse_support (C : CycleIn G) :
    (CycleIn.reverse C).support = C.support := by
  ext v
  simp [CycleIn.reverse, CycleIn.support, SimpleGraph.Walk.support_reverse]

lemma CycleIn.exists_strict_degreeTwoOrThree_extension_of_disjoint_verts
    {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H) (C : CycleIn G)
    (hdisj : Disjoint C.support H.verts) :
    ∃ K : G.Subgraph, H < K ∧ DegreeTwoOrThreeSubgraph K := by
  classical
  let K : G.Subgraph := H ⊔ C.walk.toSubgraph
  have hstrict : H < K := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hEq
    have hrootC : C.root ∈ C.support := C.walk.start_mem_support
    have hrootK : C.root ∈ K.verts := by
      dsimp [K]
      exact Or.inr (C.walk.mem_verts_toSubgraph.mpr hrootC)
    have hrootH : C.root ∈ H.verts := by
      simpa [hEq] using hrootK
    exact Set.disjoint_left.mp hdisj hrootC hrootH
  refine ⟨K, hstrict, ?_⟩
  intro v hvK
  dsimp [K] at hvK ⊢
  rcases hvK with hvH | hvCsub
  · have hvC : v ∉ C.support := by
      intro hvC
      exact Set.disjoint_left.mp hdisj hvC hvH
    have hCempty : C.walk.toSubgraph.neighborSet v = ∅ :=
      walk_toSubgraph_neighborSet_eq_empty_of_not_mem_support C.walk hvC
    rw [subgraphDegree, SimpleGraph.Subgraph.neighborSet_sup, hCempty]
    simpa [subgraphDegree] using hH v hvH
  · have hvC : v ∈ C.support := by
      simpa [cycle_toSubgraph_verts] using hvCsub
    have hvHnot : v ∉ H.verts := by
      intro hvH
      exact Set.disjoint_left.mp hdisj hvC hvH
    have hHempty : H.neighborSet v = ∅ :=
      subgraph_neighborSet_eq_empty_of_not_mem_verts H hvHnot
    rw [subgraphDegree, SimpleGraph.Subgraph.neighborSet_sup, hHempty]
    have hCdeg : (C.walk.toSubgraph.neighborSet v).ncard = 2 :=
      C.isCycle.ncard_neighborSet_toSubgraph_eq_two hvC
    simp [hCdeg]

lemma no_cycle_disjoint_H_of_maximal
    {H : G.Subgraph} (hmax : Maximal DegreeTwoOrThreeSubgraph H)
    (C : CycleIn G) :
    ¬ Disjoint C.support H.verts := by
  intro hdisj
  exact not_exists_strict_degreeTwoOrThreeSubgraph_of_maximal hmax
    (CycleIn.exists_strict_degreeTwoOrThree_extension_of_disjoint_verts
      hmax.1 C hdisj)

lemma cycle_support_inter_H_nonempty_of_maximal
    {H : G.Subgraph} (hmax : Maximal DegreeTwoOrThreeSubgraph H)
    (C : CycleIn G) :
    (C.support ∩ H.verts).Nonempty := by
  by_contra hnone
  have hdisj : Disjoint C.support H.verts := by
    rw [Set.disjoint_left]
    intro v hvC hvH
    exact hnone ⟨v, hvC, hvH⟩
  exact no_cycle_disjoint_H_of_maximal hmax C hdisj

lemma subgraphMulti_branchSet_eq
    (H : G.Subgraph) [DecidableEq V] [Finite H.edgeSet]
    [∀ v : V, Fintype (H.neighborSet v)] :
    {v : V | v ∈ (subgraphMulti H).vertexSet ∧
        (subgraphMulti H).diestelDegree v = 3} = branchSet H := by
  ext v
  simp [branchSet, subgraphDegree_eq_degree, subgraphMulti_diestelDegree_eq]

lemma subgraphMulti_diestelDegree_le_three_of_degreeTwoOrThree
    (H : G.Subgraph) [DecidableEq V] [Finite H.edgeSet]
    [∀ v : V, Fintype (H.neighborSet v)]
    (hH : DegreeTwoOrThreeSubgraph H) :
    ∀ v : V, v ∈ (subgraphMulti H).vertexSet →
      (subgraphMulti H).diestelDegree v ≤ 3 := by
  intro v hv
  rw [subgraphMulti_diestelDegree_eq H v]
  rcases hH v hv with hdeg | hdeg
  · have hdeg' : H.degree v = 2 := by
      rwa [subgraphDegree_eq_degree H v] at hdeg
    omega
  · have hdeg' : H.degree v = 3 := by
      rwa [subgraphDegree_eq_degree H v] at hdeg
    omega

lemma two_le_subgraphMulti_diestelDegree_of_degreeTwoOrThree
    (H : G.Subgraph) [DecidableEq V] [Finite H.edgeSet]
    [∀ v : V, Fintype (H.neighborSet v)]
    (hH : DegreeTwoOrThreeSubgraph H) :
    ∀ v : V, v ∈ (subgraphMulti H).vertexSet →
      2 ≤ (subgraphMulti H).diestelDegree v := by
  intro v hv
  rw [subgraphMulti_diestelDegree_eq H v]
  rcases hH v hv with hdeg | hdeg
  · have hdeg' : H.degree v = 2 := by
      rwa [subgraphDegree_eq_degree H v] at hdeg
    omega
  · have hdeg' : H.degree v = 3 := by
      rwa [subgraphDegree_eq_degree H v] at hdeg
    omega

theorem subgraphMulti_hasKDisjointCycles_of_large_branchSet
    (H : G.Subgraph) [Finite V] [DecidableEq V] [Finite H.edgeSet]
    [∀ v : V, Fintype (H.neighborSet v)]
    (hH : DegreeTwoOrThreeSubgraph H) (k : ℕ) :
    erdosPosaS k < ((branchSet H).ncard : ℝ) →
      (subgraphMulti H).HasKDisjointCycles k := by
  classical
  intro hLarge
  let M : MultiGraph V H.edgeSet := subgraphMulti H
  have hle3 :
      ∀ a : V, a ∈ M.vertexSet → M.diestelDegree a ≤ 3 := by
    simpa [M] using
      subgraphMulti_diestelDegree_le_three_of_degreeTwoOrThree H hH
  have hge2 :
      ∀ a : V, a ∈ M.vertexSet → 2 ≤ M.diestelDegree a := by
    simpa [M] using
      two_le_subgraphMulti_diestelDegree_of_degreeTwoOrThree H hH
  obtain ⟨V', E', hfinV', hfinE', K, hKCubic, hbranch, htransfer⟩ :=
    MultiGraph.Suppression.exists_diestelSuppressedCubicKernel_of_degree_bounds
      (G := M) hle3 hge2
  haveI : Finite V' := hfinV'
  haveI : Finite E' := hfinE'
  have hbranch_eq :
      ({v : V | v ∈ M.vertexSet ∧ M.diestelDegree v = 3}).ncard =
        (branchSet H).ncard := by
    simpa [M] using congrArg Set.ncard (subgraphMulti_branchSet_eq H)
  have hKLarge : erdosPosaS k < (K.vertexSet.ncard : ℝ) := by
    have hle : ((branchSet H).ncard : ℝ) ≤ (K.vertexSet.ncard : ℝ) := by
      exact_mod_cast (by simpa [hbranch_eq] using hbranch)
    exact lt_of_lt_of_le hLarge hle
  have hKpack : K.HasKDisjointDiestelCycles k :=
    MultiGraph.Suppression.lemma_2_3_1_diestel K k hKCubic hKLarge
  have hMpack : M.HasKDisjointDiestelCycles k :=
    htransfer k hKpack
  exact MultiGraph.hasKDisjointCycles_of_hasKDisjointDiestelCycles_of_loopless
    (G := M) (subgraphMulti_loopless H) hMpack

/-- The simple subgraph selected by a cycle in the canonical multigraph of `H`. -/
noncomputable def cycleSubgraph
    (H : G.Subgraph) (C : (subgraphMulti H).CycleIn) : G.Subgraph where
  verts := C.support
  Adj x y := ∃ e : C.edgeSupport, (e.1 : Sym2 V) = s(x, y)
  adj_sub := by
    rintro x y ⟨e, heq⟩
    have hHadj : H.Adj x y := by
      simpa [SimpleGraph.Subgraph.mem_edgeSet, heq] using e.1.2
    exact H.adj_sub hHadj
  edge_vert := by
    rintro x y ⟨e, heq⟩
    have hinside := C.edges_inside e.2
    exact hinside.2 x ⟨y, heq⟩
  symm := by
    rintro x y ⟨e, heq⟩
    exact ⟨e, by rw [heq]; exact Sym2.eq_swap⟩

@[simp]
lemma cycleSubgraph_verts
    (H : G.Subgraph) (C : (subgraphMulti H).CycleIn) :
    (cycleSubgraph H C).verts = C.support := rfl

lemma cycleSubgraph_adj_iff
    {H : G.Subgraph} {C : (subgraphMulti H).CycleIn} {x y : V} :
    (cycleSubgraph H C).Adj x y ↔
      ∃ e : C.edgeSupport, (e.1 : Sym2 V) = s(x, y) := Iff.rfl

noncomputable def cycleSubgraphNeighborEquivIncident
    (H : G.Subgraph) (C : (subgraphMulti H).CycleIn)
    (v : (cycleSubgraph H C).verts) :
    ((cycleSubgraph H C).coe.neighborSet v) ≃
      {e : C.edgeSupport // (subgraphMulti H).Inc e.1 v.1} where
  toFun n := by
    classical
    have hadj : (cycleSubgraph H C).Adj v.1 n.1.1 := n.2
    let e : C.edgeSupport := Classical.choose hadj
    have heq : (e.1 : Sym2 V) = s(v.1, n.1.1) := Classical.choose_spec hadj
    exact ⟨e, ⟨n.1.1, heq⟩⟩
  invFun e := by
    classical
    let y : V := Classical.choose e.2
    have heq : (e.1.1 : Sym2 V) = s(v.1, y) := Classical.choose_spec e.2
    have hyC : y ∈ C.support := by
      have hinside := C.edges_inside e.1.2
      exact hinside.2 y ⟨v.1, by
        change (e.1.1 : Sym2 V) = s(y, v.1)
        exact heq.trans Sym2.eq_swap⟩
    have hadj : (cycleSubgraph H C).Adj v.1 y := ⟨e.1, heq⟩
    exact ⟨⟨y, hyC⟩, hadj⟩
  left_inv n := by
    classical
    have hadj : (cycleSubgraph H C).Adj v.1 n.1.1 := n.2
    let e : C.edgeSupport := Classical.choose hadj
    have heq : (e.1 : Sym2 V) = s(v.1, n.1.1) := Classical.choose_spec hadj
    let hinc : (subgraphMulti H).Inc e.1 v.1 := ⟨n.1.1, heq⟩
    let y : V := Classical.choose hinc
    have hyEq : (e.1 : Sym2 V) = s(v.1, y) := Classical.choose_spec hinc
    have hyn : y = n.1.1 := by
      have hsame : s(v.1, n.1.1) = s(v.1, y) := heq.symm.trans hyEq
      rcases Sym2.eq_iff.mp hsame with h | h
      · exact h.2.symm
      · have hnv : n.1.1 = v.1 := h.2
        exfalso
        have hGadj : G.Adj v.1 n.1.1 := (cycleSubgraph H C).adj_sub n.2
        exact (G.irrefl (v := v.1)) (by simpa [hnv] using hGadj)
    apply Subtype.ext
    apply Subtype.ext
    exact hyn
  right_inv e := by
    classical
    let y : V := Classical.choose e.2
    have heq : (e.1.1 : Sym2 V) = s(v.1, y) := Classical.choose_spec e.2
    have hyC : y ∈ C.support := by
      have hinside := C.edges_inside e.1.2
      exact hinside.2 y ⟨v.1, by
        change (e.1.1 : Sym2 V) = s(y, v.1)
        exact heq.trans Sym2.eq_swap⟩
    let hadj : (cycleSubgraph H C).Adj v.1 y := ⟨e.1, heq⟩
    let f : C.edgeSupport := Classical.choose hadj
    have hfEq : (f.1 : Sym2 V) = s(v.1, y) := Classical.choose_spec hadj
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    exact hfEq.trans heq.symm

lemma cycleSubgraph_coe_neighborSet_natCard_eq_two
    [Finite V] (H : G.Subgraph) (C : (subgraphMulti H).CycleIn)
    (v : (cycleSubgraph H C).verts) :
    Nat.card (((cycleSubgraph H C).coe).neighborSet v) = 2 := by
  classical
  haveI : Finite C.edgeSupport := Set.Finite.to_subtype C.edgeSupport_finite
  rw [Nat.card_congr (cycleSubgraphNeighborEquivIncident H C v)]
  exact C.degree_two v.1 v.2

lemma exists_simpleCycleIn_of_subgraphMulti_cycle
    [Finite V] (H : G.Subgraph) (C : (subgraphMulti H).CycleIn) :
    ∃ D : CycleIn G, D.support ⊆ C.support := by
  classical
  haveI : Fintype (cycleSubgraph H C).verts := Fintype.ofFinite _
  haveI : Nonempty (cycleSubgraph H C).verts := by
    rcases C.support_nonempty with ⟨v, hv⟩
    exact ⟨⟨v, hv⟩⟩
  letI : DecidableRel (cycleSubgraph H C).coe.Adj := Classical.decRel _
  have hmin : 2 ≤ (cycleSubgraph H C).coe.minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    rw [SimpleGraph.neighborFinset_def, Set.toFinset_card]
    rw [Fintype.card_eq_nat_card]
    rw [cycleSubgraph_coe_neighborSet_natCard_eq_two H C v]
  obtain ⟨a, c, hc, _hlen⟩ :=
    (Diestel.Chapter01.proposition_1_3_1 (cycleSubgraph H C).coe).2 hmin
  let cG : G.Walk a.1 a.1 := c.map (cycleSubgraph H C).hom
  have hcG : cG.IsCycle := by
    exact hc.map Subtype.val_injective
  refine ⟨⟨a.1, cG, hcG⟩, ?_⟩
  intro v hv
  change v ∈ (c.map (cycleSubgraph H C).hom).support at hv
  rw [SimpleGraph.Walk.support_map] at hv
  rcases List.mem_map.mp hv with ⟨w, _hw, rfl⟩
  exact w.2

theorem hasKDisjointCycles_of_subgraphMulti_hasKDisjointCycles
    [Finite V] (H : G.Subgraph) {k : ℕ} :
    (subgraphMulti H).HasKDisjointCycles k → HasKDisjointCycles G k := by
  rintro ⟨C, hdisj⟩
  choose D hD using fun i : Fin k =>
    exists_simpleCycleIn_of_subgraphMulti_cycle H (C i)
  refine ⟨D, ?_⟩
  intro i j hij
  rw [Set.disjoint_left]
  intro v hvi hvj
  exact Set.disjoint_left.mp (hdisj hij) (hD i hvi) (hD j hvj)

theorem hasKDisjointCycles_of_large_branchSet
    (H : G.Subgraph) [Finite V] [DecidableEq V] [Finite H.edgeSet]
    [∀ v : V, Fintype (H.neighborSet v)]
    (hH : DegreeTwoOrThreeSubgraph H) (k : ℕ) :
    erdosPosaS k < ((branchSet H).ncard : ℝ) →
      HasKDisjointCycles G k := by
  intro hLarge
  exact hasKDisjointCycles_of_subgraphMulti_hasKDisjointCycles H
    (subgraphMulti_hasKDisjointCycles_of_large_branchSet H hH k hLarge)

lemma bot_degreeTwoOrThreeSubgraph (G : SimpleGraph V) :
    DegreeTwoOrThreeSubgraph (⊥ : G.Subgraph) := by
  intro v hv
  simp at hv

lemma exists_maximal_degreeTwoOrThreeSubgraph
    (G : SimpleGraph V) [Finite V] :
    ∃ H : G.Subgraph, Maximal DegreeTwoOrThreeSubgraph H := by
  classical
  have hfinite : ({H : G.Subgraph | DegreeTwoOrThreeSubgraph H}).Finite :=
    Set.toFinite _
  have hnonempty :
      ({H : G.Subgraph | DegreeTwoOrThreeSubgraph H}).Nonempty :=
    ⟨⊥, bot_degreeTwoOrThreeSubgraph G⟩
  simpa using hfinite.exists_maximal hnonempty

lemma ncard_le_ceil_erdosPosaS_of_not_large {H : G.Subgraph} {k : ℕ}
    (hnotLarge : ¬ erdosPosaS k < ((branchSet H).ncard : ℝ)) :
    (branchSet H).ncard ≤ Nat.ceil (erdosPosaS k) := by
  have hleR : ((branchSet H).ncard : ℝ) ≤ erdosPosaS k := le_of_not_gt hnotLarge
  exact_mod_cast hleR.trans (Nat.le_ceil (erdosPosaS k))

lemma ncard_union_branchSet_le_bound {H : G.Subgraph} {X : Set V} {k : ℕ}
    (hX : X.ncard ≤ k)
    (hB : (branchSet H).ncard ≤ Nat.ceil (erdosPosaS k)) :
    (X ∪ branchSet H).ncard ≤ bound k := by
  calc
    (X ∪ branchSet H).ncard ≤ X.ncard + (branchSet H).ncard :=
      Set.ncard_union_le X (branchSet H)
    _ ≤ k + Nat.ceil (erdosPosaS k) := Nat.add_le_add hX hB
    _ = bound k := by
      rw [bound, add_comm]

/-- A concrete cycle avoids a vertex set. -/
def CycleAvoids (C : CycleIn G) (S : Set V) : Prop :=
  Disjoint C.support S

/-- A concrete cycle meets a subgraph exactly in the vertex `z`. -/
def CycleMeetsSubgraphExactlyAt (C : CycleIn G) (H : G.Subgraph) (z : V) : Prop :=
  C.support ∩ H.verts = {z}

lemma CycleMeetsSubgraphExactlyAt.mem_eq
    {C : CycleIn G} {H : G.Subgraph} {z v : V}
    (hC : CycleMeetsSubgraphExactlyAt C H z)
    (hvC : v ∈ C.support) (hvH : v ∈ H.verts) :
    v = z := by
  have hv : v ∈ C.support ∩ H.verts := ⟨hvC, hvH⟩
  rw [hC] at hv
  simpa using hv

lemma CycleMeetsSubgraphExactlyAt.center_mem_support
    {C : CycleIn G} {H : G.Subgraph} {z : V}
    (hC : CycleMeetsSubgraphExactlyAt C H z) :
    z ∈ C.support := by
  have hz : z ∈ C.support ∩ H.verts := by
    rw [hC]
    simp
  exact hz.1

lemma CycleMeetsSubgraphExactlyAt.center_mem_verts
    {C : CycleIn G} {H : G.Subgraph} {z : V}
    (hC : CycleMeetsSubgraphExactlyAt C H z) :
    z ∈ H.verts := by
  have hz : z ∈ C.support ∩ H.verts := by
    rw [hC]
    simp
  exact hz.2

lemma exists_cleanHPath_of_cycles_intersect
    {H : G.Subgraph} {C D : CycleIn G} {z w a : V}
    (hCavoid : CycleAvoids C (branchSet H))
    (hDavoid : CycleAvoids D (branchSet H))
    (hCmeet : CycleMeetsSubgraphExactlyAt C H z)
    (hDmeet : CycleMeetsSubgraphExactlyAt D H w)
    (hzw : z ≠ w) (haC : a ∈ C.support) (haD : a ∈ D.support) :
    ∃ p : G.Walk z w, IsCleanHPath H p := by
  classical
  let K : G.Subgraph := C.walk.toSubgraph ⊔ D.walk.toSubgraph
  have hInter : (C.walk.toSubgraph ⊓ D.walk.toSubgraph).verts.Nonempty := by
    refine ⟨a, ?_⟩
    constructor
    · exact C.walk.mem_verts_toSubgraph.mpr haC
    · exact D.walk.mem_verts_toSubgraph.mpr haD
  have hKconn : K.Connected := by
    dsimp [K]
    exact SimpleGraph.Subgraph.connected_sup
      C.walk.toSubgraph_connected.preconnected
      D.walk.toSubgraph_connected.preconnected
      hInter
  have hzK : z ∈ K.verts := by
    change z ∈ (C.walk.toSubgraph ⊔ D.walk.toSubgraph).verts
    rw [SimpleGraph.Subgraph.verts_sup]
    exact Or.inl (C.walk.mem_verts_toSubgraph.mpr hCmeet.center_mem_support)
  have hwK : w ∈ K.verts := by
    change w ∈ (C.walk.toSubgraph ⊔ D.walk.toSubgraph).verts
    rw [SimpleGraph.Subgraph.verts_sup]
    exact Or.inr (D.walk.mem_verts_toSubgraph.mpr hDmeet.center_mem_support)
  let zK : K.verts := ⟨z, hzK⟩
  let wK : K.verts := ⟨w, hwK⟩
  have hreach : K.coe.Reachable zK wK := hKconn zK wK
  obtain ⟨qK, hqKpath⟩ := hreach.exists_isPath
  let qG : G.Walk z w := qK.map K.hom
  refine ⟨qG, ?_⟩
  have hqGpath : qG.IsPath := by
    dsimp [qG]
    exact (SimpleGraph.Walk.map_isPath_iff_of_injective
      (f := K.hom) Subtype.val_injective).mpr hqKpath
  have hqG_le_K : qG.toSubgraph ≤ K := by
    dsimp [qG]
    exact mapped_subgraph_walk_toSubgraph_le K qK
  refine ⟨hqGpath, hCmeet.center_mem_verts, hDmeet.center_mem_verts, hzw, ?_, ?_, ?_, ?_⟩
  · intro v hvq hvH
    have hvK : v ∈ K.verts :=
      mapped_subgraph_walk_support_subset_verts' K qK (by simpa [qG] using hvq)
    change v ∈ (C.walk.toSubgraph ⊔ D.walk.toSubgraph).verts at hvK
    rw [SimpleGraph.Subgraph.verts_sup] at hvK
    rcases hvK with hvC | hvD
    · left
      exact hCmeet.mem_eq (by simpa [cycle_toSubgraph_verts] using hvC) hvH
    · right
      exact hDmeet.mem_eq (by simpa [cycle_toSubgraph_verts] using hvD) hvH
  · intro b c hbc hHbc
    have hKbc : K.Adj b c := hqG_le_K.2 hbc
    change (C.walk.toSubgraph ⊔ D.walk.toSubgraph).Adj b c at hKbc
    rw [SimpleGraph.Subgraph.sup_adj] at hKbc
    rcases hKbc with hCbc | hDbc
    · have hbC : b ∈ C.support := by
        simpa [cycle_toSubgraph_verts] using C.walk.toSubgraph.edge_vert hCbc
      have hcC : c ∈ C.support := by
        simpa [cycle_toSubgraph_verts] using C.walk.toSubgraph.edge_vert hCbc.symm
      have hbH : b ∈ H.verts := H.edge_vert hHbc
      have hcH : c ∈ H.verts := H.edge_vert hHbc.symm
      have hbz : b = z := hCmeet.mem_eq hbC hbH
      have hcz : c = z := hCmeet.mem_eq hcC hcH
      have hbc_eq : b = c := hbz.trans hcz.symm
      exact G.loopless.irrefl b (by simpa [hbc_eq] using H.adj_sub hHbc)
    · have hbD : b ∈ D.support := by
        simpa [cycle_toSubgraph_verts] using D.walk.toSubgraph.edge_vert hDbc
      have hcD : c ∈ D.support := by
        simpa [cycle_toSubgraph_verts] using D.walk.toSubgraph.edge_vert hDbc.symm
      have hbH : b ∈ H.verts := H.edge_vert hHbc
      have hcH : c ∈ H.verts := H.edge_vert hHbc.symm
      have hbw : b = w := hDmeet.mem_eq hbD hbH
      have hcw : c = w := hDmeet.mem_eq hcD hcH
      have hbc_eq : b = c := hbw.trans hcw.symm
      exact G.loopless.irrefl b (by simpa [hbc_eq] using H.adj_sub hHbc)
  · intro hzBranch
    exact Set.disjoint_left.mp hCavoid hCmeet.center_mem_support hzBranch
  · intro hwBranch
    exact Set.disjoint_left.mp hDavoid hDmeet.center_mem_support hwBranch

/--
Diestel's set `Z`: degree-two vertices of `H` that are the unique point where
some cycle avoiding the branch set meets `H`.
-/
def zSet (H : G.Subgraph) : Set V :=
  {z | z ∈ H.verts ∧ z ∉ branchSet H ∧
    ∃ C : CycleIn G,
      CycleAvoids C (branchSet H) ∧ CycleMeetsSubgraphExactlyAt C H z}

lemma zSet_subset_verts (H : G.Subgraph) : zSet H ⊆ H.verts := by
  intro z hz
  exact hz.1

lemma zSet_disjoint_branchSet (H : G.Subgraph) :
    Disjoint (zSet H) (branchSet H) := by
  rw [Set.disjoint_left]
  intro z hz hbranch
  exact hz.2.1 hbranch

/--
The components of `H` that play the role of Diestel's set `D`: components
entirely inside `H`, avoiding both branch vertices and `Z`.
-/
def IsDComponent (H : G.Subgraph)
    (c : H.spanningCoe.ConnectedComponent) : Prop :=
  c.supp ⊆ H.verts ∧ Disjoint c.supp (branchSet H) ∧ Disjoint c.supp (zSet H)

def dComponentSet (H : G.Subgraph) : Set H.spanningCoe.ConnectedComponent :=
  {c | IsDComponent H c}

lemma dComponentSet_component_subset_verts
    {H : G.Subgraph} {c : H.spanningCoe.ConnectedComponent}
    (hc : c ∈ dComponentSet H) :
    c.supp ⊆ H.verts :=
  hc.1

lemma dComponentSet_disjoint_branchSet
    {H : G.Subgraph} {c : H.spanningCoe.ConnectedComponent}
    (hc : c ∈ dComponentSet H) :
    Disjoint c.supp (branchSet H) :=
  hc.2.1

lemma dComponentSet_disjoint_zSet
    {H : G.Subgraph} {c : H.spanningCoe.ConnectedComponent}
    (hc : c ∈ dComponentSet H) :
    Disjoint c.supp (zSet H) :=
  hc.2.2

noncomputable def dComponentRep
    (H : G.Subgraph) (c : dComponentSet H) : V :=
  Classical.choose c.1.nonempty_supp

lemma dComponentRep_mem_supp
    (H : G.Subgraph) (c : dComponentSet H) :
    dComponentRep H c ∈ c.1.supp :=
  Classical.choose_spec c.1.nonempty_supp

lemma dComponentRep_mem_verts
    (H : G.Subgraph) (c : dComponentSet H) :
    dComponentRep H c ∈ H.verts :=
  c.2.1 (dComponentRep_mem_supp H c)

lemma dComponentRep_not_mem_zSet
    (H : G.Subgraph) (c : dComponentSet H) :
    dComponentRep H c ∉ zSet H := by
  intro hz
  exact Set.disjoint_left.mp c.2.2.2 (dComponentRep_mem_supp H c) hz

def dRepSet (H : G.Subgraph) : Set V :=
  {v | ∃ c : dComponentSet H, dComponentRep H c = v}

def xSet (H : G.Subgraph) : Set V :=
  zSet H ∪ dRepSet H

def coverSet (H : G.Subgraph) : Set V :=
  xSet H ∪ branchSet H

lemma dRepSet_subset_verts (H : G.Subgraph) :
    dRepSet H ⊆ H.verts := by
  rintro v ⟨c, rfl⟩
  exact dComponentRep_mem_verts H c

lemma dRepSet_disjoint_zSet (H : G.Subgraph) :
    Disjoint (dRepSet H) (zSet H) := by
  rw [Set.disjoint_left]
  rintro v ⟨c, rfl⟩ hvZ
  exact dComponentRep_not_mem_zSet H c hvZ

lemma dRepSet_ncard_le_dComponentSet_ncard [Finite V] (H : G.Subgraph) :
    (dRepSet H).ncard ≤ (dComponentSet H).ncard := by
  classical
  haveI : Finite (dComponentSet H) := Set.Finite.to_subtype (Set.toFinite _)
  have hEq :
      dRepSet H =
        (fun c : dComponentSet H => dComponentRep H c) '' Set.univ := by
    ext v
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, by simp, rfl⟩
    · rintro ⟨c, _hc, rfl⟩
      exact ⟨c, rfl⟩
  rw [hEq]
  simpa [Set.ncard_univ] using
    (Set.ncard_image_le (f := fun c : dComponentSet H => dComponentRep H c)
      (s := Set.univ))

noncomputable def dComponentNeighborEquiv
    {H : G.Subgraph} {c : H.spanningCoe.ConnectedComponent}
    (hc : c ∈ dComponentSet H) (v : c.supp) :
    c.toSimpleGraph.neighborSet v ≃ H.neighborSet v.1 where
  toFun w := by
    refine ⟨w.1.1, ?_⟩
    have hAdj : H.spanningCoe.Adj v.1 w.1.1 := by
      exact (c.toSimpleGraph_adj v.2 w.1.2).mp w.2
    simpa [SimpleGraph.Subgraph.spanningCoe_adj] using hAdj
  invFun w := by
    have hAdjSpan : H.spanningCoe.Adj v.1 w.1 := by
      exact w.2
    have hwc : w.1 ∈ c.supp :=
      c.mem_supp_of_adj_mem_supp v.2 hAdjSpan
    refine ⟨⟨w.1, hwc⟩, ?_⟩
    exact (c.toSimpleGraph_adj v.2 hwc).mpr hAdjSpan
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

lemma dComponent_toSimpleGraph_isCycles
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    {c : H.spanningCoe.ConnectedComponent} (hc : c ∈ dComponentSet H) :
    c.toSimpleGraph.IsCycles := by
  intro v hvne
  have hvH : v.1 ∈ H.verts := hc.1 v.2
  have hvNotBranch : v.1 ∉ branchSet H := by
    intro hvB
    exact Set.disjoint_left.mp hc.2.1 v.2 hvB
  have hdegH : subgraphDegree H v.1 = 2 :=
    subgraphDegree_eq_two_of_mem_not_branch hH hvH hvNotBranch
  have hcardEq :
      (c.toSimpleGraph.neighborSet v).ncard = (H.neighborSet v.1).ncard :=
    Set.ncard_congr' (dComponentNeighborEquiv hc v)
  have hHcard : (H.neighborSet v.1).ncard = 2 := by
    simpa [subgraphDegree] using hdegH
  exact hcardEq.trans hHcard

lemma dComponentRep_neighborSet_nonempty
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    (c : dComponentSet H) :
    (c.1.toSimpleGraph.neighborSet
      ⟨dComponentRep H c, dComponentRep_mem_supp H c⟩).Nonempty := by
  classical
  have hrepH : dComponentRep H c ∈ H.verts :=
    dComponentRep_mem_verts H c
  have hrepNotBranch : dComponentRep H c ∉ branchSet H := by
    intro hb
    exact Set.disjoint_left.mp c.2.2.1 (dComponentRep_mem_supp H c) hb
  have hdegH : subgraphDegree H (dComponentRep H c) = 2 :=
    subgraphDegree_eq_two_of_mem_not_branch hH hrepH hrepNotBranch
  have hHcard : (H.neighborSet (dComponentRep H c)).ncard = 2 := by
    simpa [subgraphDegree] using hdegH
  have hHnonempty : (H.neighborSet (dComponentRep H c)).Nonempty := by
    exact Set.nonempty_of_ncard_ne_zero (by simp [hHcard])
  rcases hHnonempty with ⟨w, hw⟩
  have hwc : w ∈ c.1.supp := by
    exact c.1.mem_supp_of_adj_mem_supp (dComponentRep_mem_supp H c) hw
  refine ⟨⟨w, hwc⟩, ?_⟩
  exact (c.1.toSimpleGraph_adj (dComponentRep_mem_supp H c) hwc).mpr hw

lemma connectedComponent_supp_eq_univ_of_connected
    {α : Type u} {F : SimpleGraph α} (hF : F.Connected)
    (c : F.ConnectedComponent) :
    c.supp = Set.univ := by
  ext v
  constructor
  · intro _hv
    simp
  · intro _hv
    obtain ⟨r, hr⟩ := c.nonempty_supp
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mpr
      ((SimpleGraph.ConnectedComponent.mem_supp_iff c r).mp hr ▸
        SimpleGraph.ConnectedComponent.sound (hF.preconnected v r))

lemma mem_support_map_connectedComponent_hom_iff
    {α : Type u} {F : SimpleGraph α} (c : F.ConnectedComponent)
    {x y : c.supp} (p : c.toSimpleGraph.Walk x y) {v : α} :
    v ∈ (p.map c.toSimpleGraph_hom).support ↔
      ∃ u : c.supp, u ∈ p.support ∧ u.1 = v := by
  rw [SimpleGraph.Walk.support_map]
  constructor
  · intro hv
    rcases List.mem_map.mp hv with ⟨u, hu, huv⟩
    exact ⟨u, hu, huv⟩
  · rintro ⟨u, hu, huv⟩
    exact List.mem_map.mpr ⟨u, hu, huv⟩

lemma exists_dCycle_support_eq
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    (c : dComponentSet H) :
    ∃ C : CycleIn G, C.support = c.1.supp := by
  classical
  let r : c.1.supp := ⟨dComponentRep H c, dComponentRep_mem_supp H c⟩
  let c0 : c.1.toSimpleGraph.ConnectedComponent :=
    c.1.toSimpleGraph.connectedComponentMk r
  have hcyc : c.1.toSimpleGraph.IsCycles :=
    dComponent_toSimpleGraph_isCycles hH c.2
  have hneigh : (c.1.toSimpleGraph.neighborSet r).Nonempty :=
    dComponentRep_neighborSet_nonempty hH c
  obtain ⟨p, hpcycle, hpverts⟩ :=
    SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (G := c.1.toSimpleGraph) (c := c0) hcyc
      (v := r) (by exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem)
      hneigh
  have hc0supp : c0.supp = Set.univ :=
    connectedComponent_supp_eq_univ_of_connected
      c.1.connected_toSimpleGraph c0
  let pSpan : H.spanningCoe.Walk r.1 r.1 :=
    p.map c.1.toSimpleGraph_hom
  let pG : G.Walk r.1 r.1 :=
    pSpan.mapLe (SimpleGraph.Subgraph.spanningCoe_le H)
  have hpSpanCycle : pSpan.IsCycle := by
    dsimp [pSpan]
    exact hpcycle.map Subtype.val_injective
  have hpGCycle : pG.IsCycle := by
    dsimp [pG]
    exact hpSpanCycle.mapLe (SimpleGraph.Subgraph.spanningCoe_le H)
  refine ⟨⟨r.1, pG, hpGCycle⟩, ?_⟩
  ext v
  constructor
  · intro hv
    change v ∈ pG.support at hv
    dsimp [pG, pSpan] at hv
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
    rcases (mem_support_map_connectedComponent_hom_iff c.1 p).mp hv with
      ⟨y, _hy, rfl⟩
    exact y.2
  · intro hv
    change v ∈ pG.support
    dsimp [pG, pSpan]
    rw [SimpleGraph.Walk.support_mapLe_eq_support]
    let y : c.1.supp := ⟨v, hv⟩
    have hyc0 : y ∈ c0.supp := by
      rw [hc0supp]
      simp
    have hyp : y ∈ p.support := by
      have hyverts : y ∈ p.toSubgraph.verts := by
        rw [hpverts]
        exact hyc0
      exact p.mem_verts_toSubgraph.mp hyverts
    exact (mem_support_map_connectedComponent_hom_iff c.1 p).mpr
      ⟨y, hyp, rfl⟩

/-- The cycle carried by a `D`-component. -/
noncomputable def dCycle
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    (c : dComponentSet H) : CycleIn G :=
  Classical.choose (exists_dCycle_support_eq hH c)

lemma dCycle_support_eq
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    (c : dComponentSet H) :
    (dCycle hH c).support = c.1.supp :=
  Classical.choose_spec (exists_dCycle_support_eq hH c)

lemma dCycle_pairwise_disjoint
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H) :
    Pairwise fun c d : dComponentSet H =>
      Disjoint (dCycle hH c).support (dCycle hH d).support := by
  intro c d hcd
  rw [dCycle_support_eq hH c, dCycle_support_eq hH d]
  exact SimpleGraph.pairwise_disjoint_supp_connectedComponent H.spanningCoe
    (by
      intro h
      exact hcd (Subtype.ext h))

/-- A chosen representative cycle witnessing `z ∈ Z`. -/
noncomputable def zCycle (H : G.Subgraph) (z : zSet H) : CycleIn G :=
  Classical.choose z.2.2.2

lemma zCycle_avoids_branchSet (H : G.Subgraph) (z : zSet H) :
    CycleAvoids (zCycle H z) (branchSet H) :=
  (Classical.choose_spec z.2.2.2).1

lemma zCycle_meets_exactly (H : G.Subgraph) (z : zSet H) :
    CycleMeetsSubgraphExactlyAt (zCycle H z) H z.1 :=
  (Classical.choose_spec z.2.2.2).2

lemma branchSet_subset_coverSet (H : G.Subgraph) :
    branchSet H ⊆ coverSet H := by
  intro v hv
  simp [coverSet, hv]

lemma zSet_subset_coverSet (H : G.Subgraph) :
    zSet H ⊆ coverSet H := by
  intro v hv
  simp [coverSet, xSet, hv]

lemma cycle_avoids_branchSet_of_avoids_coverSet
    {H : G.Subgraph} {C : CycleIn G}
    (havoid : CycleAvoids C (coverSet H)) :
    CycleAvoids C (branchSet H) := by
  unfold CycleAvoids at havoid ⊢
  rw [Set.disjoint_left] at havoid ⊢
  intro v hvC hvB
  exact havoid hvC (branchSet_subset_coverSet H hvB)

lemma not_cycle_meets_H_exactly_one_of_avoids_coverSet
    {H : G.Subgraph} {C : CycleIn G} {z : V}
    (havoid : CycleAvoids C (coverSet H)) :
    ¬ CycleMeetsSubgraphExactlyAt C H z := by
  intro hmeet
  have havoidB : CycleAvoids C (branchSet H) :=
    cycle_avoids_branchSet_of_avoids_coverSet havoid
  have hznotB : z ∉ branchSet H := by
    intro hzB
    exact Set.disjoint_left.mp havoid hmeet.center_mem_support
      (branchSet_subset_coverSet H hzB)
  have hzZ : z ∈ zSet H :=
    ⟨hmeet.center_mem_verts, hznotB, ⟨C, havoidB, hmeet⟩⟩
  exact Set.disjoint_left.mp havoid hmeet.center_mem_support
    (zSet_subset_coverSet H hzZ)

lemma cycle_toSubgraph_neighborSet_eq_of_le_H_of_avoids_branch
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    {C : CycleIn G} (hle : C.walk.toSubgraph ≤ H)
    (havoidB : CycleAvoids C (branchSet H)) {v : V}
    (hvC : v ∈ C.support) :
    C.walk.toSubgraph.neighborSet v = H.neighborSet v := by
  have hvCsub : v ∈ C.walk.toSubgraph.verts :=
    C.walk.mem_verts_toSubgraph.mpr hvC
  have hvH : v ∈ H.verts := hle.1 hvCsub
  have hvNotBranch : v ∉ branchSet H := by
    intro hvB
    exact Set.disjoint_left.mp havoidB hvC hvB
  have hHdeg : subgraphDegree H v = 2 :=
    subgraphDegree_eq_two_of_mem_not_branch hH hvH hvNotBranch
  have hCdeg : (C.walk.toSubgraph.neighborSet v).ncard = 2 :=
    C.isCycle.ncard_neighborSet_toSubgraph_eq_two hvC
  refine Set.eq_of_subset_of_ncard_le
    (SimpleGraph.Subgraph.neighborSet_subset_of_subgraph hle v) ?_
  rw [hCdeg]
  simpa [subgraphDegree] using hHdeg.le

lemma cycle_support_closed_under_H_adj_of_le_H_of_avoids_branch
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    {C : CycleIn G} (hle : C.walk.toSubgraph ≤ H)
    (havoidB : CycleAvoids C (branchSet H)) {v w : V}
    (hvC : v ∈ C.support) (hvw : H.Adj v w) :
    w ∈ C.support := by
  have hEq :=
    cycle_toSubgraph_neighborSet_eq_of_le_H_of_avoids_branch
      hH hle havoidB hvC
  have hwCneigh : w ∈ C.walk.toSubgraph.neighborSet v := by
    rw [hEq]
    exact hvw
  exact C.walk.mem_verts_toSubgraph.mp
    (C.walk.toSubgraph.edge_vert hwCneigh.symm)

lemma H_walk_support_subset_cycle_support_of_cycle_le_H
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    {C : CycleIn G} (hle : C.walk.toSubgraph ≤ H)
    (havoidB : CycleAvoids C (branchSet H))
    {x y : V} (p : H.spanningCoe.Walk x y) (hxC : x ∈ C.support) :
    ∀ ⦃v : V⦄, v ∈ p.support → v ∈ C.support := by
  induction p with
  | nil =>
      intro v hv
      simp at hv
      subst v
      exact hxC
  | cons h p ih =>
      intro v hv
      simp [SimpleGraph.Walk.support_cons] at hv
      rcases hv with rfl | hv
      · exact hxC
      · have hyC : _ ∈ C.support :=
          cycle_support_closed_under_H_adj_of_le_H_of_avoids_branch
            hH hle havoidB hxC h
        exact ih hyC hv

lemma component_supp_subset_cycle_support_of_cycle_le_H
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    {C : CycleIn G} (hle : C.walk.toSubgraph ≤ H)
    (havoidB : CycleAvoids C (branchSet H)) :
    (H.spanningCoe.connectedComponentMk C.root).supp ⊆ C.support := by
  intro v hv
  have hroot :
      C.root ∈ (H.spanningCoe.connectedComponentMk C.root).supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hreach :
      H.spanningCoe.Reachable C.root v :=
    (H.spanningCoe.connectedComponentMk C.root).reachable_of_mem_supp hroot hv
  rcases hreach with ⟨p⟩
  exact H_walk_support_subset_cycle_support_of_cycle_le_H
    hH hle havoidB p C.walk.start_mem_support p.end_mem_support

lemma cycle_avoiding_cover_not_le_H_of_maximal
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    {C : CycleIn G} (havoid : CycleAvoids C (coverSet H)) :
    ¬ C.walk.toSubgraph ≤ H := by
  intro hle
  let c : H.spanningCoe.ConnectedComponent :=
    H.spanningCoe.connectedComponentMk C.root
  have havoidB : CycleAvoids C (branchSet H) :=
    cycle_avoids_branchSet_of_avoids_coverSet havoid
  have hc_subset_C : c.supp ⊆ C.support :=
    component_supp_subset_cycle_support_of_cycle_le_H hH hle havoidB
  have hC_subset_H : C.support ⊆ H.verts := by
    intro v hv
    exact hle.1 (C.walk.mem_verts_toSubgraph.mpr hv)
  have hcD : c ∈ dComponentSet H := by
    refine ⟨?_, ?_, ?_⟩
    · exact fun v hv => hC_subset_H (hc_subset_C hv)
    · rw [Set.disjoint_left]
      intro v hvc hvB
      exact Set.disjoint_left.mp havoidB (hc_subset_C hvc) hvB
    · rw [Set.disjoint_left]
      intro v hvc hvZ
      exact Set.disjoint_left.mp havoid (hc_subset_C hvc)
        (zSet_subset_coverSet H hvZ)
  let d : dComponentSet H := ⟨c, hcD⟩
  have hdC : dComponentRep H d ∈ C.support :=
    hc_subset_C (dComponentRep_mem_supp H d)
  exact Set.disjoint_left.mp havoid hdC
    (by
      apply Or.inl
      apply Or.inr
      exact ⟨d, rfl⟩)

lemma exists_cleanHPath_of_cycle_support_subset_H_not_le_H
    {H : G.Subgraph} {C : CycleIn G}
    (havoid : CycleAvoids C (coverSet H))
    (hsub : C.support ⊆ H.verts)
    (hnotle : ¬ C.walk.toSubgraph ≤ H) :
    ∃ x y : V, ∃ p : G.Walk x y, IsCleanHPath H p := by
  classical
  have hExists :
      ∃ x y : V, C.walk.toSubgraph.Adj x y ∧ ¬ H.Adj x y := by
    by_contra hnone
    apply hnotle
    constructor
    · intro v hv
      exact hsub (by simpa [cycle_toSubgraph_verts] using hv)
    · intro x y hxy
      by_contra hxyH
      exact hnone ⟨x, y, hxy, hxyH⟩
  rcases hExists with ⟨x, y, hxyC, hxyH⟩
  have hxC : x ∈ C.support := by
    simpa [cycle_toSubgraph_verts] using C.walk.toSubgraph.edge_vert hxyC
  have hyC : y ∈ C.support := by
    simpa [cycle_toSubgraph_verts] using C.walk.toSubgraph.edge_vert hxyC.symm
  have hxH : x ∈ H.verts := hsub hxC
  have hyH : y ∈ H.verts := hsub hyC
  have havoidB : CycleAvoids C (branchSet H) :=
    cycle_avoids_branchSet_of_avoids_coverSet havoid
  have hxB : x ∉ branchSet H := by
    intro hxB
    exact Set.disjoint_left.mp havoidB hxC hxB
  have hyB : y ∉ branchSet H := by
    intro hyB
    exact Set.disjoint_left.mp havoidB hyC hyB
  exact ⟨x, y, (C.walk.toSubgraph.adj_sub hxyC).toWalk,
    one_edge_cleanHPath (C.walk.toSubgraph.adj_sub hxyC)
      hxH hyH hxyH hxB hyB⟩

lemma exists_first_H_on_rotated_cycle
    [Finite V] [DecidableEq V] {H : G.Subgraph} {C : CycleIn G}
    {a : V} (haC : a ∈ C.support)
    (hInter : (C.support ∩ H.verts).Nonempty) :
    ∃ x : V, ∃ hxC : x ∈ C.support, ∃ hxH : x ∈ H.verts,
      ∃ hxRot : x ∈ (C.walk.rotate a haC).support,
        ∀ ⦃v : V⦄, v ∈ C.support → v ∈ H.verts →
          v ∈ ((C.walk.rotate a haC).takeUntil x hxRot).support → v = x := by
  classical
  haveI : Fintype (C.support ∩ H.verts : Set V) := Fintype.ofFinite _
  let S : Finset V := (C.support ∩ H.verts : Set V).toFinset
  have hSnon :
      {x ∈ S | x ∈ (C.walk.rotate a haC).support}.Nonempty := by
    rcases hInter with ⟨z, hzC, hzH⟩
    have hzRot : z ∈ (C.walk.rotate a haC).support := by
      rw [SimpleGraph.Walk.mem_support_rotate_iff]
      change z ∈ C.walk.support at hzC
      exact hzC
    refine ⟨z, ?_⟩
    rw [Finset.mem_filter]
    constructor
    · dsimp [S]
      simpa using (show z ∈ C.support ∩ H.verts from ⟨hzC, hzH⟩)
    · exact hzRot
  obtain ⟨x, hxS, hxRot, hfirst⟩ :=
    (C.walk.rotate a haC).exists_mem_support_forall_mem_support_imp_eq S hSnon
  have hxSet : x ∈ C.support ∩ H.verts := by
    simpa [S] using hxS
  have hxC : x ∈ C.support := by
    exact hxSet.1
  have hxH : x ∈ H.verts := by
    exact hxSet.2
  refine ⟨x, hxC, hxH, hxRot, ?_⟩
  intro v hvC hvH hvTake
  have hvS : v ∈ S := by
    dsimp [S]
    simpa using (show v ∈ C.support ∩ H.verts from ⟨hvC, hvH⟩)
  exact hfirst v hvS hvTake

lemma cycle_meets_exactly_at_of_unique_H_vertex
    {H : G.Subgraph} {C : CycleIn G} {z : V}
    (hzC : z ∈ C.support) (hzH : z ∈ H.verts)
    (huniq : ∀ ⦃v : V⦄, v ∈ C.support → v ∈ H.verts → v = z) :
    CycleMeetsSubgraphExactlyAt C H z := by
  ext v
  constructor
  · intro hv
    rw [Set.mem_singleton_iff]
    exact huniq hv.1 hv.2
  · intro hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    exact ⟨hzC, hzH⟩

lemma exists_second_H_vertex_of_not_meets_exactly
    {H : G.Subgraph} {C : CycleIn G} {z : V}
    (hzC : z ∈ C.support) (hzH : z ∈ H.verts)
    (hnot : ¬ CycleMeetsSubgraphExactlyAt C H z) :
    ∃ y : V, y ∈ C.support ∧ y ∈ H.verts ∧ y ≠ z := by
  by_contra hnone
  apply hnot
  exact cycle_meets_exactly_at_of_unique_H_vertex hzC hzH (by
    intro v hvC hvH
    by_contra hvz
    exact hnone ⟨v, hvC, hvH, hvz⟩)

lemma exists_first_H_on_walk
    [Finite V] [DecidableEq V] {H : G.Subgraph} {x y : V}
    (p : G.Walk x y)
    (hInter : ∃ z : V, z ∈ p.support ∧ z ∈ H.verts) :
    ∃ z : V, ∃ hzP : z ∈ p.support, ∃ hzH : z ∈ H.verts,
      ∀ ⦃v : V⦄, v ∈ p.support → v ∈ H.verts →
        v ∈ (p.takeUntil z hzP).support → v = z := by
  classical
  let S : Finset V := p.support.toFinset.filter fun v => v ∈ H.verts
  have hSnon :
      {z ∈ S | z ∈ p.support}.Nonempty := by
    rcases hInter with ⟨z, hzP, hzH⟩
    refine ⟨z, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨by simp [S, hzP, hzH], hzP⟩
  obtain ⟨z, hzS, hzP, hfirst⟩ :=
    p.exists_mem_support_forall_mem_support_imp_eq S hSnon
  have hzH : z ∈ H.verts := by
    have hzSet : z ∈ p.support ∧ z ∈ H.verts := by
      simpa [S] using hzS
    exact hzSet.2
  refine ⟨z, hzP, hzH, ?_⟩
  intro v hvP hvH hvTake
  have hvS : v ∈ S := by
    simp [S, hvP, hvH]
  exact hfirst v hvS hvTake

lemma takeUntil_end_eq_self_of_isPath
    [DecidableEq V] {x y : V} {p : G.Walk x y} (hp : p.IsPath) :
    p.takeUntil y p.end_mem_support = p := by
  apply SimpleGraph.Walk.ext_support
  rw [SimpleGraph.Walk.takeUntil_eq_take]
  simp only [SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.take_support_eq_support_take_succ]
  have hyLast : p.support.getLast (by simp) = y := p.getLast_support
  have hyNotDrop : y ∉ p.support.dropLast := by
    intro hy
    have hrel := hp.support_nodup.rel_dropLast_getLast hy
    simpa [hyLast] using hrel
  have hidx : p.support.idxOf y = p.support.length - 1 := by
    simpa [hyLast] using List.idxOf_getLast (l := p.support) (by simp) (by
      simpa [hyLast] using hyNotDrop)
  rw [hidx]
  have hlen : p.support.length - 1 + 1 = p.support.length := by
    have hpos : 0 < p.support.length := by simp
    omega
  rw [hlen, List.take_length]

lemma exists_cleanHPath_of_cycle_support_not_subset_H
    [Finite V] [DecidableEq V] {H : G.Subgraph} {C : CycleIn G}
    (havoid : CycleAvoids C (coverSet H))
    (hInter : (C.support ∩ H.verts).Nonempty)
    (hnotSub : ¬ C.support ⊆ H.verts) :
    ∃ x y : V, ∃ p : G.Walk x y, IsCleanHPath H p := by
  classical
  have hOutside : ∃ a : V, a ∈ C.support ∧ a ∉ H.verts := by
    by_contra hnone
    apply hnotSub
    intro v hvC
    by_contra hvH
    exact hnone ⟨v, hvC, hvH⟩
  obtain ⟨a, haC, haH⟩ := hOutside
  let R : G.Walk a a := C.walk.rotate a haC
  have hRcycle : R.IsCycle := by
    dsimp [R]
    exact C.isCycle.rotate haC
  have hR_support : ∀ ⦃v : V⦄, v ∈ R.support ↔ v ∈ C.support := by
    intro v
    dsimp [R]
    rw [SimpleGraph.Walk.mem_support_rotate_iff]
    rfl
  have hRInter : ∃ z : V, z ∈ R.support ∧ z ∈ H.verts := by
    rcases hInter with ⟨z, hzC, hzH⟩
    exact ⟨z, hR_support.mpr hzC, hzH⟩
  obtain ⟨x, hxR, hxH, hfirstX⟩ :=
    exists_first_H_on_walk (H := H) R hRInter
  have hxC : x ∈ C.support := hR_support.mp hxR
  have hnotExact : ¬ CycleMeetsSubgraphExactlyAt C H x :=
    not_cycle_meets_H_exactly_one_of_avoids_coverSet havoid
  obtain ⟨y0, hy0C, hy0H, hy0_ne_x⟩ :=
    exists_second_H_vertex_of_not_meets_exactly hxC hxH hnotExact
  have hy0R : y0 ∈ R.support := hR_support.mpr hy0C
  have hy0_not_pX : y0 ∉ (R.takeUntil x hxR).support := by
    intro hy0p
    exact hy0_ne_x (hfirstX hy0R hy0H hy0p)
  have hy0D : y0 ∈ (R.dropUntil x hxR).support := by
    have hy0Split :
        y0 ∈ (R.takeUntil x hxR).support ∨
          y0 ∈ (R.dropUntil x hxR).support := by
      have hy0Append :
          y0 ∈ ((R.takeUntil x hxR).append (R.dropUntil x hxR)).support := by
        simpa [R.take_spec hxR] using hy0R
      rw [SimpleGraph.Walk.mem_support_append_iff] at hy0Append
      exact hy0Append
    exact hy0Split.resolve_left hy0_not_pX
  let pX : G.Walk a x := R.takeUntil x hxR
  let d : G.Walk x a := R.dropUntil x hxR
  have hax : a ≠ x := by
    intro h
    exact haH (by simpa [h] using hxH)
  have hpX_path : pX.IsPath := by
    dsimp [pX]
    exact hRcycle.isPath_takeUntil hxR
  have hpX_not_nil : ¬ pX.Nil := by
    exact SimpleGraph.Walk.not_nil_of_ne hax
  have hd_path : d.IsPath := by
    dsimp [d, pX] at *
    have hcyc_split : ((R.takeUntil x hxR).append (R.dropUntil x hxR)).IsCycle := by
      simpa [R.take_spec hxR] using hRcycle
    exact hcyc_split.isPath_of_append_right hpX_not_nil
  have hdrev_path : d.reverse.IsPath := hd_path.reverse
  have hy0Drev : y0 ∈ d.reverse.support := by
    dsimp [d]
    rw [SimpleGraph.Walk.support_reverse]
    exact List.mem_reverse.mpr hy0D
  have hxDrev : x ∈ d.reverse.support := d.reverse.end_mem_support
  obtain ⟨y, hyDrev, hyH, hfirstY⟩ :=
    exists_first_H_on_walk (H := H) d.reverse ⟨y0, hy0Drev, hy0H⟩
  have hy_ne_x : y ≠ x := by
    intro hyx
    subst y
    have htake : d.reverse.takeUntil x hyDrev = d.reverse := by
      convert takeUntil_end_eq_self_of_isPath hdrev_path
    have hy0Take : y0 ∈ (d.reverse.takeUntil x hyDrev).support := by
      simpa [htake] using hy0Drev
    exact hy0_ne_x (hfirstY hy0Drev hy0H hy0Take)
  let pY : G.Walk a y := d.reverse.takeUntil y hyDrev
  have hpY_path : pY.IsPath := by
    dsimp [pY]
    exact hdrev_path.takeUntil hyDrev
  let K : G.Subgraph := pX.toSubgraph ⊔ pY.toSubgraph
  have hKconn : K.Connected := by
    dsimp [K]
    apply SimpleGraph.Subgraph.connected_sup
      pX.toSubgraph_connected.preconnected
      pY.toSubgraph_connected.preconnected
    refine ⟨a, ?_⟩
    constructor
    · exact pX.mem_verts_toSubgraph.mpr pX.start_mem_support
    · exact pY.mem_verts_toSubgraph.mpr pY.start_mem_support
  have hxK : x ∈ K.verts := by
    dsimp [K]
    exact Or.inl (pX.mem_verts_toSubgraph.mpr pX.end_mem_support)
  have hyK : y ∈ K.verts := by
    dsimp [K]
    exact Or.inr (pY.mem_verts_toSubgraph.mpr pY.end_mem_support)
  let xK : K.verts := ⟨x, hxK⟩
  let yK : K.verts := ⟨y, hyK⟩
  have hreach : K.coe.Reachable xK yK := hKconn xK yK
  obtain ⟨qK, hqKpath⟩ := hreach.exists_isPath
  let qG : G.Walk x y := qK.map K.hom
  refine ⟨x, y, qG, ?_⟩
  have hqGpath : qG.IsPath := by
    dsimp [qG]
    exact (SimpleGraph.Walk.map_isPath_iff_of_injective
      (f := K.hom) Subtype.val_injective).mpr hqKpath
  have hqG_le_K : qG.toSubgraph ≤ K := by
    dsimp [qG]
    exact mapped_subgraph_walk_toSubgraph_le K qK
  have havoidB : CycleAvoids C (branchSet H) :=
    cycle_avoids_branchSet_of_avoids_coverSet havoid
  have hxNotB : x ∉ branchSet H := by
    intro hxB
    exact Set.disjoint_left.mp havoidB hxC hxB
  have hyC : y ∈ C.support := by
    have hyD : y ∈ d.support := by
      rw [SimpleGraph.Walk.support_reverse] at hyDrev
      exact List.mem_reverse.mp hyDrev
    exact hR_support.mp (R.support_dropUntil_subset hxR hyD)
  have hyNotB : y ∉ branchSet H := by
    intro hyB
    exact Set.disjoint_left.mp havoidB hyC hyB
  refine ⟨hqGpath, hxH, hyH, hy_ne_x.symm, ?_, ?_, hxNotB, hyNotB⟩
  · intro v hvq hvH
    have hvK : v ∈ K.verts :=
      mapped_subgraph_walk_support_subset_verts' K qK (by simpa [qG] using hvq)
    change v ∈ (pX.toSubgraph ⊔ pY.toSubgraph).verts at hvK
    rw [SimpleGraph.Subgraph.verts_sup] at hvK
    rcases hvK with hvPX | hvPY
    · left
      have hvPXsupp : v ∈ pX.support := pX.mem_verts_toSubgraph.mp hvPX
      dsimp [pX] at hvPXsupp
      exact hfirstX (R.support_takeUntil_subset hxR hvPXsupp) hvH hvPXsupp
    · right
      have hvPYsupp : v ∈ pY.support := pY.mem_verts_toSubgraph.mp hvPY
      dsimp [pY] at hvPYsupp
      exact hfirstY (d.reverse.support_takeUntil_subset hyDrev hvPYsupp)
        hvH hvPYsupp
  · intro b c hbc hHbc
    have hKbc : K.Adj b c := hqG_le_K.2 hbc
    change (pX.toSubgraph ⊔ pY.toSubgraph).Adj b c at hKbc
    rw [SimpleGraph.Subgraph.sup_adj] at hKbc
    rcases hKbc with hPXbc | hPYbc
    · have hbPX : b ∈ pX.support :=
        pX.mem_verts_toSubgraph.mp (pX.toSubgraph.edge_vert hPXbc)
      have hcPX : c ∈ pX.support :=
        pX.mem_verts_toSubgraph.mp (pX.toSubgraph.edge_vert hPXbc.symm)
      have hbH : b ∈ H.verts := H.edge_vert hHbc
      have hcH : c ∈ H.verts := H.edge_vert hHbc.symm
      have hbx : b = x := by
        dsimp [pX] at hbPX
        exact hfirstX (R.support_takeUntil_subset hxR hbPX) hbH hbPX
      have hcx : c = x := by
        dsimp [pX] at hcPX
        exact hfirstX (R.support_takeUntil_subset hxR hcPX) hcH hcPX
      have hbc_eq : b = c := hbx.trans hcx.symm
      exact G.loopless.irrefl b (by simpa [hbc_eq] using H.adj_sub hHbc)
    · have hbPY : b ∈ pY.support :=
        pY.mem_verts_toSubgraph.mp (pY.toSubgraph.edge_vert hPYbc)
      have hcPY : c ∈ pY.support :=
        pY.mem_verts_toSubgraph.mp (pY.toSubgraph.edge_vert hPYbc.symm)
      have hbH : b ∈ H.verts := H.edge_vert hHbc
      have hcH : c ∈ H.verts := H.edge_vert hHbc.symm
      have hby : b = y := by
        dsimp [pY] at hbPY
        exact hfirstY (d.reverse.support_takeUntil_subset hyDrev hbPY) hbH hbPY
      have hcy : c = y := by
        dsimp [pY] at hcPY
        exact hfirstY (d.reverse.support_takeUntil_subset hyDrev hcPY) hcH hcPY
      have hbc_eq : b = c := hby.trans hcy.symm
      exact G.loopless.irrefl b (by simpa [hbc_eq] using H.adj_sub hHbc)

lemma zCycle_disjoint_dCycle
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    (z : zSet H) (c : dComponentSet H) :
    Disjoint (zCycle H z).support (dCycle hH c).support := by
  rw [Set.disjoint_left]
  intro v hvz hvd
  have hvd_supp : v ∈ c.1.supp := by
    simpa [dCycle_support_eq hH c] using hvd
  have hvH : v ∈ H.verts :=
    dComponentSet_component_subset_verts c.2 hvd_supp
  have hv_eq_z : v = z.1 :=
    (zCycle_meets_exactly H z).mem_eq hvz hvH
  have hz_supp : z.1 ∈ c.1.supp := by
    simpa [hv_eq_z] using hvd_supp
  exact Set.disjoint_left.mp (dComponentSet_disjoint_zSet c.2) hz_supp z.2

lemma zCycle_pairwise_disjoint_of_maximal
    {H : G.Subgraph} (hmax : Maximal DegreeTwoOrThreeSubgraph H) :
    Pairwise fun z w : zSet H =>
      Disjoint (zCycle H z).support (zCycle H w).support := by
  intro z w hzw
  rw [Set.disjoint_left]
  intro a haZ haW
  have hzw_val : z.1 ≠ w.1 := by
    intro h
    exact hzw (Subtype.ext h)
  obtain ⟨p, hp⟩ :=
    exists_cleanHPath_of_cycles_intersect
      (H := H)
      (C := zCycle H z) (D := zCycle H w)
      (z := z.1) (w := w.1) (a := a)
      (zCycle_avoids_branchSet H z)
      (zCycle_avoids_branchSet H w)
      (zCycle_meets_exactly H z)
      (zCycle_meets_exactly H w)
      hzw_val haZ haW
  exact no_cleanHPath_of_maximal hmax hp

lemma exists_injective_fin_zSet_of_le_ncard
    [Finite V] {H : G.Subgraph} {k : ℕ}
    (hk : k ≤ (zSet H).ncard) :
    ∃ f : Fin k → zSet H, Function.Injective f := by
  classical
  haveI : Fintype (zSet H) := Fintype.ofFinite _
  have hcard_eq : (zSet H).ncard = Fintype.card (zSet H) := by
    rw [Set.ncard_eq_toFinset_card' (zSet H), Set.toFinset_card]
  have hkcard : k ≤ Fintype.card (zSet H) := by
    simpa [hcard_eq] using hk
  let e := Fintype.equivFin (zSet H)
  let f : Fin k → zSet H := fun i =>
    e.symm ⟨i.1, lt_of_lt_of_le i.2 hkcard⟩
  refine ⟨f, ?_⟩
  intro i j hij
  apply Fin.ext
  have hij' := congrArg e hij
  simpa [f, e] using congrArg Fin.val hij'

lemma exists_injective_fin_of_le_natCard
    {α : Type u} [Finite α] {k : ℕ} (hk : k ≤ Nat.card α) :
    ∃ f : Fin k → α, Function.Injective f := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have hkcard : k ≤ Fintype.card α := by
    simpa [Nat.card_eq_fintype_card] using hk
  let e := Fintype.equivFin α
  let f : Fin k → α := fun i =>
    e.symm ⟨i.1, lt_of_lt_of_le i.2 hkcard⟩
  refine ⟨f, ?_⟩
  intro i j hij
  apply Fin.ext
  have hij' := congrArg e hij
  simpa [f, e] using congrArg Fin.val hij'

lemma exists_injective_fin_sum_zSet_dComponentSet_of_le
    [Finite V] {H : G.Subgraph} {k : ℕ}
    (hk : k ≤ (zSet H).ncard + (dComponentSet H).ncard) :
    ∃ f : Fin k → (zSet H ⊕ dComponentSet H), Function.Injective f := by
  classical
  haveI : Finite (zSet H) := Set.Finite.to_subtype (Set.toFinite _)
  haveI : Finite (dComponentSet H) := Set.Finite.to_subtype (Set.toFinite _)
  have hcard :
      Nat.card (zSet H ⊕ dComponentSet H) =
        (zSet H).ncard + (dComponentSet H).ncard := by
    rw [Nat.card_sum, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact exists_injective_fin_of_le_natCard (α := zSet H ⊕ dComponentSet H)
    (by simpa [hcard] using hk)

lemma hasKDisjointCycles_of_le_zSet_add_dComponentSet_ncard
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    (hmax : Maximal DegreeTwoOrThreeSubgraph H) {k : ℕ}
    (hk : k ≤ (zSet H).ncard + (dComponentSet H).ncard) :
    HasKDisjointCycles G k := by
  obtain ⟨f, hf⟩ :=
    exists_injective_fin_sum_zSet_dComponentSet_of_le (H := H) hk
  let C : Fin k → CycleIn G := fun i =>
    match f i with
    | Sum.inl z => zCycle H z
    | Sum.inr c => dCycle hH c
  refine ⟨C, ?_⟩
  intro i j hij
  have hfij : f i ≠ f j := by
    intro h
    exact hij (hf h)
  cases hfi : f i with
  | inl z =>
      cases hfj : f j with
      | inl w =>
          have hzw : z ≠ w := by
            intro h
            exact hfij (by simp [hfi, hfj, h])
          simpa [C, hfi, hfj] using
            zCycle_pairwise_disjoint_of_maximal hmax hzw
      | inr c =>
          simpa [C, hfi, hfj] using zCycle_disjoint_dCycle hH z c
  | inr c =>
      cases hfj : f j with
      | inl z =>
          have hdisj := zCycle_disjoint_dCycle hH z c
          simpa [C, hfi, hfj, disjoint_comm] using hdisj
      | inr d =>
          have hcd : c ≠ d := by
            intro h
            exact hfij (by simp [hfi, hfj, h])
          simpa [C, hfi, hfj] using dCycle_pairwise_disjoint hH hcd

lemma zSet_add_dComponentSet_ncard_lt_of_not_hasKDisjointCycles
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    (hmax : Maximal DegreeTwoOrThreeSubgraph H) {k : ℕ}
    (hnot : ¬ HasKDisjointCycles G k) :
    (zSet H).ncard + (dComponentSet H).ncard < k := by
  exact lt_of_not_ge fun hk =>
    hnot (hasKDisjointCycles_of_le_zSet_add_dComponentSet_ncard
      hH hmax hk)

lemma xSet_ncard_le_of_not_hasKDisjointCycles
    [Finite V] {H : G.Subgraph} (hH : DegreeTwoOrThreeSubgraph H)
    (hmax : Maximal DegreeTwoOrThreeSubgraph H) {k : ℕ}
    (hnot : ¬ HasKDisjointCycles G k) :
    (xSet H).ncard ≤ k := by
  have hsum :
      (zSet H).ncard + (dComponentSet H).ncard < k :=
    zSet_add_dComponentSet_ncard_lt_of_not_hasKDisjointCycles
      hH hmax hnot
  calc
    (xSet H).ncard = (zSet H ∪ dRepSet H).ncard := rfl
    _ ≤ (zSet H).ncard + (dRepSet H).ncard :=
        Set.ncard_union_le (zSet H) (dRepSet H)
    _ ≤ (zSet H).ncard + (dComponentSet H).ncard :=
        Nat.add_le_add_left (dRepSet_ncard_le_dComponentSet_ncard H) _
    _ ≤ k := hsum.le

lemma coverSet_ncard_le_bound
    [Finite V] {H : G.Subgraph} {k : ℕ}
    (hX : (xSet H).ncard ≤ k)
    (hB : (branchSet H).ncard ≤ Nat.ceil (erdosPosaS k)) :
    (coverSet H).ncard ≤ bound k := by
  calc
    (coverSet H).ncard = (xSet H ∪ branchSet H).ncard := rfl
    _ ≤ (xSet H).ncard + (branchSet H).ncard :=
        Set.ncard_union_le (xSet H) (branchSet H)
    _ ≤ k + Nat.ceil (erdosPosaS k) := Nat.add_le_add hX hB
    _ = bound k := by simp [bound, Nat.add_comm]

lemma hasKDisjointCycles_of_le_zSet_ncard
    [Finite V] {H : G.Subgraph}
    (hmax : Maximal DegreeTwoOrThreeSubgraph H) {k : ℕ}
    (hk : k ≤ (zSet H).ncard) :
    HasKDisjointCycles G k := by
  obtain ⟨f, hf⟩ := exists_injective_fin_zSet_of_le_ncard (H := H) hk
  refine ⟨fun i => zCycle H (f i), ?_⟩
  intro i j hij
  exact zCycle_pairwise_disjoint_of_maximal hmax (by
    intro h
    exact hij (hf h))

lemma zSet_ncard_lt_of_not_hasKDisjointCycles
    [Finite V] {H : G.Subgraph}
    (hmax : Maximal DegreeTwoOrThreeSubgraph H) {k : ℕ}
    (hnot : ¬ HasKDisjointCycles G k) :
    (zSet H).ncard < k := by
  exact lt_of_not_ge fun hk =>
    hnot (hasKDisjointCycles_of_le_zSet_ncard hmax hk)

lemma isCycleVertexCover_empty_of_acyclic (G : SimpleGraph V)
    (hG : G.IsAcyclic) :
    IsCycleVertexCover G ∅ := by
  intro C
  exact False.elim (hG C.walk C.isCycle)

lemma isCycleVertexCover_of_no_cycle_avoids
    {U : Set V} (hU : ∀ C : CycleIn G, ¬ CycleAvoids C U) :
    IsCycleVertexCover G U := by
  intro C
  by_contra hnone
  have hdisj : CycleAvoids C U := by
    unfold CycleAvoids
    rw [Set.disjoint_left]
    intro v hvC hvU
    exact hnone ⟨v, hvC, hvU⟩
  exact hU C hdisj

lemma coverSet_isCycleVertexCover_of_maximal
    [Finite V] [DecidableEq V] {H : G.Subgraph}
    (hmax : Maximal DegreeTwoOrThreeSubgraph H) :
    IsCycleVertexCover G (coverSet H) := by
  apply isCycleVertexCover_of_no_cycle_avoids
  intro C havoid
  have hInter : (C.support ∩ H.verts).Nonempty :=
    cycle_support_inter_H_nonempty_of_maximal hmax C
  by_cases hsub : C.support ⊆ H.verts
  · have hnotle : ¬ C.walk.toSubgraph ≤ H :=
      cycle_avoiding_cover_not_le_H_of_maximal hmax.1 havoid
    obtain ⟨x, y, p, hp⟩ :=
      exists_cleanHPath_of_cycle_support_subset_H_not_le_H havoid hsub hnotle
    exact no_cleanHPath_of_maximal hmax hp
  · obtain ⟨x, y, p, hp⟩ :=
      exists_cleanHPath_of_cycle_support_not_subset_H havoid hInter hsub
    exact no_cleanHPath_of_maximal hmax hp

lemma hasKDisjointCycles_zero (G : SimpleGraph V) :
    HasKDisjointCycles G 0 := by
  refine ⟨fun i : Fin 0 => Fin.elim0 i, ?_⟩
  intro i _j _hij
  exact Fin.elim0 i

end ErdosPosa

end Chapter02
end Diestel
