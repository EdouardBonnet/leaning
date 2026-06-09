import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Data.Set.Finite.Basic

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter01

universe u

def supportEdgeSet {V : Type u} (G : SimpleGraph V) (D : EdgeSpace G) :
    Set (Sym2 V) :=
  {e | ∃ he : e ∈ G.edgeSet, D ⟨e, he⟩ = 1}

def supportGraph {V : Type u} (G : SimpleGraph V) (D : EdgeSpace G) :
    SimpleGraph V :=
  SimpleGraph.fromEdgeSet (supportEdgeSet G D)

private lemma supportEdgeSet_not_diag {V : Type u} {G : SimpleGraph V}
    {D : EdgeSpace G} {e : Sym2 V} (he : e ∈ supportEdgeSet G D) :
    ¬ e.IsDiag := by
  rcases he with ⟨heG, _hD⟩
  exact SimpleGraph.not_isDiag_of_mem_edgeSet G heG

theorem supportGraph_edgeSet {V : Type u} (G : SimpleGraph V) (D : EdgeSpace G) :
    (supportGraph G D).edgeSet = supportEdgeSet G D := by
  ext e
  rw [supportGraph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · intro he
    exact he.1
  · intro he
    exact ⟨he, supportEdgeSet_not_diag he⟩

theorem supportGraph_le {V : Type u} (G : SimpleGraph V) (D : EdgeSpace G) :
    supportGraph G D ≤ G := by
  rw [supportGraph, SimpleGraph.fromEdgeSet_le]
  intro e he
  exact he.1.1

private lemma card_incident_edge_subtype_eq_degree {V : Type u} (H : SimpleGraph V)
    [Fintype H.edgeSet] [Fintype V] [DecidableEq V] [DecidableRel H.Adj] (v : V) :
    letI : Fintype (H.neighborSet v) := H.neighborSetFintype v
    Fintype.card {e : H.edgeSet // v ∈ (e : Sym2 V)} = H.degree v := by
  classical
  letI : Fintype (H.neighborSet v) := H.neighborSetFintype v
  let B : Set (Sym2 V) := {e | e ∈ H.edgeSet ∧ v ∈ e}
  letI : Fintype B := Fintype.ofFinset (H.incidenceFinset v) (by
    intro e
    rw [SimpleGraph.incidenceFinset_eq_filter]
    simp [SimpleGraph.mem_edgeFinset, B])
  have hAB :
      Fintype.card {e : H.edgeSet // v ∈ (e : Sym2 V)} = Fintype.card B := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun e => ⟨(e.1 : Sym2 V), e.1.2, e.2⟩
        invFun := fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro e
      rfl
    · intro e
      rfl
  calc
    Fintype.card {e : H.edgeSet // v ∈ (e : Sym2 V)} = Fintype.card B := hAB
    _ = (H.incidenceFinset v).card := Fintype.card_ofFinset (H.incidenceFinset v) (by
      intro e
      rw [SimpleGraph.incidenceFinset_eq_filter]
      simp [SimpleGraph.mem_edgeFinset, B])
    _ = H.degree v := SimpleGraph.card_incidenceFinset_eq_degree H v

/--
The degree of a vertex in the support graph is the number of selected
edges incident with it.
-/
theorem supportGraph_degree_eq {V : Type u} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [Fintype G.edgeSet] (D : EdgeSpace G) (v : V) :
    letI : DecidableRel (supportGraph G D).Adj := Classical.decRel (supportGraph G D).Adj
    letI : Fintype ((supportGraph G D).neighborSet v) :=
      (supportGraph G D).neighborSetFintype v
    (supportGraph G D).degree v =
      Nat.card {e : G.edgeSet // D e = 1 ∧ v ∈ (e : Sym2 V)} := by
  classical
  let H := supportGraph G D
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  letI : Fintype (H.neighborSet v) := H.neighborSetFintype v
  change H.degree v =
      Nat.card {e : G.edgeSet // D e = 1 ∧ v ∈ (e : Sym2 V)}
  have hHedge : H.edgeSet = supportEdgeSet G D := supportGraph_edgeSet G D
  haveI : Fintype H.edgeSet := by
    rw [hHedge]
    exact (Set.Finite.subset (Set.toFinite G.edgeSet) (by
      intro e he
      exact he.1)).fintype
  have hleft :
      H.degree v = Fintype.card {e : H.edgeSet // v ∈ (e : Sym2 V)} := by
    exact (card_incident_edge_subtype_eq_degree H v).symm
  rw [hleft, Nat.card_eq_fintype_card]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun e =>
        let raw : Sym2 V := e.1.1
        have heSupp : raw ∈ supportEdgeSet G D := by
          simpa [raw, hHedge] using e.1.2
        ⟨⟨raw, heSupp.1⟩, heSupp.2, by simpa [raw] using e.2⟩
      invFun := fun e =>
        let raw : Sym2 V := e.1.1
        have heSupp : raw ∈ supportEdgeSet G D := ⟨e.1.2, e.2.1⟩
        have heH : raw ∈ H.edgeSet := by
          simpa [raw, hHedge] using heSupp
        ⟨⟨raw, heH⟩, by simpa [raw] using e.2.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    rfl
  · intro e
    rfl

theorem supportGraph_even_degrees_of_even_incidence {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [Fintype G.edgeSet]
    (D : EdgeSpace G)
    (hD : ∀ v : V, Even (Nat.card {e : G.edgeSet // D e = 1 ∧ v ∈ (e : Sym2 V)})) :
    ∀ v : V,
      letI : DecidableRel (supportGraph G D).Adj := Classical.decRel (supportGraph G D).Adj
      letI : Fintype ((supportGraph G D).neighborSet v) :=
        (supportGraph G D).neighborSetFintype v
      Even ((supportGraph G D).degree v) := by
  intro v
  letI : DecidableRel (supportGraph G D).Adj := Classical.decRel (supportGraph G D).Adj
  letI : Fintype ((supportGraph G D).neighborSet v) :=
    (supportGraph G D).neighborSetFintype v
  rw [supportGraph_degree_eq G D v]
  exact hD v

private lemma used_incident_count_eq_degree {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {u v x : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hall : ∀ e : Sym2 V, e ∈ G.edgeSet → x ∈ e → e ∈ p.edges) :
    p.edges.countP (fun e => x ∈ e) = G.degree x := by
  classical
  have hfin : hp.edgesFinset.filter (fun e : Sym2 V => x ∈ e) = G.incidenceFinset x := by
    ext e
    constructor
    · intro he
      have he' := Finset.mem_filter.mp he
      rw [SimpleGraph.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr
        ⟨(SimpleGraph.mem_edgeFinset).mpr (p.edges_subset_edgeSet he'.1), he'.2⟩
    · intro he
      rw [SimpleGraph.incidenceFinset_eq_filter] at he
      have he' := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr
        ⟨hall e ((SimpleGraph.mem_edgeFinset).mp he'.1) he'.2, he'.2⟩
  rw [← SimpleGraph.card_incidenceFinset_eq_degree G x]
  rw [← hfin]
  rw [List.countP_eq_length_filter]
  rfl

private lemma longest_trail_start_incident_edges_used {V : Type u} (G : SimpleGraph V)
    [DecidableEq V] {u v : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsTrail → p'.length ≤ p.length) :
    ∀ e : Sym2 V, e ∈ G.edgeSet → u ∈ e → e ∈ p.edges := by
  classical
  intro e he hu
  by_contra he_not
  let y := Sym2.Mem.other hu
  have heq : s(u, y) = e := Sym2.other_spec hu
  have hadj : G.Adj u y := by
    rw [← SimpleGraph.mem_edgeSet G]
    exact heq.symm ▸ he
  have hnot : s(y, u) ∉ p.edges := by
    intro hmem
    exact he_not (by simpa [Sym2.eq_swap, heq] using hmem)
  let q : G.Walk y v := p.cons hadj.symm
  have hq : q.IsTrail := by
    dsimp [q]
    rw [SimpleGraph.Walk.isTrail_cons]
    exact ⟨hp, hnot⟩
  have hle := hmax y v q hq
  dsimp [q] at hle
  simp at hle

private lemma longest_trail_closed_of_even_degrees {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsTrail → p'.length ≤ p.length)
    (heven : ∀ x : V, Even (G.degree x)) : u = v := by
  by_contra huv_eq
  have huv : u ≠ v := huv_eq
  have hall := longest_trail_start_incident_edges_used G hp hmax
  have hcount := used_incident_count_eq_degree G hp hall
  have hcount_even : Even (p.edges.countP (fun e => u ∈ e)) := by
    rw [hcount]
    exact heven u
  have hpar := (SimpleGraph.Walk.IsTrail.even_countP_edges_iff hp u).mp hcount_even
  exact hpar huv |>.1 rfl

theorem supportGraph_exists_cycle_of_nonzero_even {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [Fintype G.edgeSet]
    (D : EdgeSpace G)
    (hnonzero : ∃ e : G.edgeSet, D e = 1)
    (hD : ∀ v : V, Even (Nat.card {e : G.edgeSet // D e = 1 ∧ v ∈ (e : Sym2 V)})) :
    letI : DecidableRel (supportGraph G D).Adj := Classical.decRel (supportGraph G D).Adj
    ∃ a : V, ∃ c : (supportGraph G D).Walk a a, c.IsCycle := by
  classical
  let H := supportGraph G D
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hHedge : H.edgeSet = supportEdgeSet G D := supportGraph_edgeSet G D
  haveI : Fintype H.edgeSet := by
    rw [hHedge]
    exact (Set.Finite.subset (Set.toFinite G.edgeSet) (by
      intro e he
      exact he.1)).fintype
  haveI : Nonempty V := by
    rcases hnonzero with ⟨e, _heD⟩
    exact ⟨e.1.out.1⟩
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isTrail_forall_isTrail_length_le_length H
  have hp_pos : 0 < p.length := by
    rcases hnonzero with ⟨e, heD⟩
    obtain ⟨raw, heG⟩ := e
    induction raw using Sym2.inductionOn with
    | hf x y =>
        have heH : s(x, y) ∈ H.edgeSet := by
          rw [hHedge]
          exact ⟨heG, heD⟩
        have hadj : H.Adj x y := (SimpleGraph.mem_edgeSet H).mp heH
        let q : H.Walk x y := (SimpleGraph.Walk.nil : H.Walk y y).cons hadj
        have hq : q.IsTrail := by
          dsimp [q]
          rw [SimpleGraph.Walk.isTrail_cons]
          constructor
          · simp [SimpleGraph.Walk.isTrail_def]
          · simp
        have hle := hmax x y q hq
        have hq_len : q.length = 1 := by
          simp [q]
        rw [hq_len] at hle
        omega
  have hevenH : ∀ x : V, Even (H.degree x) := by
    intro x
    letI : Fintype (H.neighborSet x) := H.neighborSetFintype x
    change Even ((supportGraph G D).degree x)
    exact supportGraph_even_degrees_of_even_incidence G D hD x
  have hclosed := longest_trail_closed_of_even_degrees H hp hmax hevenH
  subst v
  have hne_nil : p ≠ SimpleGraph.Walk.nil := by
    intro hpnil
    subst p
    simp at hp_pos
  exact ⟨u, p.cycleBypass, SimpleGraph.Walk.IsTrail.isCycle_cycleBypass hne_nil hp⟩

theorem supportGraph_cycle_transfers_to_selected_cycle {V : Type u}
    (G : SimpleGraph V) (D : EdgeSpace G) {a : V}
    (c : (supportGraph G D).Walk a a) (hc : c.IsCycle) :
    ∃ cG : G.Walk a a,
      cG.IsCycle ∧
        ∀ e : G.edgeSet, (e : Sym2 V) ∈ cG.edgeSet → D e = 1 := by
  classical
  let H := supportGraph G D
  have hHedge : H.edgeSet = supportEdgeSet G D := supportGraph_edgeSet G D
  have hle : H ≤ G := supportGraph_le G D
  have hedges : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
    intro e he
    exact SimpleGraph.edgeSet_mono hle (c.edges_subset_edgeSet he)
  let cG : G.Walk a a := c.transfer G hedges
  refine ⟨cG, hc.transfer hedges, ?_⟩
  intro e he
  have he_edges_G : (e : Sym2 V) ∈ cG.edges :=
    SimpleGraph.Walk.mem_edgeSet.mp he
  have he_edges_H : (e : Sym2 V) ∈ c.edges := by
    simpa [cG] using he_edges_G
  have heH : (e : Sym2 V) ∈ H.edgeSet := c.edges_subset_edgeSet he_edges_H
  have heSupp : (e : Sym2 V) ∈ supportEdgeSet G D := by
    simpa [hHedge] using heH
  rcases heSupp with ⟨heG, hD⟩
  have hproof : heG = e.2 := Subsingleton.elim _ _
  simpa [hproof]
    using hD

end Chapter01
end Diestel
