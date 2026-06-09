import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Trails

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

private lemma isCycle_isTrail {V : Type u} {G : SimpleGraph V} {a : V}
    {c : G.Walk a a} (hc : c.IsCycle) : c.IsTrail := by
  cases c with
  | nil =>
      simp [SimpleGraph.Walk.isTrail_def]
  | cons h p =>
      rw [SimpleGraph.Walk.cons_isCycle_iff] at hc
      rw [SimpleGraph.Walk.isTrail_cons]
      exact ⟨hc.1.isTrail, hc.2⟩

private lemma support_eq_cons_tail_support {V : Type u} {G : SimpleGraph V} {a : V}
    {c : G.Walk a a} (hpos : 0 < c.length) :
    c.support = a :: c.tail.support := by
  cases c with
  | nil =>
      simp at hpos
  | cons h p =>
      simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.tail_cons]

private lemma idxOf_getVert_of_isCycle {V : Type u} {G : SimpleGraph V} {a : V}
    [DecidableEq V] {c : G.Walk a a} (hc : c.IsCycle) {i : ℕ}
    (hi0 : 0 < i) (hil : i < c.length) :
    List.idxOf (c.getVert i) c.support = i := by
  have hpos : 0 < c.length := lt_of_lt_of_le hi0 hil.le
  have hsupport : c.support = a :: c.tail.support :=
    support_eq_cons_tail_support hpos
  have hne : a ≠ c.getVert i := by
    intro h
    have hend := (hc.getVert_endpoint_iff hil.le).mp h.symm
    omega
  have htail_nodup : c.tail.support.Nodup := by
    simpa [hsupport] using hc.support_nodup
  have htail_len : c.tail.length = c.length - 1 := by
    have h := SimpleGraph.Walk.length_tail_add_one (p := c)
      (by
        intro hnil
        have hlen : c.length = 0 := SimpleGraph.Walk.nil_iff_length_eq.mp hnil
        omega)
    omega
  have hidx_lt : i - 1 < c.tail.support.length := by
    rw [SimpleGraph.Walk.length_support, htail_len]
    omega
  have hget_tail : c.tail.getVert (i - 1) = c.getVert i := by
    rw [SimpleGraph.Walk.getVert_tail]
    congr
    omega
  have hget_elem : c.getVert i = c.tail.support[i - 1] := by
    rw [← hget_tail]
    exact SimpleGraph.Walk.getVert_eq_support_getElem c.tail (by
      rw [htail_len]
      omega)
  have hidx_tail :
      List.idxOf (c.getVert i) c.tail.support = i - 1 := by
    rw [hget_elem]
    exact List.idxOf_getElem htail_nodup (i - 1) hidx_lt
  rw [hsupport]
  rw [List.idxOf_cons_ne c.tail.support hne]
  rw [hidx_tail]
  omega

private lemma two_paths_short_cycle {V : Type u} {G : SimpleGraph V}
    {x y : V} {p q : G.Walk x y}
    (hp : p.IsPath) (hq : q.IsPath) (hlen : q.length < p.length) :
    G.girth ≤ p.length + q.length := by
  classical
  let E : Finset (Sym2 V) := p.edges.toFinset ∪ q.edges.toFinset
  let H : SimpleGraph V := SimpleGraph.fromEdgeSet (E : Set (Sym2 V))
  have hH_finite : H.edgeSet.Finite :=
    (Set.Finite.ofFinset E (by intro e; rfl)).subset (by
      intro e he
      rw [SimpleGraph.edgeSet_fromEdgeSet] at he
      exact he.1)
  letI : Fintype H.edgeSet := hH_finite.fintype
  have hp_edges : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨?_, ?_⟩
    · exact Finset.mem_union.mpr (Or.inl (List.mem_toFinset.mpr he))
    · exact SimpleGraph.not_isDiag_of_mem_edgeSet G (p.edges_subset_edgeSet he)
  have hq_edges : ∀ e ∈ q.edges, e ∈ H.edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨?_, ?_⟩
    · exact Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr he))
    · exact SimpleGraph.not_isDiag_of_mem_edgeSet G (q.edges_subset_edgeSet he)
  let pH : H.Walk x y := p.transfer H hp_edges
  let qH : H.Walk x y := q.transfer H hq_edges
  have hpH : pH.IsPath := hp.transfer hp_edges
  have hqH : qH.IsPath := hq.transfer hq_edges
  have hpaths_ne : (⟨pH, hpH⟩ : H.Path x y) ≠ ⟨qH, hqH⟩ := by
    intro hEq
    have hLen := congrArg (fun r : H.Path x y => r.1.length) hEq
    dsimp [pH, qH] at hLen
    simp at hLen
    omega
  have hnot_acyclic : ¬ H.IsAcyclic := by
    intro hacy
    exact hpaths_ne (hacy.path_unique ⟨pH, hpH⟩ ⟨qH, hqH⟩)
  obtain ⟨z, cH, hcH, _hgirthH⟩ :=
    (SimpleGraph.exists_girth_eq_length (G := H)).mpr hnot_acyclic
  have hH_le_G : H ≤ G := by
    rw [SimpleGraph.fromEdgeSet_le]
    intro e he
    rcases Finset.mem_union.mp he.1 with heP | heQ
    · exact p.edges_subset_edgeSet (List.mem_toFinset.mp heP)
    · exact q.edges_subset_edgeSet (List.mem_toFinset.mp heQ)
  have hcH_trail : cH.IsTrail := isCycle_isTrail hcH
  have hcycle_bound : cH.length ≤ p.length + q.length := by
    have h1 := hcH_trail.length_le_card_edgeFinset
    have hcard_to_union : H.edgeFinset.card ≤ E.card := by
      apply Finset.card_le_card
      intro e he
      have heH : e ∈ H.edgeSet := (SimpleGraph.mem_edgeFinset).mp he
      rw [SimpleGraph.edgeSet_fromEdgeSet] at heH
      exact heH.1
    have hcard_union :
        E.card ≤ p.edges.toFinset.card + q.edges.toFinset.card := by
      dsimp [E]
      exact Finset.card_union_le p.edges.toFinset q.edges.toFinset
    have hp_card : p.edges.toFinset.card ≤ p.length := by
      simpa [SimpleGraph.Walk.length_edges] using List.toFinset_card_le p.edges
    have hq_card : q.edges.toFinset.card ≤ q.length := by
      simpa [SimpleGraph.Walk.length_edges] using List.toFinset_card_le q.edges
    omega
  have hc_edges : ∀ e ∈ cH.edges, e ∈ G.edgeSet := by
    intro e he
    exact SimpleGraph.edgeSet_mono hH_le_G (cH.edges_subset_edgeSet he)
  have hcG : (cH.transfer G hc_edges).IsCycle := hcH.transfer hc_edges
  have hg : G.girth ≤ cH.length := by
    simpa using SimpleGraph.girth_le_length hcG
  omega

/--
Diestel, Proposition 1.3.2.
Every connected finite graph containing a cycle satisfies
`g(G) ≤ 2 * diam(G) + 1`.
-/
theorem proposition_1_3_2 {V : Type u} (G : SimpleGraph V) [Finite V] [Nonempty V] :
    G.Connected → ¬ G.IsAcyclic → G.girth ≤ 2 * G.diam + 1 := by
  classical
  intro hconn hcyc
  by_contra hnot
  have hstrict : 2 * G.diam + 1 < G.girth := Nat.lt_of_not_ge hnot
  obtain ⟨a, c, hc, hcgirth⟩ :=
    (SimpleGraph.exists_girth_eq_length (G := G)).mpr hcyc
  let i : ℕ := G.diam + 1
  have hi0 : 0 < i := by dsimp [i]; omega
  have hil : i < c.length := by
    rw [← hcgirth]
    dsimp [i] at *
    omega
  let b : V := c.getVert i
  have hb_support : b ∈ c.support := SimpleGraph.Walk.getVert_mem_support c i
  let p : G.Walk a b := c.takeUntil b hb_support
  have hp : p.IsPath := hc.isPath_takeUntil hb_support
  have hp_len : p.length = i := by
    dsimp [p, b]
    rw [SimpleGraph.Walk.length_takeUntil]
    exact idxOf_getVert_of_isCycle hc hi0 hil
  obtain ⟨q, hq, hq_len⟩ := hconn.exists_path_of_dist a b
  have hediam_ne_top : G.ediam ≠ ⊤ :=
    (SimpleGraph.connected_iff_ediam_ne_top (G := G)).mp hconn
  have hq_le_diam : q.length ≤ G.diam := by
    rw [hq_len]
    exact SimpleGraph.dist_le_diam hediam_ne_top
  have hq_lt_p : q.length < p.length := by
    rw [hp_len]
    dsimp [i]
    omega
  have hshort := two_paths_short_cycle hp hq hq_lt_p
  rw [hp_len] at hshort
  dsimp [i] at hshort
  have hupper : G.girth ≤ 2 * G.diam + 1 := by
    omega
  exact (Nat.not_lt_of_ge hupper) hstrict

end Chapter01
end Diestel
