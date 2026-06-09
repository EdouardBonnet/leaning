import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Tactic.Linarith

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

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

private lemma longest_closed_trail_support_incident_edges_used {V : Type u} (G : SimpleGraph V)
    [DecidableEq V] {u x : V} {p : G.Walk u u} (hp : p.IsTrail)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsTrail → p'.length ≤ p.length)
    (hx : x ∈ p.support) :
    ∀ e : Sym2 V, e ∈ G.edgeSet → x ∈ e → e ∈ p.edges := by
  classical
  intro e he hxedge
  by_contra he_not
  let y := Sym2.Mem.other hxedge
  have heq : s(x, y) = e := Sym2.other_spec hxedge
  have hadj : G.Adj x y := by
    rw [← SimpleGraph.mem_edgeSet G]
    exact heq.symm ▸ he
  let r : G.Walk x x := p.rotate x hx
  have hr : r.IsTrail := by
    dsimp [r]
    exact (SimpleGraph.Walk.isTrail_rotate hx).mpr hp
  have hnot : s(y, x) ∉ r.edges := by
    intro hmem
    have hmem_p : s(y, x) ∈ p.edges :=
      (SimpleGraph.Walk.rotate_edges p x hx).mem_iff.mp hmem
    exact he_not (by simpa [Sym2.eq_swap, heq] using hmem_p)
  let q : G.Walk y x := r.cons hadj.symm
  have hq : q.IsTrail := by
    dsimp [q]
    rw [SimpleGraph.Walk.isTrail_cons]
    exact ⟨hr, hnot⟩
  have hle := hmax y x q hq
  dsimp [q, r] at hle
  rw [SimpleGraph.Walk.length_rotate] at hle
  omega

private lemma walk_from_support_to_outside_has_unused_incident {V : Type u} {G : SimpleGraph V}
    {r : V} {p : G.Walk r r} {a b : V} (q : G.Walk a b)
    (ha : a ∈ p.support) (hb : b ∉ p.support) :
    ∃ x : V, x ∈ p.support ∧ ∃ e : Sym2 V, e ∈ G.edgeSet ∧ x ∈ e ∧ e ∉ p.edges := by
  induction q with
  | nil => exact (hb ha).elim
  | @cons a c b hac q ih =>
      by_cases hc : c ∈ p.support
      · exact ih hc hb
      · refine ⟨a, ha, s(a, c), ?_, ?_, ?_⟩
        · rw [SimpleGraph.mem_edgeSet]
          exact hac
        · simp [Sym2.mem_iff]
        · intro hmem
          exact hc (p.snd_mem_support_of_mem_edges hmem)

private lemma longest_closed_trail_uses_all_edges {V : Type u} (G : SimpleGraph V)
    [DecidableEq V] (hconn : G.Connected)
    {u : V} {p : G.Walk u u} (hp : p.IsTrail)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsTrail → p'.length ≤ p.length) :
    ∀ e : Sym2 V, e ∈ G.edgeSet → e ∈ p.edges := by
  classical
  intro e he
  refine Sym2.ind ?_ e he
  intro a b heab
  by_cases ha : a ∈ p.support
  · exact longest_closed_trail_support_incident_edges_used G hp hmax ha
      s(a, b) heab (by simp [Sym2.mem_iff])
  · obtain ⟨q⟩ := hconn u a
    obtain ⟨x, hx, f, hfG, hxf, hfn⟩ :=
      walk_from_support_to_outside_has_unused_incident q p.start_mem_support ha
    exact (hfn (longest_closed_trail_support_incident_edges_used G hp hmax hx f hfG hxf)).elim

/--
Diestel, Theorem 1.8.1 (Euler 1736).
A connected graph is Eulerian iff every vertex has even degree.
-/
theorem theorem_1_8_1 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    G.Connected → (IsEulerian G ↔ ∀ v : V, Even (G.degree v)) := by
  intro hconn
  constructor
  · rintro ⟨a, p, hp⟩ x
    unfold IsEulerTour at hp
    exact (SimpleGraph.Walk.IsEulerian.even_degree_iff (x := x) hp).mpr
      (by intro h; exact (h rfl).elim)
  · intro heven
    haveI : Nonempty V := (SimpleGraph.connected_iff G).mp hconn |>.2
    obtain ⟨a, b, p, hp, hmax⟩ :=
      SimpleGraph.Walk.exists_isTrail_forall_isTrail_length_le_length G
    have hclosed := longest_trail_closed_of_even_degrees G hp hmax heven
    subst b
    refine ⟨a, p, ?_⟩
    unfold IsEulerTour
    exact hp.isEulerian_of_forall_mem (longest_closed_trail_uses_all_edges G hconn hp hmax)

end Chapter01
end Diestel
