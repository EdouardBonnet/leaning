import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Degree bounds for finite simple graphs

The grid-minor proof needs to state that an auxiliary subgraph has maximum
degree at most `3`.  This file provides a finset-neighborhood formulation that
is convenient inside existential theorem statements, without requiring a
separate `DecidableRel` instance for every graph that appears as a witness.
-/

namespace TwinWidth
namespace SimpleGraph

/-- `N` is exactly the neighbor set of `v` in `G`. -/
def IsNeighborFinset {V : Type*}
    (G : _root_.SimpleGraph V) (v : V) (N : Finset V) : Prop :=
  ∀ u : V, u ∈ N ↔ G.Adj v u

/-- A vertex has degree at most `d` if its neighbor set is represented by a
finset of cardinality at most `d`. -/
def DegreeAtMost {V : Type*}
    (G : _root_.SimpleGraph V) (v : V) (d : ℕ) : Prop :=
  ∃ N : Finset V, IsNeighborFinset G v N ∧ N.card ≤ d

/-- A vertex has degree exactly `d` if its neighbor set is represented by a
finset of cardinality `d`. -/
def DegreeEquals {V : Type*}
    (G : _root_.SimpleGraph V) (v : V) (d : ℕ) : Prop :=
  ∃ N : Finset V, IsNeighborFinset G v N ∧ N.card = d

/-- A graph has maximum degree at most `d`. -/
def MaxDegreeAtMost {V : Type*}
    (G : _root_.SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, DegreeAtMost G v d

namespace DegreeAtMost

/-- Degree upper bounds are monotone in the numerical bound. -/
theorem mono {V : Type*} {G : _root_.SimpleGraph V} {v : V} {d e : ℕ}
    (h : DegreeAtMost G v d) (hde : d ≤ e) :
    DegreeAtMost G v e := by
  rcases h with ⟨N, hN, hcard⟩
  exact ⟨N, hN, hcard.trans hde⟩

end DegreeAtMost

namespace MaxDegreeAtMost

/-- A chosen neighbor finset supplied by a maximum-degree certificate. -/
noncomputable def neighborFinset {V : Type*} {G : _root_.SimpleGraph V} {d : ℕ}
    (h : MaxDegreeAtMost G d) (v : V) : Finset V :=
  Classical.choose (h v)

theorem mem_neighborFinset {V : Type*} {G : _root_.SimpleGraph V} {d : ℕ}
    (h : MaxDegreeAtMost G d) (v u : V) :
    u ∈ neighborFinset h v ↔ G.Adj v u :=
  (Classical.choose_spec (h v)).1 u

theorem card_neighborFinset_le {V : Type*} {G : _root_.SimpleGraph V} {d : ℕ}
    (h : MaxDegreeAtMost G d) (v : V) :
    (neighborFinset h v).card ≤ d :=
  (Classical.choose_spec (h v)).2

end MaxDegreeAtMost

/-- Maximum-degree upper bounds are monotone in the numerical bound. -/
theorem maxDegreeAtMost_mono {V : Type*} {G : _root_.SimpleGraph V} {d e : ℕ}
    (h : MaxDegreeAtMost G d) (hde : d ≤ e) :
    MaxDegreeAtMost G e := by
  intro v
  exact DegreeAtMost.mono (h v) hde

/-- Passing to a spanning subgraph cannot increase the maximum degree. -/
theorem maxDegreeAtMost_of_le {V : Type*}
    {G H : _root_.SimpleGraph V} {d : ℕ}
    (hG : MaxDegreeAtMost G d) (hHG : H ≤ G) :
    MaxDegreeAtMost H d := by
  classical
  intro v
  let N : Finset V :=
    (MaxDegreeAtMost.neighborFinset hG v).filter fun u => H.Adj v u
  refine ⟨N, ?_, ?_⟩
  · intro u
    constructor
    · intro hu
      exact (Finset.mem_filter.mp hu).2
    · intro huv
      exact Finset.mem_filter.mpr
        ⟨(MaxDegreeAtMost.mem_neighborFinset hG v u).2 (hHG huv), huv⟩
  · exact (Finset.card_filter_le _ _).trans
      (MaxDegreeAtMost.card_neighborFinset_le hG v)

/-- A vertex has degree exactly one when it has a unique neighbor. -/
theorem degreeEquals_one_of_unique_neighbor {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {v u : V}
    (hadj : G.Adj v u) (huniq : ∀ w : V, G.Adj v w → w = u) :
    DegreeEquals G v 1 := by
  refine ⟨{u}, ?_, by simp⟩
  intro w
  constructor
  · intro hw
    have hwu : w = u := by simpa using hw
    simpa [hwu] using hadj
  · intro hvw
    simp [huniq w hvw]

/-- A degree-one vertex has at most one neighbor. -/
theorem DegreeEquals.one_adj_eq {V : Type*} [DecidableEq V]
    {G : _root_.SimpleGraph V} {v u w : V}
    (h : DegreeEquals G v 1) (hu : G.Adj v u) (hw : G.Adj v w) :
    u = w := by
  rcases h with ⟨N, hN, hcard⟩
  have huN : u ∈ N := (hN u).2 hu
  have hwN : w ∈ N := (hN w).2 hw
  rcases Finset.card_eq_one.mp hcard with ⟨a, ha⟩
  have hua : u = a := by simpa [ha] using huN
  have hwa : w = a := by simpa [ha] using hwN
  exact hua.trans hwa.symm

/-- The finset-neighborhood formulation follows from mathlib's `degree` when
the adjacency relation is decidable. -/
theorem maxDegreeAtMost_of_degree_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (h : ∀ v : V, G.degree v ≤ d) :
    MaxDegreeAtMost G d := by
  intro v
  refine ⟨G.neighborFinset v, ?_, h v⟩
  intro u
  simp

end SimpleGraph
end TwinWidth
