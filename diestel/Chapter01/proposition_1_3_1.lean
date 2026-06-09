import Chapter01.definitions_ch1
import Mathlib.Order.Interval.Finset.Nat

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

private lemma edge_not_mem_reverse_takeUntil_of_two_le_idx
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {a b x : V} {p : G.Walk a b} (hp : p.IsPath) (hx : x ∈ p.support)
    (hidx : 2 ≤ p.support.idxOf x) :
    s(a, x) ∉ (p.takeUntil x hx).reverse.edges := by
  intro hmem
  let q : G.Walk x a := (p.takeUntil x hx).reverse
  have hqpath : q.IsPath := (hp.takeUntil hx).reverse
  have hqa : q.getVert 1 = a := by
    have h := hqpath.eq_snd_of_mem_edges (w := a) (by
      simpa [q, Sym2.eq_swap] using hmem)
    change q.getVert 1 = a
    exact h.symm
  have hq_len : q.length = p.support.idxOf x := by
    simp [q, SimpleGraph.Walk.length_takeUntil]
  have hq_len_ge : 2 ≤ q.length := by
    rw [hq_len]
    exact hidx
  have hget : q.getVert 1 = q.getVert q.length := by
    rw [hqa, SimpleGraph.Walk.getVert_length]
  have hone : 1 ∈ ({i : ℕ | i ≤ q.length} : Set ℕ) := by
    simp [Nat.succ_le_of_lt (lt_of_lt_of_le Nat.zero_lt_two hq_len_ge)]
  have hlast : q.length ∈ ({i : ℕ | i ≤ q.length} : Set ℕ) := by
    simp
  have hEq := hqpath.getVert_injOn hone hlast hget
  omega

private lemma longest_path_neighbor_mem_support
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {a b : V} {p : G.Walk a b} (hp : p.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ p.length)
    {w : V} (hAdj : G.Adj a w) : w ∈ p.support := by
  by_contra hw_not
  have hp' : (SimpleGraph.Walk.cons hAdj.symm p).IsPath := hp.cons hw_not
  have hle := hmax w b (SimpleGraph.Walk.cons hAdj.symm p) hp'
  rw [SimpleGraph.Walk.length_cons] at hle
  omega

/--
Diestel, Proposition 1.3.1.
Every graph contains a path of length `δ(G)` and, if `δ(G) ≥ 2`, a cycle
of length at least `δ(G) + 1`.
-/
theorem proposition_1_3_1 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [Nonempty V] [DecidableRel G.Adj] :
  (∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ G.minDegree ≤ p.length) ∧
    (2 ≤ G.minDegree →
      ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧ G.minDegree + 1 ≤ c.length) := by
  classical
  obtain ⟨a, b, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  constructor
  · refine ⟨a, b, p, hp, ?_⟩
    calc
      G.minDegree ≤ G.degree b := G.minDegree_le_degree b
      _ = (G.neighborFinset b).card := (SimpleGraph.card_neighborFinset_eq_degree G b).symm
      _ ≤ p.support.dropLast.toFinset.card := by
        apply Finset.card_le_card
        intro w hw
        have hAdj : G.Adj b w := (SimpleGraph.mem_neighborFinset G b w).mp hw
        have hw_support : w ∈ p.support := by
          by_contra hw_not
          have hp' : (p.concat hAdj).IsPath := hp.concat hw_not hAdj
          have hle := hmax a w (p.concat hAdj) hp'
          rw [SimpleGraph.Walk.length_concat] at hle
          omega
        exact List.mem_toFinset.mpr <|
          List.mem_dropLast_of_mem_of_ne_getLast hw_support (by
            rw [SimpleGraph.Walk.getLast_support]
            exact hAdj.ne')
      _ ≤ p.support.dropLast.length := List.toFinset_card_le _
      _ = p.length := by
        rw [List.length_dropLast, SimpleGraph.Walk.length_support]
        omega
  · intro hmin
    let idxSet : Finset ℕ := (G.neighborFinset a).image fun w => p.support.idxOf w
    have hdeg_a : 2 ≤ G.degree a := hmin.trans (G.minDegree_le_degree a)
    have hN_nonempty : (G.neighborFinset a).Nonempty := by
      rw [← Finset.card_pos, SimpleGraph.card_neighborFinset_eq_degree]
      omega
    have hidx_nonempty : idxSet.Nonempty := hN_nonempty.image _
    let m : ℕ := idxSet.max' hidx_nonempty
    have hmax_mem : m ∈ idxSet := by
      exact Finset.max'_mem idxSet hidx_nonempty
    obtain ⟨x, hxN, hxidx⟩ := Finset.mem_image.mp hmax_mem
    have hxAdj : G.Adj a x := (SimpleGraph.mem_neighborFinset G a x).mp hxN
    have hx_support : x ∈ p.support :=
      longest_path_neighbor_mem_support hp hmax hxAdj
    have neighbor_support : ∀ ⦃y : V⦄, y ∈ G.neighborFinset a → y ∈ p.support := by
      intro y hy
      exact longest_path_neighbor_mem_support hp hmax
        ((SimpleGraph.mem_neighborFinset G a y).mp hy)
    have hidx_inj : Set.InjOn (fun w : V => p.support.idxOf w)
        (G.neighborFinset a : Set V) := by
      intro y hy z _hz hyz
      exact (List.idxOf_inj (neighbor_support hy)).mp hyz
    have hcard_image : idxSet.card = (G.neighborFinset a).card := by
      exact Finset.card_image_of_injOn hidx_inj
    have hidx_subset : idxSet ⊆ Finset.Icc 1 m := by
      intro i hi
      obtain ⟨y, hyN, rfl⟩ := Finset.mem_image.mp hi
      have hyAdj : G.Adj a y := (SimpleGraph.mem_neighborFinset G a y).mp hyN
      have hy_support : y ∈ p.support := neighbor_support hyN
      have hpos : 1 ≤ p.support.idxOf y := by
        by_contra hnot
        have hzero : p.support.idxOf y = 0 := Nat.eq_zero_of_not_pos hnot
        have hget := p.getVert_support_idxOf hy_support
        rw [hzero, SimpleGraph.Walk.getVert_zero] at hget
        exact hyAdj.ne hget
      have hle : p.support.idxOf y ≤ m := by
        exact Finset.le_max' idxSet (p.support.idxOf y)
          (Finset.mem_image.mpr ⟨y, hyN, rfl⟩)
      exact Finset.mem_Icc.mpr ⟨hpos, hle⟩
    have hdeg_le_m : G.degree a ≤ m := by
      calc
        G.degree a = (G.neighborFinset a).card :=
          (SimpleGraph.card_neighborFinset_eq_degree G a).symm
        _ = idxSet.card := hcard_image.symm
        _ ≤ (Finset.Icc 1 m).card := Finset.card_le_card hidx_subset
        _ = m := by
          rw [Nat.card_Icc]
          omega
    have hm_ge_two : 2 ≤ m := hdeg_a.trans hdeg_le_m
    have hxidx_m : p.support.idxOf x = m := hxidx
    let pref : G.Walk a x := p.takeUntil x hx_support
    let c : G.Walk a a := SimpleGraph.Walk.cons hxAdj pref.reverse
    refine ⟨a, c, ?_, ?_⟩
    · have hpref_path : pref.IsPath := hp.takeUntil hx_support
      have hidx_two : 2 ≤ p.support.idxOf x := by
        rw [hxidx_m]
        exact hm_ge_two
      exact (SimpleGraph.Walk.cons_isCycle_iff pref.reverse hxAdj).mpr
        ⟨hpref_path.reverse,
          edge_not_mem_reverse_takeUntil_of_two_le_idx hp hx_support hidx_two⟩
    · have hmin_le_m : G.minDegree ≤ m := (G.minDegree_le_degree a).trans hdeg_le_m
      have hc_len : c.length = m + 1 := by
        simp [c, pref, SimpleGraph.Walk.length_takeUntil, hxidx_m]
      rw [hc_len]
      omega

end Chapter01
end Diestel
