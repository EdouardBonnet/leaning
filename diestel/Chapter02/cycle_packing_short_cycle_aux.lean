import Chapter01.corollary_1_3_5
import Chapter02.cycle_packing_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma two_lt_two_log_div_log_two_of_six_lt {x : ℝ} (hx : 6 < x) :
    (2 : ℝ) < 2 * (Real.log x / Real.log 2) := by
  have hlog2pos : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hxpos : 0 < x := by nlinarith
  have hlt : Real.log 2 < Real.log x := by
    apply Real.log_lt_log (by norm_num)
    nlinarith
  have hone_lt : (1 : ℝ) < Real.log x / Real.log 2 := by
    rw [one_lt_div hlog2pos]
    nlinarith
  nlinarith

lemma vertexSet_nonempty_of_six_lt_ncard {G : MultiGraph V E} [Finite V]
    (h : (6 : ℝ) < (G.vertexSet.ncard : ℝ)) :
    G.vertexSet.Nonempty := by
  have hpos : 0 < G.vertexSet.ncard := by
    by_contra hnot
    have hz : G.vertexSet.ncard = 0 := Nat.eq_zero_of_not_pos hnot
    have hz_real : (G.vertexSet.ncard : ℝ) = 0 := by
      exact_mod_cast hz
    nlinarith
  exact (Set.ncard_pos (s := G.vertexSet)).mp hpos

lemma one_le_log_nat_div_log_two {k : ℕ} (hk : 2 ≤ k) :
    (1 : ℝ) ≤ Real.log (k : ℝ) / Real.log 2 := by
  have hlog2pos : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  have hlog_le : Real.log 2 ≤ Real.log (k : ℝ) := by
    exact Real.log_le_log (by norm_num) hk_real
  rw [le_div_iff₀ hlog2pos]
  simpa using hlog_le

lemma five_le_erdosPosaR {k : ℕ} (hk : 2 ≤ k) :
    (5 : ℝ) ≤ erdosPosaR k := by
  have hlog2pos : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hone : (1 : ℝ) ≤ Real.log (k : ℝ) / Real.log 2 :=
    one_le_log_nat_div_log_two hk
  have hloglog_nonneg :
      0 ≤ Real.log (Real.log (k : ℝ) / Real.log 2) / Real.log 2 := by
    have hlog_nonneg :
        0 ≤ Real.log (Real.log (k : ℝ) / Real.log 2) :=
      Real.log_nonneg hone
    exact div_nonneg hlog_nonneg hlog2pos.le
  unfold erdosPosaR
  nlinarith

lemma six_lt_erdosPosaS {k : ℕ} (hk : 2 ≤ k) :
    (6 : ℝ) < erdosPosaS k := by
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hr : (5 : ℝ) ≤ erdosPosaR k := five_le_erdosPosaR hk
  have hr_nonneg : 0 ≤ erdosPosaR k := by nlinarith
  have hleft : (8 : ℝ) ≤ 4 * (k : ℝ) := by nlinarith
  have hprod' : (8 : ℝ) * 5 ≤ (4 * (k : ℝ)) * erdosPosaR k :=
    mul_le_mul hleft hr (by norm_num) (by nlinarith)
  have hprod : (40 : ℝ) ≤ (4 * (k : ℝ)) * erdosPosaR k := by
    norm_num at hprod' ⊢
    exact hprod'
  have hs : (6 : ℝ) < 4 * (k : ℝ) * erdosPosaR k := by
    nlinarith
  simpa [erdosPosaS, hk] using hs

/--
The graph-theoretic short-cycle step used in Lemma 2.3.1.  If the simple
shadow has minimum degree at least three, Corollary 1.3.5 gives a short
simple cycle and `cycleOfSimpleCycle` lifts it.  Otherwise a vertex of
shadow-degree at most two has two parallel incident multiedges, giving a
2-cycle.
-/
theorem exists_cycle_support_ncard_lt_log_bound {V : Type u} {E : Type v}
    (G : MultiGraph V E) [Finite V] [Finite E]
    (hNonempty : G.vertexSet.Nonempty) :
    G.IsCubic →
      (2 : ℝ) < 2 * (Real.log (G.vertexSet.ncard : ℝ) / Real.log 2) →
        ∃ C : G.CycleIn,
          (C.support.ncard : ℝ) <
            2 * (Real.log (G.vertexSet.ncard : ℝ) / Real.log 2) := by
  classical
  intro hCubic htwo_lt
  letI : Fintype G.vertexSet := Fintype.ofFinite G.vertexSet
  letI : Nonempty G.vertexSet := hNonempty.to_subtype
  letI : DecidableRel G.toSimpleGraph.Adj := Classical.decRel _
  by_cases hmin : 3 ≤ G.toSimpleGraph.minDegree
  · have hnotAcyclic : ¬ G.toSimpleGraph.IsAcyclic := by
      intro hacy
      obtain ⟨a, c, hc, _hlen⟩ :=
        (Diestel.Chapter01.proposition_1_3_1 G.toSimpleGraph).2 (by omega)
      exact hacy c hc
    obtain ⟨r, c, hc, hgirth⟩ :=
      (SimpleGraph.exists_girth_eq_length (G := G.toSimpleGraph)).mpr hnotAcyclic
    refine ⟨cycleOfSimpleCycle (G := G) hc, ?_⟩
    have hshort :=
      Diestel.Chapter01.corollary_1_3_5 G.toSimpleGraph hmin
    have hcard :
        Fintype.card G.vertexSet = G.vertexSet.ncard := by
      exact (Nat.card_eq_fintype_card (α := G.vertexSet)).symm.trans
        (Nat.card_coe_set_eq G.vertexSet)
    rw [cycleOfSimpleCycle_support_ncard_eq_length (G := G) hc]
    rw [← hgirth]
    simpa [hcard] using hshort
  · obtain ⟨x, hxmindeg⟩ := G.toSimpleGraph.exists_minimal_degree_vertex
    have hxdeg_lt : G.toSimpleGraph.degree x < 3 := by
      have hmin_lt : G.toSimpleGraph.minDegree < 3 := Nat.lt_of_not_ge hmin
      rwa [hxmindeg] at hmin_lt
    have hxdeg_le : G.toSimpleGraph.degree x ≤ 2 := by
      omega
    have hmulti_deg : G.degree x.1 = 3 := hCubic.2 x.1 x.2
    obtain ⟨e, f, y, hef, hxy, he, hf⟩ :=
      exists_parallel_edges_of_simple_degree_le_two (G := G)
        hCubic.1 x.2 hmulti_deg hxdeg_le
    refine ⟨cycleOfParallelEdges (G := G) hef hxy he hf, ?_⟩
    rw [cycleOfParallelEdges_support_ncard (G := G) hef hxy he hf]
    exact htwo_lt

theorem exists_cycle_support_ncard_lt_log_bound_of_erdosPosaS_lt
    {V : Type u} {E : Type v} (G : MultiGraph V E) [Finite V] [Finite E]
    {k : ℕ} (hk : 2 ≤ k) :
    G.IsCubic →
      erdosPosaS k < (G.vertexSet.ncard : ℝ) →
        ∃ C : G.CycleIn,
          (C.support.ncard : ℝ) <
            2 * (Real.log (G.vertexSet.ncard : ℝ) / Real.log 2) := by
  intro hCubic hLarge
  have hsix_s : (6 : ℝ) < erdosPosaS k := six_lt_erdosPosaS hk
  have hsix_n : (6 : ℝ) < (G.vertexSet.ncard : ℝ) := hsix_s.trans hLarge
  have hNonempty : G.vertexSet.Nonempty :=
    vertexSet_nonempty_of_six_lt_ncard (G := G) hsix_n
  have htwo_lt :
      (2 : ℝ) < 2 * (Real.log (G.vertexSet.ncard : ℝ) / Real.log 2) :=
    two_lt_two_log_div_log_two_of_six_lt hsix_n
  exact exists_cycle_support_ncard_lt_log_bound G hNonempty hCubic htwo_lt

end MultiGraph

end Chapter02
end Diestel
