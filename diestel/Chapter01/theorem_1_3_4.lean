import Chapter01.ahl_counting
import Chapter01.average_degree
import Chapter01.proposition_1_2_2
import Mathlib.Tactic

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

private theorem egirth_induce_ge {V : Type u} (G : SimpleGraph V)
    (U : Set V) {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) :
    (g : ℕ∞) ≤ (G.induce U).egirth := by
  rw [SimpleGraph.le_egirth]
  intro a w hw
  let e := SimpleGraph.Embedding.induce (G := G) U
  let f := e.toHom
  have hcycle : (w.map f).IsCycle := hw.map e.injective
  have hlen := (SimpleGraph.le_egirth.mp hg (a : V)
    (w.map f) hcycle)
  have hlen_eq : ((w.map f).length : ℕ∞) = (w.length : ℕ∞) := by
    exact_mod_cast (SimpleGraph.Walk.length_map (p := w) (f := f))
  exact hlen_eq ▸ hlen

private theorem edgeSet_nat_card_pos_of_average_degree_ge_two {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (havg2 : (2 : ℝ) ≤ (average_degree G : ℝ)) :
    0 < Nat.card G.edgeSet := by
  by_contra hnot
  have hE0 : Nat.card G.edgeSet = 0 := Nat.eq_zero_of_not_pos hnot
  have hEdgeFinset0 : G.edgeFinset.card = 0 := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] at hE0
    exact hE0
  have hsum_zero : ∑ v : V, (G.degree v : ℚ) = 0 := by
    rw [← Nat.cast_sum, SimpleGraph.sum_degrees_eq_twice_card_edges]
    rw [hEdgeFinset0]
    norm_num
  have havg_zero : average_degree G = 0 := by
    rw [average_degree, hsum_zero, zero_div]
  have : ((average_degree G : ℚ) : ℝ) = 0 := by
    rw [havg_zero]
    norm_num
  linarith

private theorem edge_ratio_nat_eq_edge_vertex_ratio_rat {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    (Nat.card G.edgeSet : ℚ) / Nat.card V = edge_vertex_ratio G := by
  have hE : (Nat.card G.edgeSet : ℚ) = (G.edgeFinset.card : ℚ) := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  have hV : (Nat.card V : ℚ) = (Fintype.card V : ℚ) := by
    rw [Nat.card_eq_fintype_card]
  rw [hE, hV, edge_vertex_ratio]

/--
Diestel, Theorem 1.3.4 (Alon-Hoory-Linial).
Natural-language statement:
If `d(G) ≥ d ≥ 2` and `g(G) ≥ g`, then `|G| ≥ n₀(d,g)`.
-/
theorem theorem_1_3_4 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (d : ℝ) (g : ℕ) :
  2 ≤ d →
    d ≤ (average_degree G : ℝ) →
      (g : ℕ∞) ≤ G.egirth →
        n0 d g ≤ (Fintype.card V : ℝ) := by
  classical
  intro hd havg hg
  have havg2 : (2 : ℝ) ≤ (average_degree G : ℝ) := hd.trans havg
  have hE : 0 < Nat.card G.edgeSet :=
    edgeSet_nat_card_pos_of_average_degree_ge_two G havg2
  obtain ⟨U, hUne, hratio_ge, hmindeg_ratio⟩ := proposition_1_2_2 G hE
  let H : SimpleGraph U := G.induce U
  letI : Fintype U := Fintype.ofFinite U
  letI : DecidableEq U := Classical.decEq U
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  haveI : Nonempty U := hUne.to_subtype
  have hratio_ge_real :
      (edge_vertex_ratio G : ℝ) ≤ (edge_vertex_ratio H : ℝ) := by
    have hratio_ge_rat : edge_vertex_ratio G ≤ edge_vertex_ratio H := by
      rw [← edge_ratio_nat_eq_edge_vertex_ratio_rat G,
        ← edge_ratio_nat_eq_edge_vertex_ratio_rat H]
      exact hratio_ge
    exact_mod_cast hratio_ge_rat
  have hAvgGR : (average_degree G : ℝ) = 2 * (edge_vertex_ratio G : ℝ) := by
    exact_mod_cast average_degree_eq_two_mul_edge_vertex_ratio G
  have hAvgHR : (average_degree H : ℝ) = 2 * (edge_vertex_ratio H : ℝ) := by
    exact_mod_cast average_degree_eq_two_mul_edge_vertex_ratio H
  have havg_ge_real : (average_degree G : ℝ) ≤ (average_degree H : ℝ) := by
    rw [hAvgGR, hAvgHR]
    nlinarith
  have havgH2 : (2 : ℝ) ≤ (average_degree H : ℝ) :=
    havg2.trans havg_ge_real
  have hratioG_ge_one : (1 : ℝ) ≤ (edge_vertex_ratio G : ℝ) := by
    nlinarith
  have hratioH_ge_one : (1 : ℝ) ≤ (edge_vertex_ratio H : ℝ) :=
    hratioG_ge_one.trans hratio_ge_real
  have hdegH : ∀ v : U, 2 ≤ H.degree v := by
    intro v
    have hgtQ := hmindeg_ratio v
    have hgtR : (edge_vertex_ratio H : ℝ) <
        (Nat.card (H.neighborSet v) : ℝ) := by
      have hgtQ' : edge_vertex_ratio H < (Nat.card (H.neighborSet v) : ℚ) := by
        rw [← edge_ratio_nat_eq_edge_vertex_ratio_rat H]
        exact hgtQ
      exact_mod_cast hgtQ'
    have hone_lt : (1 : ℝ) < (Nat.card (H.neighborSet v) : ℝ) :=
      lt_of_le_of_lt hratioH_ge_one hgtR
    have hone_lt_nat : 1 < Nat.card (H.neighborSet v) := by
      exact_mod_cast hone_lt
    have hcard : Nat.card (H.neighborSet v) = H.degree v := by
      rw [Nat.card_eq_fintype_card]
      exact SimpleGraph.card_neighborSet_eq_degree H v
    omega
  have hgH : (g : ℕ∞) ≤ H.egirth := by
    simpa [H] using egirth_induce_ge G U hg
  have hAHL : n0 (ahlLambda H + 1) g ≤ (Fintype.card U : ℝ) :=
    ahl_moore_bound_minDegree_two H hgH hdegH
  have hLambda_ge : (average_degree H : ℝ) - 1 ≤ ahlLambda H :=
    average_degree_sub_one_le_ahlLambda H havgH2 hdegH
  have hd_le_lam : d ≤ ahlLambda H + 1 := by
    have hd_le_avgH : d ≤ (average_degree H : ℝ) := havg.trans havg_ge_real
    linarith
  have hn0mono : n0 d g ≤ n0 (ahlLambda H + 1) g :=
    n0_mono_degree hd hd_le_lam
  have hcardUleV : (Fintype.card U : ℝ) ≤ (Fintype.card V : ℝ) := by
    have hnat : Fintype.card U ≤ Fintype.card V :=
      Fintype.card_subtype_le (fun v : V => v ∈ U)
    exact_mod_cast hnat
  exact hn0mono.trans (hAHL.trans hcardUleV)

end Chapter01
end Diestel
