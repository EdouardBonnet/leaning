import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

private noncomputable def induced_ratio {V : Type u} (G : SimpleGraph V) (U : Set V) : ℚ :=
  (Nat.card (G.induce U).edgeSet : ℚ) / Nat.card U

private def induce_diff_singleton_iso {V : Type u} (G : SimpleGraph V)
    (U : Set V) (v : U) :
    G.induce (U \ {v.1}) ≃g (G.induce U).induce ({v}ᶜ : Set U) where
  toFun x := ⟨⟨x.1, x.2.1⟩, by
    intro h
    exact x.2.2 (by
      rw [Set.mem_singleton_iff]
      exact congrArg Subtype.val h)⟩
  invFun x := ⟨x.1.1, x.1.2, by
    intro h
    exact x.2 (by
      rw [Set.mem_singleton_iff]
      exact Subtype.ext (Set.mem_singleton_iff.mp h))⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
  map_rel_iff' := by
    intro x y
    rfl

private lemma induced_ratio_univ {V : Type u} (G : SimpleGraph V) [Finite V] :
    induced_ratio G Set.univ =
      (Nat.card G.edgeSet : ℚ) / Nat.card V := by
  classical
  letI := Fintype.ofFinite V
  have h_edges :
      Nat.card (G.induce Set.univ).edgeSet = Nat.card G.edgeSet := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet]
    exact (SimpleGraph.induceUnivIso G).card_edgeFinset_eq
  have h_vertices : Nat.card (Set.univ : Set V) = Nat.card V := by
    exact Nat.card_congr (Equiv.Set.univ V)
  rw [induced_ratio, h_edges, h_vertices]

private lemma induced_ratio_pos_of_edge {V : Type u} (G : SimpleGraph V) [Finite V]
    (hE : 0 < Nat.card G.edgeSet) :
    0 < (Nat.card G.edgeSet : ℚ) / Nat.card V := by
  haveI : Nonempty V := by
    have hne : Nonempty G.edgeSet := (Finite.card_pos_iff.mp hE)
    let e : G.edgeSet := Classical.choice hne
    exact ⟨e.1.out.1⟩
  have hV : 0 < Nat.card V := Finite.card_pos
  exact div_pos (by exact_mod_cast hE) (by exact_mod_cast hV)

private lemma one_lt_ncard_of_positive_induced_ratio {V : Type u} (G : SimpleGraph V)
    [Finite V] {U : Set V} (hpos : 0 < induced_ratio G U) :
    1 < U.ncard := by
  classical
  letI := Fintype.ofFinite V
  by_contra hnot
  have hsub : U.Subsingleton := by
    rw [← Set.ncard_le_one_iff_subsingleton]
    exact le_of_not_gt hnot
  haveI : Subsingleton U := Set.Subsingleton.coe_sort hsub
  have h_edge_empty : (G.induce U).edgeSet = ∅ := by
    ext e
    constructor
    · intro he
      exact (G.induce U).not_isDiag_of_mem_edgeSet he <|
        Sym2.isDiag_of_subsingleton e
    · intro he
      exact False.elim (by simpa using he)
  have hzero_edges : Nat.card (G.induce U).edgeSet = 0 := by
    rw [h_edge_empty]
    exact Nat.card_of_isEmpty
  have : induced_ratio G U = 0 := by
    rw [induced_ratio, hzero_edges, Nat.cast_zero, zero_div]
  linarith

private lemma induced_delete_ratio_ge {V : Type u} (G : SimpleGraph V) [Finite V]
    {U : Set V} (v : U) (hUcard : 1 < Nat.card U)
    (hsmall :
      (Nat.card ((G.induce U).neighborSet v) : ℚ) ≤ induced_ratio G U) :
    induced_ratio G U ≤ induced_ratio G (U \ {v.1}) := by
  classical
  letI := Fintype.ofFinite V
  letI : DecidableEq V := Classical.decEq V
  let H : SimpleGraph U := G.induce U
  let W : Set V := U \ {v.1}
  have hUpos : 0 < Nat.card U := by
    exact (Set.ncard_pos (s := U)).mpr ⟨v.1, v.2⟩
  have hdeg_eq :
      Nat.card (H.neighborSet v) = H.degree v := by
    rw [Nat.card_eq_fintype_card]
    exact SimpleGraph.card_neighborSet_eq_degree H v
  have hcardW : Nat.card W + 1 = Nat.card U := by
    change W.ncard + 1 = U.ncard
    exact Set.ncard_diff_singleton_add_one (s := U) (a := v.1) v.2
  have hW_nat : Nat.card W = Nat.card U - 1 := by omega
  have hH_edges :
      Nat.card (G.induce W).edgeSet =
        Nat.card H.edgeSet - H.degree v := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    calc
      Fintype.card (G.induce W).edgeSet =
          (G.induce W).edgeFinset.card := SimpleGraph.card_edgeSet
      _ = ((H.induce ({v}ᶜ : Set U)).edgeFinset.card) := by
        rw [(induce_diff_singleton_iso G U v).card_edgeFinset_eq]
      _ = (H.deleteIncidenceSet v).edgeFinset.card := by
        rw [SimpleGraph.card_edgeFinset_induce_compl_singleton]
      _ = H.edgeFinset.card - H.degree v := by
        rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet]
      _ = Fintype.card H.edgeSet - H.degree v := by
        rw [SimpleGraph.edgeFinset_card]
  have hdeg_le_edges : H.degree v ≤ Nat.card H.edgeSet := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    exact H.degree_le_card_edgeFinset v
  have hineq_mul :
      (Nat.card U : ℚ) * (H.degree v : ℚ) ≤
        (Nat.card H.edgeSet : ℚ) := by
    have := hsmall
    rw [induced_ratio, hdeg_eq] at this
    have hUq : (0 : ℚ) < Nat.card U := by exact_mod_cast hUpos
    have hmul := mul_le_mul_of_nonneg_left this hUq.le
    rw [mul_div_cancel₀ _ hUq.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hcalc :
      (Nat.card H.edgeSet : ℚ) / Nat.card U ≤
        ((Nat.card H.edgeSet - H.degree v : ℕ) : ℚ) /
          ((Nat.card U - 1 : ℕ) : ℚ) := by
    have hUq : (0 : ℚ) < Nat.card U := by exact_mod_cast hUpos
    have hUsubq : (0 : ℚ) < ((Nat.card U - 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.sub_pos_of_lt hUcard
    have hsub_cast :
        ((Nat.card H.edgeSet - H.degree v : ℕ) : ℚ) =
          (Nat.card H.edgeSet : ℚ) - H.degree v := by
      rw [Nat.cast_sub hdeg_le_edges]
    have hden_cast :
        ((Nat.card U - 1 : ℕ) : ℚ) = (Nat.card U : ℚ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_of_lt hUcard)]
      norm_num
    rw [hden_cast] at hUsubq
    rw [hsub_cast, hden_cast]
    rw [div_le_div_iff₀ hUq hUsubq]
    nlinarith
  rw [induced_ratio, induced_ratio, hH_edges, hW_nat]
  change (Nat.card H.edgeSet : ℚ) / Nat.card U ≤
    ((Nat.card H.edgeSet - H.degree v : ℕ) : ℚ) /
      ((Nat.card U - 1 : ℕ) : ℚ)
  exact hcalc

/--
Diestel, Proposition 1.2.2.
Every graph with at least one edge has an induced subgraph `H` with
`δ(H) > ε(H) ≥ ε(G)`.
-/
theorem proposition_1_2_2 {V : Type u} (G : SimpleGraph V) [Finite V] :
  0 < Nat.card G.edgeSet →
    ∃ U : Set V, U.Nonempty ∧
      (let H := G.induce U
       ((Nat.card G.edgeSet : ℚ) / Nat.card V ≤
          (Nat.card H.edgeSet : ℚ) / Nat.card U) ∧
        ∀ v : U,
          (Nat.card H.edgeSet : ℚ) / Nat.card U <
            (Nat.card (H.neighborSet v) : ℚ)) := by
  classical
  intro hE
  let candidate : Set (Set V) := {U | U.Nonempty}
  let ratio : Set V → ℚ := induced_ratio G
  have hfinite_candidate : candidate.Finite := Set.toFinite candidate
  have hV_nonempty : Nonempty V := by
    have hne : Nonempty G.edgeSet := (Finite.card_pos_iff.mp hE)
    let e : G.edgeSet := Classical.choice hne
    exact ⟨e.1.out.1⟩
  have hcandidate_nonempty : candidate.Nonempty := by
    exact ⟨Set.univ, by exact Set.univ_nonempty⟩
  obtain ⟨U₀, hU₀max⟩ :=
    hfinite_candidate.exists_maximalFor ratio candidate hcandidate_nonempty
  have hratio_le_U₀ : ∀ W : Set V, W.Nonempty → ratio W ≤ ratio U₀ := by
    intro W hW
    have hWcand : W ∈ candidate := hW
    rcases le_total (ratio W) (ratio U₀) with hle | hle
    · exact hle
    · exact hU₀max.2 hWcand hle
  let maxCandidate : Set (Set V) := {W | W.Nonempty ∧ ratio W = ratio U₀}
  have hfinite_maxCandidate : maxCandidate.Finite := Set.toFinite maxCandidate
  have hmaxCandidate_nonempty : maxCandidate.Nonempty :=
    ⟨U₀, hU₀max.1, rfl⟩
  obtain ⟨U, hUmin⟩ :=
    hfinite_maxCandidate.exists_minimalFor Set.ncard maxCandidate hmaxCandidate_nonempty
  have hUnonempty : U.Nonempty := hUmin.1.1
  have hUratio : ratio U = ratio U₀ := hUmin.1.2
  have hratio_ge_G :
      (Nat.card G.edgeSet : ℚ) / Nat.card V ≤ induced_ratio G U := by
    rw [← induced_ratio_univ G]
    change ratio Set.univ ≤ ratio U
    rw [hUratio]
    exact hratio_le_U₀ Set.univ Set.univ_nonempty
  have hUratio_pos : 0 < induced_ratio G U := by
    exact (induced_ratio_pos_of_edge G hE).trans_le hratio_ge_G
  refine ⟨U, hUnonempty, ?_, ?_⟩
  · exact hratio_ge_G
  · intro v
    by_contra hnot
    have hsmall :
        (Nat.card ((G.induce U).neighborSet v) : ℚ) ≤ induced_ratio G U := by
      exact le_of_not_gt hnot
    have hUncard : 1 < U.ncard :=
      one_lt_ncard_of_positive_induced_ratio G hUratio_pos
    have hUncard_nat : 1 < Nat.card U := by
      exact hUncard
    let W : Set V := U \ {v.1}
    have hratioUW : induced_ratio G U ≤ induced_ratio G W :=
      induced_delete_ratio_ge G v hUncard_nat hsmall
    have hWnonempty : W.Nonempty := by
      rw [Set.one_lt_ncard_iff] at hUncard
      obtain ⟨a, b, haU, hbU, hab⟩ := hUncard
      by_cases ha : a = v.1
      · exact ⟨b, hbU, by
          rw [Set.mem_singleton_iff]
          exact fun hb => hab (ha.trans hb.symm)⟩
      · exact ⟨a, haU, by
          rw [Set.mem_singleton_iff]
          exact ha⟩
    have hWmax : W ∈ maxCandidate := by
      have hWle : ratio W ≤ ratio U₀ := hratio_le_U₀ W hWnonempty
      have hU₀leW : ratio U₀ ≤ ratio W := by
        show ratio U₀ ≤ ratio W
        rw [← hUratio]
        exact hratioUW
      exact ⟨hWnonempty, le_antisymm hWle hU₀leW⟩
    have hWcard_lt : W.ncard < U.ncard :=
      Set.ncard_diff_singleton_lt_of_mem (s := U) v.2
    have hUcard_le_Wcard : U.ncard ≤ W.ncard :=
      hUmin.2 hWmax hWcard_lt.le
    omega

end Chapter01
end Diestel
