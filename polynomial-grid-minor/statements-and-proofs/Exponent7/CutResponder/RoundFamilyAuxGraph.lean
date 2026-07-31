import «statements-and-proofs».Exponent7.CutResponder.FreshClusterCutMatching
import «statements-and-proofs».Separator

/-!
# The simple auxiliary graph of an abstract cut-matching transcript

The cut-matching game records matching edges with multiplicity by round.
For minor containment and separator arguments we also need the corresponding
simple union graph.  This module develops that bridge for an arbitrary
`CutMatchingGame.RoundFamily`; it does not use any hairy-crossbar geometry.
-/

namespace SimpleGraph
namespace CutMatchingGame

universe u

open Finset

variable {X : Type u} [Fintype X] [DecidableEq X]

namespace RoundFamily

/-- The simple graph obtained by forgetting the round multiplicity of the
matching union. -/
noncomputable def auxiliaryGraph
    {roundBound : ℕ}
    (F : RoundFamily X (Fin roundBound)) :
    _root_.SimpleGraph X where
  Adj x y :=
    ∃ e : F.Edge,
      (F.edgeSource e = x ∧ F.edgeTarget e = y) ∨
      (F.edgeSource e = y ∧ F.edgeTarget e = x)
  symm := by
    intro x y hxy
    rcases hxy with ⟨e, h | h⟩
    · exact ⟨e, Or.inr ⟨h.1, h.2⟩⟩
    · exact ⟨e, Or.inl ⟨h.1, h.2⟩⟩
  loopless := ⟨by
    intro x hxx
    rcases hxx with ⟨e, h | h⟩
    · exact F.edgeSource_ne_edgeTarget e (h.1.trans h.2.symm)
    · exact F.edgeSource_ne_edgeTarget e (h.1.trans h.2.symm)⟩

theorem auxiliaryGraph_adj_of_edge
    {roundBound : ℕ}
    (F : RoundFamily X (Fin roundBound))
    (e : F.Edge) :
    F.auxiliaryGraph.Adj (F.edgeSource e) (F.edgeTarget e) :=
  ⟨e, Or.inl ⟨rfl, rfl⟩⟩

/-- In one perfect-matching round, an incident vertex determines the matching
edge. -/
theorem edge_eq_of_same_round_of_common_endpoint
    {roundBound : ℕ}
    (F : RoundFamily X (Fin roundBound))
    {e f : F.Edge}
    (hr : e.1 = f.1)
    {z : X}
    (he :
      F.edgeSource e = z ∨ F.edgeTarget e = z)
    (hf :
      F.edgeSource f = z ∨ F.edgeTarget f = z) :
    e = f := by
  cases e with
  | mk re e =>
    cases f with
    | mk rf f =>
      dsimp at hr
      subst rf
      let r := re
      simp only [edgeSource, edgeTarget] at he hf
      have hef : e = f := by
        apply Subtype.ext
        rcases he with hes | het <;>
          rcases hf with hfs | hft
        · exact hes.trans hfs.symm
        · exfalso
          have hzLeft : z ∈ (F.cut r).left := by
            rw [← hes]
            exact e.2
          have hzRight : z ∈ (F.cut r).right := by
            rw [← hft]
            exact (F.matching r).rightEndpoint_mem f
          exact
            (F.cut r).not_mem_right_of_mem_left hzLeft hzRight
        · exfalso
          have hzRight : z ∈ (F.cut r).right := by
            rw [← het]
            exact (F.matching r).rightEndpoint_mem e
          have hzLeft : z ∈ (F.cut r).left := by
            rw [← hfs]
            exact f.2
          exact
            (F.cut r).not_mem_right_of_mem_left hzLeft hzRight
        · have hright :
              (F.matching r).toEquiv e =
                (F.matching r).toEquiv f := by
            apply Subtype.ext
            exact het.trans hft.symm
          exact congrArg Subtype.val
            ((F.matching r).toEquiv.injective hright)
      subst f
      rfl

/-- The endpoint outside `A` of a boundary edge.  Under a separator
hypothesis this endpoint will lie in the separator. -/
noncomputable def boundaryOutsideEndpoint
    {roundBound : ℕ}
    (F : RoundFamily X (Fin roundBound))
    (A : Finset X)
    (e : {e : F.Edge // e ∈ F.edgeBoundary A}) : X :=
  if F.edgeSource e.1 ∈ A then
    F.edgeTarget e.1
  else
    F.edgeSource e.1

theorem boundaryOutsideEndpoint_incident
    {roundBound : ℕ}
    (F : RoundFamily X (Fin roundBound))
    (A : Finset X)
    (e : {e : F.Edge // e ∈ F.edgeBoundary A}) :
    F.edgeSource e.1 = F.boundaryOutsideEndpoint A e ∨
      F.edgeTarget e.1 = F.boundaryOutsideEndpoint A e := by
  classical
  unfold boundaryOutsideEndpoint
  by_cases hs : F.edgeSource e.1 ∈ A
  · simp [hs]
  · simp [hs]

theorem boundaryOutsideEndpoint_mem_separator
    {roundBound : ℕ}
    (F : RoundFamily X (Fin roundBound))
    (A B S : Finset X)
    (hcover : A ∪ B ∪ S = Finset.univ)
    (hnoAB :
      ∀ ⦃a b : X⦄, a ∈ A → b ∈ B →
        ¬ F.auxiliaryGraph.Adj a b)
    (e : {e : F.Edge // e ∈ F.edgeBoundary A}) :
    F.boundaryOutsideEndpoint A e ∈ S := by
  classical
  have hcross :
      F.edgeCrosses A e.1 :=
    (F.mem_edgeBoundary).mp e.2
  by_cases hs : F.edgeSource e.1 ∈ A
  · have htNotA : F.edgeTarget e.1 ∉ A := by
      rcases hcross with h | h
      · exact h.2
      · exact False.elim (h.2 hs)
    have htNotB : F.edgeTarget e.1 ∉ B := by
      intro htB
      exact
        hnoAB hs htB (F.auxiliaryGraph_adj_of_edge e.1)
    have htAll :
        F.edgeTarget e.1 ∈ A ∪ B ∪ S := by
      rw [hcover]
      simp
    have htS : F.edgeTarget e.1 ∈ S := by
      rcases Finset.mem_union.mp htAll with htAB | htS
      · rcases Finset.mem_union.mp htAB with htA | htB
        · exact False.elim (htNotA htA)
        · exact False.elim (htNotB htB)
      · exact htS
    simpa [boundaryOutsideEndpoint, hs] using htS
  · have htA : F.edgeTarget e.1 ∈ A := by
      rcases hcross with h | h
      · exact False.elim (hs h.1)
      · exact h.1
    have hsNotB : F.edgeSource e.1 ∉ B := by
      intro hsB
      exact
        hnoAB htA hsB
          (F.auxiliaryGraph.symm
            (F.auxiliaryGraph_adj_of_edge e.1))
    have hsAll :
        F.edgeSource e.1 ∈ A ∪ B ∪ S := by
      rw [hcover]
      simp
    have hsS : F.edgeSource e.1 ∈ S := by
      rcases Finset.mem_union.mp hsAll with hsAB | hsS
      · rcases Finset.mem_union.mp hsAB with hsA | hsB
        · exact False.elim (hs hsA)
        · exact False.elim (hsNotB hsB)
      · exact hsS
    simpa [boundaryOutsideEndpoint, hs] using hsS

/-- Charge every boundary edge to its outside separator endpoint and its
round. -/
noncomputable def boundarySeparatorCharge
    {roundBound : ℕ}
    (F : RoundFamily X (Fin roundBound))
    (A B S : Finset X)
    (hcover : A ∪ B ∪ S = Finset.univ)
    (hnoAB :
      ∀ ⦃a b : X⦄, a ∈ A → b ∈ B →
        ¬ F.auxiliaryGraph.Adj a b) :
    {e : F.Edge // e ∈ F.edgeBoundary A} →
      ({x : X // x ∈ S} × Fin roundBound) :=
  fun e =>
    (⟨F.boundaryOutsideEndpoint A e,
      F.boundaryOutsideEndpoint_mem_separator
        A B S hcover hnoAB e⟩,
      e.1.1)

theorem boundarySeparatorCharge_injective
    {roundBound : ℕ}
    (F : RoundFamily X (Fin roundBound))
    (A B S : Finset X)
    (hcover : A ∪ B ∪ S = Finset.univ)
    (hnoAB :
      ∀ ⦃a b : X⦄, a ∈ A → b ∈ B →
        ¬ F.auxiliaryGraph.Adj a b) :
    Function.Injective
      (F.boundarySeparatorCharge A B S hcover hnoAB) := by
  classical
  intro e f hef
  apply Subtype.ext
  have hr : e.1.1 = f.1.1 :=
    congrArg (fun p => p.2) hef
  have hz :
      F.boundaryOutsideEndpoint A e =
        F.boundaryOutsideEndpoint A f :=
    congrArg (fun p => p.1.1) hef
  apply F.edge_eq_of_same_round_of_common_endpoint hr
      (z := F.boundaryOutsideEndpoint A e)
  · exact F.boundaryOutsideEndpoint_incident A e
  · rw [hz]
    exact F.boundaryOutsideEndpoint_incident A f

/-- Separator charging bounds the multigraph boundary by one incident edge per
separator vertex per round. -/
theorem edgeBoundary_card_le_separator_card_mul_rounds
    {roundBound : ℕ}
    (F : RoundFamily X (Fin roundBound))
    (A B S : Finset X)
    (hcover : A ∪ B ∪ S = Finset.univ)
    (hnoAB :
      ∀ ⦃a b : X⦄, a ∈ A → b ∈ B →
        ¬ F.auxiliaryGraph.Adj a b) :
    (F.edgeBoundary A).card ≤ S.card * roundBound := by
  classical
  have hle :
      Fintype.card {e : F.Edge // e ∈ F.edgeBoundary A} ≤
        Fintype.card ({x : X // x ∈ S} × Fin roundBound) :=
    Fintype.card_le_of_injective
      (F.boundarySeparatorCharge A B S hcover hnoAB)
      (F.boundarySeparatorCharge_injective A B S hcover hnoAB)
  have hcodomain :
      Fintype.card ({x : X // x ∈ S} × Fin roundBound) =
        S.card * roundBound := by
    simp
  calc
    (F.edgeBoundary A).card =
        Fintype.card ↥(F.edgeBoundary A) :=
      (Fintype.card_coe (F.edgeBoundary A)).symm
    _ ≤ Fintype.card
          ({x : X // x ∈ S} × Fin roundBound) :=
      hle
    _ = S.card * roundBound := hcodomain

/-- A half-expanding `roundBound`-round transcript has no balanced separator
at scale `24 * roundBound`.  This is the generic form of the separator
argument formerly available only for the hairy-crossbar transcript. -/
theorem noSmallBalancedSeparator_auxiliaryGraph
    {roundBound : ℕ}
    (F : RoundFamily X (Fin roundBound))
    (hhalf : F.IsHalfEdgeExpander)
    (hroundPos : 0 < roundBound) :
    NoSmallBalancedSeparator F.auxiliaryGraph (24 * roundBound) := by
  classical
  intro A B S Sep
  by_contra hnot
  have hsmall :
      24 * (S.card * roundBound) < Fintype.card X := by
    have hsmall' :
        (24 * roundBound) * S.card < Fintype.card X :=
      Nat.lt_of_not_ge hnot
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsmall'
  by_cases hApos : 0 < A.card
  · have hAleB : A.card ≤ B.card :=
      Sep.left_card_le_right_card
    have hBbalanced :
        3 * B.card ≤ 2 * Fintype.card X :=
      Sep.right_balanced
    have hABle :
        A.card + B.card ≤ Fintype.card X := by
      have hle :
          (A ∪ B).card ≤ Fintype.card X := by
        simpa using
          Finset.card_le_card
            (Finset.subset_univ (A ∪ B))
      rw [Finset.card_union_of_disjoint
        Sep.disjoint_left_right] at hle
      exact hle
    have hhalfA : 2 * A.card ≤ Fintype.card X := by
      omega
    have hExp :
        A.card ≤ 2 * (F.edgeBoundary A).card :=
      hhalf A hApos hhalfA
    have hBoundary :
        (F.edgeBoundary A).card ≤ S.card * roundBound :=
      F.edgeBoundary_card_le_separator_card_mul_rounds
        A B S Sep.cover Sep.no_edge_left_right
    have hUpper :
        A.card ≤ 2 * (S.card * roundBound) :=
      hExp.trans (Nat.mul_le_mul_left 2 hBoundary)
    have hAB_S : Disjoint (A ∪ B) S := by
      rw [Finset.disjoint_left]
      intro x hx hSx
      rcases Finset.mem_union.mp hx with hxA | hxB
      · exact
          Finset.disjoint_left.mp
            Sep.disjoint_left_separator hxA hSx
      · exact
          Finset.disjoint_left.mp
            Sep.disjoint_right_separator hxB hSx
    have hcardAB :
        (A ∪ B).card = A.card + B.card :=
      Finset.card_union_of_disjoint
        Sep.disjoint_left_right
    have hcardABS :
        ((A ∪ B) ∪ S).card =
          (A ∪ B).card + S.card :=
      Finset.card_union_of_disjoint hAB_S
    have hcardCover :
        ((A ∪ B) ∪ S).card = Fintype.card X := by
      rw [Sep.cover]
      simp
    have hpartition :
        A.card + B.card + S.card =
          Fintype.card X := by
      omega
    have hSle :
        S.card ≤ S.card * roundBound :=
      Nat.le_mul_of_pos_right S.card hroundPos
    have hSsmall :
        24 * S.card < Fintype.card X :=
      lt_of_le_of_lt
        (Nat.mul_le_mul_left 24 hSle) hsmall
    have hNle6A :
        Fintype.card X ≤ 6 * A.card := by
      omega
    have hNle12 :
        Fintype.card X ≤
          6 * (2 * (S.card * roundBound)) :=
      hNle6A.trans (Nat.mul_le_mul_left 6 hUpper)
    omega
  · have hAzero : A.card = 0 :=
      Nat.eq_zero_of_not_pos hApos
    have hAB_S : Disjoint (A ∪ B) S := by
      rw [Finset.disjoint_left]
      intro x hx hSx
      rcases Finset.mem_union.mp hx with hxA | hxB
      · exact
          Finset.disjoint_left.mp
            Sep.disjoint_left_separator hxA hSx
      · exact
          Finset.disjoint_left.mp
            Sep.disjoint_right_separator hxB hSx
    have hcardAB :
        (A ∪ B).card = A.card + B.card :=
      Finset.card_union_of_disjoint
        Sep.disjoint_left_right
    have hcardABS :
        ((A ∪ B) ∪ S).card =
          (A ∪ B).card + S.card :=
      Finset.card_union_of_disjoint hAB_S
    have hcardCover :
        ((A ∪ B) ∪ S).card =
          Fintype.card X := by
      rw [Sep.cover]
      simp
    have hpartition :
        A.card + B.card + S.card =
          Fintype.card X := by
      omega
    have hSle :
        S.card ≤ S.card * roundBound :=
      Nat.le_mul_of_pos_right S.card hroundPos
    have hNle3S :
        Fintype.card X ≤ 3 * S.card := by
      nlinarith [hAzero, hpartition,
        Sep.right_balanced]
    have hNle24 :
        Fintype.card X ≤
          24 * (S.card * roundBound) := by
      nlinarith [hNle3S, hSle]
    omega

end RoundFamily
end CutMatchingGame
end SimpleGraph
