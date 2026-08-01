import «statements-and-proofs».Exponent7.CutResponder.FreshStrongClusterMatchingV2
import «statements-and-proofs».Exponent7.CutResponder.FreshClusterCutMatching

/-!
# Cut matching with existentially chosen fresh-cluster routings

The transcript and its host geometry do not depend on how a routing inside a
cluster was selected.  This module supplies the V2 producers while reusing
the frozen transcript structures and all their downstream minor lemmas.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w g : ℕ}

/-- Produce one geometric response from a V2 responder in the fresh block
belonging to round `r`. -/
noncomputable def freshStrongClusterRoundResponseV2
    {roundBound reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatementV2.{u}
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (hslots :
      roundBound * matchingBatchBudget responseConstant g ≤ ell)
    (P : StrongPathOfSetsSystem G ell w)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (r : Fin roundBound)
    (B : CutMatchingGame.Bisection (GridVertex g))
    (hdegree : MaxDegreeAtMost G 4)
    (hg : 2 ≤ g)
    (hwidth : reserve * g ^ 2 ≤ w)
    (hnogrid : ¬ ContainsGridMinor G g) :
    FreshStrongClusterRoundResponse
      hslots P selected r B := by
  classical
  let slot := roundClusterSlot hslots r
  have hbudget :
      responseConstant * (Nat.log 2 B.left.card + 1) ≤
        matchingBatchBudget responseConstant g :=
    bisection_batchBudget_le B responseConstant
  let hex :=
    exists_freshStrongClusterMatchingV2
      hclean hc P selected slot B hdegree hg hwidth hnogrid hbudget
  let M := Classical.choose hex
  have hM := Classical.choose_spec hex
  exact ⟨M, hM⟩

/-- Total V2 sequential responder.  Only bounded rounds carry host geometry;
the irrelevant tail uses the same total fallback as the frozen consumer. -/
noncomputable def freshClusterSequentialResponderV2
    {roundBound reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatementV2.{u}
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (hslots :
      roundBound * matchingBatchBudget responseConstant g ≤ ell)
    (P : StrongPathOfSetsSystem G ell w)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (hdegree : MaxDegreeAtMost G 4)
    (hg : 2 ≤ g)
    (hwidth : reserve * g ^ 2 ≤ w)
    (hnogrid : ¬ ContainsGridMinor G g) :
    CutMatchingGame.SequentialResponder (GridVertex g) :=
  fun n B =>
    if hn : n < roundBound then
      (freshStrongClusterRoundResponseV2
        hclean hc hslots P selected ⟨n, hn⟩ B
        hdegree hg hwidth hnogrid).geometric.toMatchingAcross
    else
      arbitraryMatchingAcross B

/-- The adversarial cut strategy supplied with the V2 responder produces the
same transcript type as the original consumer. -/
theorem exists_freshClusterCutMatchingTranscriptV2
    {roundBound reserve responseConstant : ℕ}
    (hstrategy :
      ∀ responder :
          CutMatchingGame.SequentialResponder (GridVertex g),
        ∃ rounds : List
            (CutMatchingGame.LazyRound (GridVertex g)),
          rounds.length = roundBound ∧
          CutMatchingGame.IsHalfEdgeExpander rounds ∧
          CutMatchingGame.FollowsResponder responder 0 rounds)
    (hclean :
      StrongClusterCleanActiveCutResponderStatementV2.{u}
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (hslots :
      roundBound * matchingBatchBudget responseConstant g ≤ ell)
    (P : StrongPathOfSetsSystem G ell w)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (hdegree : MaxDegreeAtMost G 4)
    (hg : 2 ≤ g)
    (hwidth : reserve * g ^ 2 ≤ w)
    (hnogrid : ¬ ContainsGridMinor G g) :
    Nonempty
      (FreshClusterCutMatchingTranscript
        hslots P selected) := by
  classical
  let responder :=
    freshClusterSequentialResponderV2
      hclean hc hslots P selected hdegree hg hwidth hnogrid
  rcases hstrategy responder with
    ⟨rounds, hlen, hhalf, hfollow⟩
  let cuts : Fin roundBound →
      CutMatchingGame.Bisection (GridVertex g) :=
    fun r => (rounds.get (Fin.cast hlen.symm r)).cut
  let response :
      ∀ r : Fin roundBound,
        FreshStrongClusterRoundResponse
          hslots P selected r (cuts r) :=
    fun r =>
      freshStrongClusterRoundResponseV2
        hclean hc hslots P selected r (cuts r)
        hdegree hg hwidth hnogrid
  let F :
      CutMatchingGame.RoundFamily
        (GridVertex g) (Fin roundBound) :=
    { cut := cuts
      matching := fun r =>
        (response r).geometric.toMatchingAcross }
  have hget :
      ∀ r : Fin roundBound,
        F.lazyRound r =
          rounds.get (Fin.cast hlen.symm r) := by
    intro r
    let ir : Fin rounds.length := Fin.cast hlen.symm r
    have hgetSome :
        rounds[ir.1]? = some (rounds.get ir) := by
      rw [List.get_eq_getElem]
      exact List.getElem?_eq_getElem ir.2
    have hfollow' :=
      hfollow ir.1 (rounds.get ir) hgetSome
    simpa [F, cuts, response, responder,
      CutMatchingGame.RoundFamily.lazyRound,
      CutMatchingGame.LazyRound.ofResponder,
      freshClusterSequentialResponderV2, ir, r.2] using hfollow'.symm
  have htoList : F.toFinList = rounds := by
    apply List.ext_get
    · rw [CutMatchingGame.RoundFamily.length_toFinList, hlen]
    · intro n hF hR
      have hrb : n < roundBound := by
        rw [← hlen]
        exact hR
      let r : Fin roundBound := ⟨n, hrb⟩
      have hcast :
          Fin.cast hlen.symm r =
            (⟨n, hR⟩ : Fin rounds.length) := by
        apply Fin.ext
        rfl
      have hleft :
          F.toFinList.get ⟨n, hF⟩ = F.lazyRound r := by
        dsimp [CutMatchingGame.RoundFamily.toFinList]
        simp [r]
      rw [hleft, hget r, hcast]
  have hFhalf : F.IsHalfEdgeExpander :=
    F.isHalfEdgeExpander_of_toFinList (by
      simpa [htoList] using hhalf)
  exact
    ⟨{ family := F
       half_expander := hFhalf
       response := response
       matching_eq := fun _ => rfl }⟩

end CutResponder
end Exponent7
end SimpleGraph
