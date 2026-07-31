import «statements-and-proofs».Exponent7.CutResponder.FreshStrongClusterMatching
import «statements-and-proofs».CutMatchingGameBudget

/-!
# Cut matching with fresh strong clusters

This module assigns a disjoint block of strong-system clusters to every
cut-matching round.  Inside one block, logarithmic fractional peeling realizes
the responder's exact perfect matching.  Across rounds the blocks are
disjoint.

The resulting `RoundFamily` is the abstract half-expander produced by the
existing adversarial cut strategy, but every one of its matching edges retains
a concrete clean path in the host graph.

The application-specific clean active responder remains an explicit
proposition parameter.  No axiom is declared here.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w g : ℕ}

/-- Uniform fresh-cluster budget for one bisection.  We deliberately use the
full `g^2` coordinate count rather than the definitionally smaller left side,
so the same block size works for every cut selected by the adversary. -/
def matchingBatchBudget (responseConstant g : ℕ) : ℕ :=
  responseConstant * (Nat.log 2 (g ^ 2) + 1)

/-- The `t`-th cluster slot in the block assigned to round `r`. -/
def roundClusterSlot
    {roundBound batchBudget ell : ℕ}
    (hslots : roundBound * batchBudget ≤ ell)
    (r : Fin roundBound) :
    Fin batchBudget ↪ Fin ell where
  toFun t :=
    ⟨r.1 * batchBudget + t.1, by
      calc
        r.1 * batchBudget + t.1 <
            r.1 * batchBudget + batchBudget :=
          Nat.add_lt_add_left t.2 _
        _ = (r.1 + 1) * batchBudget := by
          simp [Nat.add_mul]
        _ ≤ roundBound * batchBudget :=
          Nat.mul_le_mul_right batchBudget (Nat.succ_le_iff.mpr r.2)
        _ ≤ ell := hslots⟩
  inj' := by
    intro a b hab
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val hab)

@[simp]
theorem roundClusterSlot_val
    {roundBound batchBudget ell : ℕ}
    (hslots : roundBound * batchBudget ≤ ell)
    (r : Fin roundBound) (t : Fin batchBudget) :
    (roundClusterSlot hslots r t).1 =
      r.1 * batchBudget + t.1 :=
  rfl

/-- Distinct round/batch pairs use distinct cluster indices. -/
theorem roundClusterSlot_ne
    {roundBound batchBudget ell : ℕ}
    (hslots : roundBound * batchBudget ≤ ell)
    {r s : Fin roundBound} {a b : Fin batchBudget}
    (hrs : r ≠ s ∨ a ≠ b) :
    roundClusterSlot hslots r a ≠
      roundClusterSlot hslots s b := by
  intro heq
  have hrsEq : r = s := by
    apply Fin.ext
    have hval :
        r.1 * batchBudget + a.1 =
          s.1 * batchBudget + b.1 :=
      congrArg Fin.val heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hrslt | hsrlt
    · have hmul :
          (r.1 + 1) * batchBudget ≤ s.1 * batchBudget :=
        Nat.mul_le_mul_right batchBudget
          (Nat.succ_le_iff.mpr hrslt)
      have ha :
          r.1 * batchBudget + a.1 <
            (r.1 + 1) * batchBudget := by
        calc
          r.1 * batchBudget + a.1 <
              r.1 * batchBudget + batchBudget :=
            Nat.add_lt_add_left a.2 _
          _ = (r.1 + 1) * batchBudget := by
            simp [Nat.add_mul]
      have hb :
          s.1 * batchBudget ≤
            s.1 * batchBudget + b.1 :=
        Nat.le_add_right _ _
      omega
    · have hmul :
          (s.1 + 1) * batchBudget ≤ r.1 * batchBudget :=
        Nat.mul_le_mul_right batchBudget
          (Nat.succ_le_iff.mpr hsrlt)
      have hb :
          s.1 * batchBudget + b.1 <
            (s.1 + 1) * batchBudget := by
        calc
          s.1 * batchBudget + b.1 <
              s.1 * batchBudget + batchBudget :=
            Nat.add_lt_add_left b.2 _
          _ = (s.1 + 1) * batchBudget := by
            simp [Nat.add_mul]
      have ha :
          r.1 * batchBudget ≤
            r.1 * batchBudget + a.1 :=
        Nat.le_add_right _ _
      omega
  rcases hrs with hrs | hab
  · exact hrs hrsEq
  · subst s
    exact hab ((roundClusterSlot hslots r).injective heq)

/-- One bisection response, retaining the geometric matching that realizes the
abstract move. -/
structure FreshStrongClusterRoundResponse
    {roundBound responseConstant : ℕ}
    (hslots :
      roundBound * matchingBatchBudget responseConstant g ≤ ell)
    (P : StrongPathOfSetsSystem G ell w)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (r : Fin roundBound)
    (B : CutMatchingGame.Bisection (GridVertex g)) where
  geometric :
    CleanGeometricPeeledMatching
      (fun x : GridVertex g =>
        (GlobalRowPrefix.globalRows P).packing.path (selected x))
      (allSelectedGlobalRowVertexSet P selected)
      (fun t =>
        P.cluster
          (roundClusterSlot hslots r t))
      B.left B.right responseConstant 0
  batchCount_le :
    geometric.matching.batchCount ≤
      responseConstant * (Nat.log 2 B.left.card + 1)

/-- Every bisection side fits the uniform one-round logarithmic budget. -/
theorem bisection_batchBudget_le
    (B : CutMatchingGame.Bisection (GridVertex g))
    (responseConstant : ℕ) :
    responseConstant * (Nat.log 2 B.left.card + 1) ≤
      matchingBatchBudget responseConstant g := by
  have hcard :
      B.left.card ≤ g ^ 2 := by
    simpa [card_gridVertex, pow_two] using
      (Finset.card_le_univ B.left)
  have hlog :
      Nat.log 2 B.left.card ≤ Nat.log 2 (g ^ 2) :=
    Nat.log_mono_right hcard
  exact Nat.mul_le_mul_left responseConstant (Nat.add_le_add_right hlog 1)

/-- Produce the geometric response in the block belonging to `r`. -/
noncomputable def freshStrongClusterRoundResponse
    {roundBound reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatement.{u}
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
  let slot :=
    roundClusterSlot hslots r
  have hbudget :
      responseConstant * (Nat.log 2 B.left.card + 1) ≤
        matchingBatchBudget responseConstant g :=
    bisection_batchBudget_le B responseConstant
  let hex :=
    exists_freshStrongClusterMatching
      hclean hc P selected slot B hdegree hg hwidth hnogrid hbudget
  let M := Classical.choose hex
  have hM := Classical.choose_spec hex
  exact ⟨M, hM⟩

/-- A harmless total fallback matching.  It is used only outside the bounded
round interval and therefore carries no host geometry. -/
noncomputable def arbitraryMatchingAcross
    {X : Type*} [Fintype X] [DecidableEq X]
    (B : CutMatchingGame.Bisection X) :
    CutMatchingGame.MatchingAcross B where
  toEquiv :=
    Fintype.equivOfCardEq (by
      simpa only [Fintype.card_coe] using B.card_eq)

/-- Total sequential responder whose bounded rounds are realized in their
assigned fresh-cluster blocks. -/
noncomputable def freshClusterSequentialResponder
    {roundBound reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatement.{u}
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
      (freshStrongClusterRoundResponse
        hclean hc hslots P selected ⟨n, hn⟩ B
        hdegree hg hwidth hnogrid).geometric.toMatchingAcross
    else
      arbitraryMatchingAcross B

/-- The parallel Task-D output at the abstract/geometric interface: a
half-expanding round family and, for every round, the exact clean host
realization chosen by its responder. -/
structure FreshClusterCutMatchingTranscript
    {roundBound responseConstant : ℕ}
    (hslots :
      roundBound * matchingBatchBudget responseConstant g ≤ ell)
    (P : StrongPathOfSetsSystem G ell w)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index) where
  family :
    CutMatchingGame.RoundFamily
      (GridVertex g) (Fin roundBound)
  half_expander : family.IsHalfEdgeExpander
  response :
    ∀ r : Fin roundBound,
      FreshStrongClusterRoundResponse
        hslots P selected r (family.cut r)
  matching_eq :
    ∀ r : Fin roundBound,
      family.matching r =
        (response r).geometric.toMatchingAcross

/-- The existing adversarial cut strategy, supplied with the fresh-cluster
responder, produces the transcript above. -/
theorem exists_freshClusterCutMatchingTranscript
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
      StrongClusterCleanActiveCutResponderStatement.{u}
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
    freshClusterSequentialResponder
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
      freshStrongClusterRoundResponse
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
      freshClusterSequentialResponder, ir, r.2] using hfollow'.symm
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
