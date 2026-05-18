import Mathlib.Tactic
import TwinWidth.Graph.GridMinor
import TwinWidth.Graph.PathOfSets

/-!
# Stitched rows for the Chekuri--Chuzhoy path-of-sets theorem

This module contains the interface data extracted from Chekuri--Chuzhoy,
Corollary 3.2, in the form needed by the Appendix C.1 sparse-grid assembly.
It is kept separate from the assembly proof so the contract file can state only
the missing extraction theorem.
-/

namespace TwinWidth
namespace SimpleGraph
namespace ChekuriChuzhoy

universe u

/-- The zero-based index of the `i`th even one-based cluster used in
Chekuri--Chuzhoy Appendix C.  The paper's clusters `S_2, S_4, ...` correspond
to Lean indices `1, 3, ...`. -/
def evenClusterIndex (g : ℕ) (i : Fin (g * (g - 1))) :
    Fin (2 * g * (g - 1)) :=
  ⟨2 * i.1 + 1, by
    have hi : i.1 < g * (g - 1) := i.2
    have hsucc : i.1 + 1 ≤ g * (g - 1) := Nat.succ_le_of_lt hi
    calc
      2 * i.1 + 1 < 2 * (i.1 + 1) := by omega
      _ ≤ 2 * (g * (g - 1)) := Nat.mul_le_mul_left 2 hsucc
      _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]⟩

@[simp] theorem evenClusterIndex_val (g : ℕ)
    (i : Fin (g * (g - 1))) :
    (evenClusterIndex g i).1 = 2 * i.1 + 1 := rfl

theorem evenClusterIndex_lt_of_lt {g : ℕ}
    {i j : Fin (g * (g - 1))} (hij : i.1 < j.1) :
    (evenClusterIndex g i).1 < (evenClusterIndex g j).1 := by
  simp [evenClusterIndex]
  omega

theorem evenClusterIndex_injective {g : ℕ} :
    Function.Injective (evenClusterIndex g) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp [evenClusterIndex] at hval
  omega

/-- The next even one-based cluster ordinal, when it exists. -/
def nextEvenClusterOrdinal {g : ℕ} (i : Fin (g * (g - 1)))
    (hi : i.1 + 1 < g * (g - 1)) : Fin (g * (g - 1)) :=
  ⟨i.1 + 1, hi⟩

@[simp] theorem nextEvenClusterOrdinal_val {g : ℕ}
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (nextEvenClusterOrdinal i hi).1 = i.1 + 1 := rfl

/-- The last even one-based cluster ordinal, when the path-of-sets system has
at least one even one-based cluster. -/
def lastEvenClusterOrdinal {g : ℕ} (hN : 0 < g * (g - 1)) :
    Fin (g * (g - 1)) :=
  ⟨g * (g - 1) - 1, Nat.sub_lt hN (by decide : 0 < 1)⟩

@[simp] theorem lastEvenClusterOrdinal_val {g : ℕ}
    (hN : 0 < g * (g - 1)) :
    (lastEvenClusterOrdinal hN).1 = g * (g - 1) - 1 := rfl

/-- The last even one-based cluster is exactly the last cluster of a
`2 * g * (g - 1)`-long path-of-sets system. -/
theorem evenClusterIndex_lastEven_eq_lastIndex {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1)) :
    evenClusterIndex g (lastEvenClusterOrdinal hN) = P.lastIndex := by
  apply Fin.ext
  dsimp [lastEvenClusterOrdinal, evenClusterIndex, PathOfSetsSystem.lastIndex]
  rw [Nat.mul_assoc]
  set N := g * (g - 1)
  have hN_one : 1 ≤ N := by
    simpa [N] using Nat.succ_le_of_lt hN
  omega

/-- The odd one-based cluster lying immediately after an even one-based
cluster.  In Lean's zero-based indexing this is the cluster after
`evenClusterIndex g i`. -/
def oddClusterAfterEvenIndex (g : ℕ) (i : Fin (g * (g - 1)))
    (hi : i.1 + 1 < g * (g - 1)) :
    Fin (2 * g * (g - 1)) :=
  ⟨2 * i.1 + 2, by
    have hmul : 2 * (i.1 + 1) < 2 * (g * (g - 1)) :=
      Nat.mul_lt_mul_of_pos_left hi (by decide : 0 < 2)
    calc
      2 * i.1 + 2 = 2 * (i.1 + 1) := by omega
      _ < 2 * (g * (g - 1)) := hmul
      _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]⟩

@[simp] theorem oddClusterAfterEvenIndex_val (g : ℕ)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (oddClusterAfterEvenIndex g i hi).1 = 2 * i.1 + 2 := rfl

/-- The cluster after the odd cluster between two consecutive even one-based
clusters is the next even one-based cluster. -/
theorem oddClusterAfterEvenIndex_succ_eq_nextEven (g : ℕ)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (⟨(oddClusterAfterEvenIndex g i hi).1 + 1, by
      have hsucc : i.1 + 2 ≤ g * (g - 1) := Nat.succ_le_of_lt hi
      calc
        (oddClusterAfterEvenIndex g i hi).1 + 1 = 2 * i.1 + 3 := by
          simp [oddClusterAfterEvenIndex]
        _ < 2 * (i.1 + 2) := by omega
        _ ≤ 2 * (g * (g - 1)) := Nat.mul_le_mul_left 2 hsucc
        _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]⟩ : Fin (2 * g * (g - 1))) =
      evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
  apply Fin.ext
  simp [oddClusterAfterEvenIndex, nextEvenClusterOrdinal, evenClusterIndex]
  omega

/-- The local output obtained by applying Chekuri--Chuzhoy Theorem 3.1 inside
one even one-based cluster: a fixed-size family of disjoint left-to-right paths
inside that cluster, plus pairwise bridges localized to the cluster.

Appendix C stitches these outputs through the intervening odd clusters to
produce the global `StitchedRows` object. -/
structure EvenClusterOutput {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (i : Fin (g * (g - 1))) (q : ℕ) where
  /-- The local row pieces returned in the even cluster. -/
  paths : PathPacking G (P.left (evenClusterIndex g i))
    (P.right (evenClusterIndex g i))
  /-- The number of local row pieces. -/
  paths_card : paths.card = q
  /-- The local row pieces stay inside the even cluster. -/
  paths_staysIn :
    paths.StaysIn (P.cluster (evenClusterIndex g i))
  /-- The local bridge guarantee from Chekuri--Chuzhoy Theorem 3.1. -/
  pairwise_bridges :
    paths.HasPairwiseBridgesIn (P.cluster (evenClusterIndex g i))

/-- Local outputs for all even one-based clusters of a path-of-sets system. -/
structure EvenClusterOutputs {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w) (q : ℕ) where
  /-- The local output assigned to each even one-based cluster. -/
  output : ∀ i : Fin (g * (g - 1)), EvenClusterOutput P i q

namespace EvenClusterOutput

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {g w q : ℕ}

/-- Consecutive local even-cluster outputs can be stitched through the
intervening odd cluster.

This is the formal local step in Appendix C of Chekuri--Chuzhoy: the target
endpoints used by the first even-cluster output and the source endpoints used
by the next even-cluster output have the same size, so the strong
Path-of-Sets linkage through the two connector gaps and the odd cluster gives
a perfect packing between them. -/
theorem exists_stitchingPacking_to_next
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    {i : Fin (g * (g - 1))} (hi : i.1 + 1 < g * (g - 1))
    (E : EvenClusterOutput P.toPathOfSetsSystem i q)
    (E_next :
      EvenClusterOutput P.toPathOfSetsSystem (nextEvenClusterOrdinal i hi) q) :
    ∃ S : PerfectPathPacking G E.paths.targetSet E_next.paths.sourceSet,
      S.card = q ∧
        S.toPathPacking.InternallyDisjointFromSet
          (P.cluster (evenClusterIndex g i)) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) := by
  classical
  let e := evenClusterIndex g i
  let eOdd := oddClusterAfterEvenIndex g i hi
  have hOddSucc : eOdd.1 + 1 < 2 * g * (g - 1) := by
    have hsucc : i.1 + 2 ≤ g * (g - 1) := Nat.succ_le_of_lt hi
    calc
      eOdd.1 + 1 = 2 * i.1 + 3 := by
        simp [eOdd, oddClusterAfterEvenIndex]
      _ < 2 * (i.1 + 2) := by omega
      _ ≤ 2 * (g * (g - 1)) := Nat.mul_le_mul_left 2 hsucc
      _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]
  have hnext :
      (⟨eOdd.1 + 1, hOddSucc⟩ : Fin (2 * g * (g - 1))) =
        evenClusterIndex g (nextEvenClusterOrdinal i hi) := by
    simpa [eOdd] using oddClusterAfterEvenIndex_succ_eq_nextEven g i hi
  have hR : E.paths.targetSet ⊆ P.right e := by
    simpa [e] using E.paths.targetSet_subset_right
  have hL :
      E_next.paths.sourceSet ⊆
        P.left
          (⟨eOdd.1 + 1, hOddSucc⟩ : Fin (2 * g * (g - 1))) := by
    intro v hv
    rw [hnext]
    exact E_next.paths.sourceSet_subset_left hv
  have hcard :
      E.paths.targetSet.card = E_next.paths.sourceSet.card := by
    rw [PathPacking.targetSet_card, PathPacking.sourceSet_card,
      E.paths_card, E_next.paths_card]
  rcases P.exists_twoGap_concatPacking_between_subsets e
      (by simpa [eOdd] using (oddClusterAfterEvenIndex g i hi).2)
      hOddSucc
      hR hL hcard with
    ⟨S, hS_card, _hS_stays, hS_first, hS_last⟩
  refine ⟨S, ?_, by simpa [e] using hS_first, ?_⟩
  · exact hS_card.trans (by rw [PathPacking.targetSet_card, E.paths_card])
  · simpa [hnext] using hS_last

/-- The first local even-cluster output can be connected back to the first
left nail set of the path-of-sets system.

This is the initial stitching step in Appendix C: the strong linkage in the
first cluster and the first connector path family route a selected set of
`q` paths from `A₁` to the source endpoints used in the first even cluster. -/
theorem exists_startPacking_to_first
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P.toPathOfSetsSystem ⟨0, hN⟩ q) :
    ∃ S : PathPacking G (P.left P.firstIndex) E.paths.sourceSet,
      S.card = q := by
  classical
  let firstEven : Fin (g * (g - 1)) := ⟨0, hN⟩
  have hgap : P.firstIndex.1 + 1 < 2 * g * (g - 1) := by
    have hN_one : 1 ≤ g * (g - 1) := Nat.succ_le_of_lt hN
    calc
      P.firstIndex.1 + 1 = 1 := by simp [PathOfSetsSystem.firstIndex]
      _ < 2 * (g * (g - 1)) := by omega
      _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]
  have hfirstEven :
      (⟨P.firstIndex.1 + 1, hgap⟩ : Fin (2 * g * (g - 1))) =
        evenClusterIndex g firstEven := by
    apply Fin.ext
    simp [PathOfSetsSystem.firstIndex, firstEven, evenClusterIndex]
  let L : PerfectPathPacking G (P.left P.firstIndex)
      (P.left ⟨P.firstIndex.1 + 1, hgap⟩) :=
    P.leftNextPacking P.firstIndex hgap
  have hT :
      E.paths.sourceSet ⊆ P.left ⟨P.firstIndex.1 + 1, hgap⟩ := by
    intro v hv
    rw [hfirstEven]
    exact E.paths.sourceSet_subset_left hv
  let R : PerfectPathPacking G
      (L.sourceSet (L.targetIndexSetOfSubset E.paths.sourceSet))
      E.paths.sourceSet :=
    L.restrictTargetSet E.paths.sourceSet hT
  have hRsource :
      L.sourceSet (L.targetIndexSetOfSubset E.paths.sourceSet) ⊆
        P.left P.firstIndex := by
    exact L.sourceSet_subset_left (L.targetIndexSetOfSubset E.paths.sourceSet)
  refine ⟨R.toPathPacking.widenTerminals hRsource (by intro v hv; exact hv),
    ?_⟩
  calc
    (R.toPathPacking.widenTerminals hRsource (by intro v hv; exact hv)).card =
        R.card := rfl
    _ = E.paths.sourceSet.card := by simp [R]
    _ = E.paths.card := by rw [PathPacking.sourceSet_card]
    _ = q := E.paths_card

/-- The last local even-cluster output can be viewed as ending in the last
right nail set of the whole path-of-sets system.

This is the terminal bookkeeping step in Appendix C: the last even one-based
cluster is the final cluster of the `2 * g * (g - 1)`-cluster system, so no
additional connector is needed after the last local output. -/
def toLastRight
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P (lastEvenClusterOrdinal hN) q) :
    PathPacking G
      (P.left (evenClusterIndex g (lastEvenClusterOrdinal hN)))
      (P.right P.lastIndex) :=
  E.paths.widenTerminals (by intro v hv; exact hv) (by
    intro v hv
    rw [← evenClusterIndex_lastEven_eq_lastIndex P hN]
    exact hv)

@[simp] theorem toLastRight_card
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P (lastEvenClusterOrdinal hN) q) :
    (E.toLastRight P hN).card = q := by
  simpa [toLastRight] using E.paths_card

end EvenClusterOutput

namespace EvenClusterOutputs

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {g w q : ℕ}

/-- Consecutive entries in a family of local even-cluster outputs can be
stitched through the odd one-based cluster between them. -/
theorem exists_stitchingPacking_to_next
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    {i : Fin (g * (g - 1))} (hi : i.1 + 1 < g * (g - 1)) :
    ∃ S : PerfectPathPacking G (E.output i).paths.targetSet
        ((E.output (nextEvenClusterOrdinal i hi)).paths.sourceSet),
      S.card = q ∧
        S.toPathPacking.InternallyDisjointFromSet
          (P.cluster (evenClusterIndex g i)) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) :=
  (E.output i).exists_stitchingPacking_to_next P hi
    (E.output (nextEvenClusterOrdinal i hi))

/-- The first local output in a family can be connected back to the first left
nail set of the whole path-of-sets system. -/
theorem exists_startPacking_to_first
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (hN : 0 < g * (g - 1)) :
    ∃ S : PathPacking G (P.left P.firstIndex)
        ((E.output ⟨0, hN⟩).paths.sourceSet),
      S.card = q :=
  (E.output ⟨0, hN⟩).exists_startPacking_to_first P hN

/-- The last local output in a family can be viewed as ending in the last right
nail set of the whole path-of-sets system. -/
def toLastRight
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P q)
    (hN : 0 < g * (g - 1)) :
    PathPacking G
      (P.left (evenClusterIndex g (lastEvenClusterOrdinal hN)))
      (P.right P.lastIndex) :=
  (E.output (lastEvenClusterOrdinal hN)).toLastRight P hN

@[simp] theorem toLastRight_card
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P q)
    (hN : 0 < g * (g - 1)) :
    (E.toLastRight P hN).card = q := by
  simp [toLastRight,
    (E.output (lastEvenClusterOrdinal hN)).toLastRight_card P hN]

end EvenClusterOutputs

/-- For `g ≥ 2`, the number `g * (g - 1)` of even one-based clusters used by
Appendix C is positive. -/
theorem evenClusterOrdinal_count_pos_of_two_le {g : ℕ} (hg : 2 ≤ g) :
    0 < g * (g - 1) := by
  exact Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 2) hg)
    (Nat.sub_pos_of_lt hg)

/-- The canonical stitching pieces between local even-cluster outputs.

The start piece connects the first left nail set to the first local output.
For every consecutive pair of even one-based clusters, `between` is the
perfect packing through the intervening odd cluster supplied by the strong
path-of-sets linkage.  The last local output is exposed by `last`.

The remaining Appendix C work after this structure is to concatenate these
pieces with the local outputs, then prove the trace and ordering fields of
`StitchedRows`. -/
structure StitchingPieces {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w q : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q) where
  /-- Positivity of the even-cluster ordinal set. -/
  hN : 0 < g * (g - 1)
  /-- Initial linkage from the first left nails to the first local output. -/
  start :
    PathPacking G (P.left P.firstIndex) ((E.output ⟨0, hN⟩).paths.sourceSet)
  /-- The initial linkage has the intended cardinality. -/
  start_card : start.card = q
  /-- Stitching linkages between consecutive local even-cluster outputs. -/
  between :
    (i : Fin (g * (g - 1))) → (hi : i.1 + 1 < g * (g - 1)) →
      PerfectPathPacking G (E.output i).paths.targetSet
        ((E.output (nextEvenClusterOrdinal i hi)).paths.sourceSet)
  /-- Every between-cluster stitching linkage has the intended cardinality. -/
  between_card :
    ∀ (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)),
      (between i hi).card = q
  /-- Between-cluster stitching avoids the source even cluster internally. -/
  between_internallyDisjoint_left :
    ∀ (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)),
      (between i hi).toPathPacking.InternallyDisjointFromSet
        (P.cluster (evenClusterIndex g i))
  /-- Between-cluster stitching avoids the target even cluster internally. -/
  between_internallyDisjoint_right :
    ∀ (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)),
      (between i hi).toPathPacking.InternallyDisjointFromSet
        (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi)))
  /-- The last local output, viewed as ending in the last right nail set. -/
  last :
    PathPacking G
      (P.left (evenClusterIndex g (lastEvenClusterOrdinal hN)))
      (P.right P.lastIndex)
  /-- The last local output has the intended cardinality. -/
  last_card : last.card = q

namespace StitchingPieces

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {g w q : ℕ}

/-- Construct the canonical stitching pieces from a strong path-of-sets system
and local outputs, assuming the even-cluster ordinal set is nonempty. -/
noncomputable def canonical
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (hN : 0 < g * (g - 1)) :
    StitchingPieces P E where
  hN := hN
  start := Classical.choose (E.exists_startPacking_to_first P hN)
  start_card := (Classical.choose_spec
    (E.exists_startPacking_to_first P hN))
  between := fun i hi =>
    Classical.choose (E.exists_stitchingPacking_to_next P hi)
  between_card := by
    intro i hi
    exact (Classical.choose_spec
      (E.exists_stitchingPacking_to_next P hi)).1
  between_internallyDisjoint_left := by
    intro i hi
    exact (Classical.choose_spec
      (E.exists_stitchingPacking_to_next P hi)).2.1
  between_internallyDisjoint_right := by
    intro i hi
    exact (Classical.choose_spec
      (E.exists_stitchingPacking_to_next P hi)).2.2
  last := E.toLastRight P.toPathOfSetsSystem hN
  last_card := by
    simp

/-- For `g ≥ 2`, the canonical stitching pieces exist. -/
noncomputable def canonicalOfTwoLe
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (hg : 2 ≤ g) :
    StitchingPieces P E :=
  canonical P E (evenClusterOrdinal_count_pos_of_two_le hg)

end StitchingPieces

/-- Formal local input corresponding to Chekuri--Chuzhoy Theorem 3.1.

For linked equal-size terminal sets `A` and `B` inside a connected cluster `C`,
the theorem either produces an `h x h` grid minor in the ambient graph or
returns `q` disjoint `A`-to-`B` paths inside `C` with pairwise bridges inside
`C`. -/
def LocalRoutingInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {C A B : Finset V} {h q w : ℕ},
      1 < h →
        1 < q →
          NodeLinkedIn G C A B →
            A.card = w →
              B.card = w →
                (16 * h + 10) * q ≤ w →
                  ContainsGridMinor G h ∨
                    ∃ P : PathPacking G A B,
                      P.card = q ∧ P.StaysIn C ∧ P.HasPairwiseBridgesIn C

/-- Applying the local Chekuri--Chuzhoy routing theorem in each even
one-based cluster either already gives a grid minor, or gives local outputs for
all even one-based clusters.

This is the first proved part of Corollary 3.2: the remaining work is to
concatenate these local outputs through the intervening odd clusters and prove
the trace/order fields of `StitchedRows`. -/
theorem gridMinor_or_evenClusterOutputs_of_localRoutingInput
    (hlocal : LocalRoutingInput.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {g w : ℕ}
    (hg : 2 ≤ g)
    (hw : (16 * g + 10) * g ≤ w)
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w) :
    ContainsGridMinor G g ∨
      Nonempty (EvenClusterOutputs P.toPathOfSetsSystem g) := by
  classical
  by_cases hgrid : ContainsGridMinor G g
  · exact Or.inl hgrid
  · refine Or.inr ⟨{ output := ?_ }⟩
    intro i
    let e := evenClusterIndex g i
    have hgt : 1 < g := lt_of_lt_of_le (by decide : 1 < 2) hg
    have hleft : (P.left e).card = w := P.left_card e
    have hright : (P.right e).card = w := P.right_card e
    have hpaths_exists :
        ∃ Q : PathPacking G (P.left e) (P.right e),
          Q.card = g ∧ Q.StaysIn (P.cluster e) ∧
            Q.HasPairwiseBridgesIn (P.cluster e) := by
      rcases hlocal G hgt hgt (P.left_right_nodeLinked e)
          hleft hright hw with hgrid' | hpaths
      · exact False.elim (hgrid hgrid')
      · exact hpaths
    let Q : PathPacking G (P.left e) (P.right e) :=
      Classical.choose hpaths_exists
    have hQspec :
        Q.card = g ∧ Q.StaysIn (P.cluster e) ∧
          Q.HasPairwiseBridgesIn (P.cluster e) :=
      Classical.choose_spec hpaths_exists
    exact {
      paths := Q
      paths_card := hQspec.1
      paths_staysIn := by simpa [e] using hQspec.2.1
      pairwise_bridges := by simpa [e] using hQspec.2.2
    }

/-- Specialization of `gridMinor_or_evenClusterOutputs_of_localRoutingInput`
to the width used in Chekuri--Chuzhoy Corollary 3.3. -/
theorem gridMinor_or_evenClusterOutputs_of_localRoutingInput_corollary33Width
    (hlocal : LocalRoutingInput.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {g : ℕ}
    (hg : 2 ≤ g)
    (P : StrongPathOfSetsSystem G
      (2 * g * (g - 1)) (16 * g ^ 2 + 10 * g)) :
    ContainsGridMinor G g ∨
      Nonempty (EvenClusterOutputs P.toPathOfSetsSystem g) := by
  refine gridMinor_or_evenClusterOutputs_of_localRoutingInput hlocal G hg ?_ P
  have hwidth : (16 * g + 10) * g = 16 * g ^ 2 + 10 * g := by
    ring
  exact le_of_eq hwidth

/-- The stitched rows returned by Chekuri--Chuzhoy Corollary 3.2, specialized
to the parameters used in Corollary 3.3.

The row packing connects the first left nail set to the last right nail set.
For each even one-based cluster, every pair of distinct row paths has a bridge
inside that cluster, internally disjoint from all rows.  The later Appendix C.1
assembly turns this data into a path-valued sparse-grid branch certificate. -/
structure StitchedRows {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (g w : ℕ)
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w) where
  /-- The row paths. -/
  rows : PathPacking G (P.left P.firstIndex) (P.right P.lastIndex)
  /-- The number of row paths. -/
  rows_card : rows.card = g
  /-- Each row meets each cluster in a path-shaped trace. -/
  row_trace_cluster :
    ∀ (a : rows.Index) (i : Fin (2 * g * (g - 1))),
      (rows.path a).TraceOn (P.cluster i)
  /-- The cluster traces occur along each row in the cluster order. -/
  row_clusters_ordered :
    ∀ (a : rows.Index) ⦃i j : Fin (2 * g * (g - 1))⦄,
      i.1 < j.1 →
        ∀ ⦃u v : V⦄,
          u ∈ (rows.path a).vertexSet → u ∈ P.cluster i →
            v ∈ (rows.path a).vertexSet → v ∈ P.cluster j →
              (rows.path a).Before u v
  /-- Each even one-based cluster supplies all pairwise row bridges. -/
  bridge_in_even_cluster :
    ∀ i : Fin (g * (g - 1)),
      rows.HasPairwiseBridgesIn (P.cluster (evenClusterIndex g i))

/-- The remaining stitching input after the local Chekuri--Chuzhoy routing
theorem has been applied in every even one-based cluster.

It says that compatible local outputs can be concatenated through the
intervening odd clusters into the global stitched rows of Corollary 3.2.  The
canonical `StitchingPieces` argument supplies the start and between-cluster
linkages; this input is only responsible for the remaining global
concatenation, trace, and order proof. -/
def StitchingInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {g : ℕ},
      2 ≤ g →
        (P : StrongPathOfSetsSystem G
          (2 * g * (g - 1)) (16 * g ^ 2 + 10 * g)) →
          (E : EvenClusterOutputs P.toPathOfSetsSystem g) →
            StitchingPieces P E →
            Nonempty
              (StitchedRows G g (16 * g ^ 2 + 10 * g)
                P.toPathOfSetsSystem)

end ChekuriChuzhoy
end SimpleGraph
end TwinWidth
