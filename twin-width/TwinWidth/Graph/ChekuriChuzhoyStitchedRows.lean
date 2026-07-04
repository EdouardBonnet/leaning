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

/-- The gap from an even one-based cluster to the following odd one-based
cluster exists whenever the next even one-based cluster exists. -/
theorem evenClusterIndex_succ_lt_length {g : ℕ}
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (evenClusterIndex g i).1 + 1 < 2 * g * (g - 1) := by
  dsimp [evenClusterIndex]
  calc
    2 * i.1 + 1 + 1 = 2 * (i.1 + 1) := by omega
    _ < 2 * (g * (g - 1)) :=
      Nat.mul_lt_mul_of_pos_left hi (by decide : 0 < 2)
    _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]

/-- The gap from the odd one-based cluster after an even one to the next even
one-based cluster exists whenever the next even ordinal exists. -/
theorem oddClusterAfterEvenIndex_succ_lt_length {g : ℕ}
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (oddClusterAfterEvenIndex g i hi).1 + 1 < 2 * g * (g - 1) := by
  have hsucc : i.1 + 2 ≤ g * (g - 1) := Nat.succ_le_of_lt hi
  calc
    (oddClusterAfterEvenIndex g i hi).1 + 1 = 2 * i.1 + 3 := by
      simp [oddClusterAfterEvenIndex]
    _ < 2 * (i.1 + 2) := by omega
    _ ≤ 2 * (g * (g - 1)) := Nat.mul_le_mul_left 2 hsucc
    _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]

/-- The first connector gap exists when there is at least one even one-based
cluster. -/
theorem firstIndex_succ_lt_length_of_evenClusterOrdinal_pos
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (_hN : 0 < g * (g - 1)) :
    P.firstIndex.1 + 1 < 2 * g * (g - 1) := by
  calc
    P.firstIndex.1 + 1 = 1 := by simp [PathOfSetsSystem.firstIndex]
    _ < 2 * (g * (g - 1)) := by omega
    _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]

/-- The vertex region used by the initial stitching paths. -/
noncomputable def firstStitchingRegion {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1)) : Finset V :=
  P.cluster P.firstIndex ∪
    (P.connector P.firstIndex
      (firstIndex_succ_lt_length_of_evenClusterOrdinal_pos
        P.toPathOfSetsSystem hN)).toPathPacking.vertexSet

/-- The vertex region used to stitch between two consecutive even one-based
clusters. -/
noncomputable def betweenStitchingRegion {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    Finset V :=
  (P.connector (evenClusterIndex g i)
      (evenClusterIndex_succ_lt_length i hi)).toPathPacking.vertexSet ∪
    (P.cluster (oddClusterAfterEvenIndex g i hi) ∪
      (P.connector (oddClusterAfterEvenIndex g i hi)
        (oddClusterAfterEvenIndex_succ_lt_length i hi)).toPathPacking.vertexSet)

/-- The first stitching region is disjoint from the region used to stitch from
the first even one-based cluster to the second. -/
theorem betweenStitchingRegion_first_disjoint_firstStitchingRegion
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V} {g w : ℕ}
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1)) (hi : 0 + 1 < g * (g - 1)) :
    Disjoint (betweenStitchingRegion P ⟨0, hN⟩ hi)
      (firstStitchingRegion P hN) := by
  classical
  let first : Fin (g * (g - 1)) := ⟨0, hN⟩
  let e0 : Fin (2 * g * (g - 1)) := evenClusterIndex g first
  let odd : Fin (2 * g * (g - 1)) := oddClusterAfterEvenIndex g first hi
  let hgap0 := firstIndex_succ_lt_length_of_evenClusterOrdinal_pos
    P.toPathOfSetsSystem hN
  let hgap1 := evenClusterIndex_succ_lt_length first hi
  let hgap2 := oddClusterAfterEvenIndex_succ_lt_length first hi
  have hfirst_ne_e0 : P.firstIndex ≠ e0 := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, e0, first, evenClusterIndex] at hval
  have he0_ne_first : e0 ≠ P.firstIndex := fun h => hfirst_ne_e0 h.symm
  have hfirst_ne_odd : P.firstIndex ≠ odd := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, odd, first, oddClusterAfterEvenIndex] at hval
  have hodd_ne_first : odd ≠ P.firstIndex := fun h => hfirst_ne_odd h.symm
  have hfirst_ne_after_e0 : P.firstIndex ≠ ⟨e0.1 + 1, hgap1⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, e0, first, evenClusterIndex] at hval
  have hodd_ne_e0 : odd ≠ e0 := by
    intro h
    have hval := congrArg Fin.val h
    simp [odd, e0, first, oddClusterAfterEvenIndex, evenClusterIndex] at hval
  have hodd_ne_after_first : odd ≠ ⟨P.firstIndex.1 + 1, hgap0⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, odd, first, oddClusterAfterEvenIndex] at hval
  have hfirst_ne_after_odd : P.firstIndex ≠ ⟨odd.1 + 1, hgap2⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, odd, first, oddClusterAfterEvenIndex] at hval
  rw [Finset.disjoint_left]
  intro v hvBetween hvFirst
  simp [betweenStitchingRegion, firstStitchingRegion] at hvBetween hvFirst
  rcases hvBetween with hvConnEven | hvOdd | hvConnOdd
  · rcases hvFirst with hvFirstCluster | hvFirstConn
    · exact Finset.disjoint_left.mp
        (P.connector_vertexSet_disjoint_cluster_of_ne e0 hgap1 P.firstIndex
          hfirst_ne_e0 hfirst_ne_after_e0)
        hvConnEven hvFirstCluster
    · exact Finset.disjoint_left.mp
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (P.connector_mutually_nodeDisjoint hgap1 hgap0 he0_ne_first))
        hvConnEven hvFirstConn
  · rcases hvFirst with hvFirstCluster | hvFirstConn
    · exact Finset.disjoint_left.mp (P.cluster_disjoint hodd_ne_first)
        hvOdd hvFirstCluster
    · exact Finset.disjoint_left.mp
        ((P.connector_vertexSet_disjoint_cluster_of_ne P.firstIndex hgap0 odd
          hodd_ne_first hodd_ne_after_first).symm)
        hvOdd hvFirstConn
  · rcases hvFirst with hvFirstCluster | hvFirstConn
    · exact Finset.disjoint_left.mp
        (P.connector_vertexSet_disjoint_cluster_of_ne odd hgap2 P.firstIndex
          hfirst_ne_odd hfirst_ne_after_odd)
        hvConnOdd hvFirstCluster
    · exact Finset.disjoint_left.mp
        (PathPacking.vertexSet_disjoint_of_mutuallyNodeDisjoint
          (P.connector_mutually_nodeDisjoint hgap2 hgap0 hodd_ne_first))
        hvConnOdd hvFirstConn

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

/-- Consecutive local even-cluster outputs can be stitched through the
intervening odd cluster, with the full region and endpoint-cluster separation
certificates retained.

The earlier `exists_stitchingPacking_to_next` theorem exposes only the
separation from the two even clusters.  The global row concatenation also needs
to know where the stitching paths live, so this strengthened version keeps the
two-gap region returned by the strong path-of-sets API. -/
theorem exists_stitchingPacking_to_next_with_invariants
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    {i : Fin (g * (g - 1))} (hi : i.1 + 1 < g * (g - 1))
    (E : EvenClusterOutput P.toPathOfSetsSystem i q)
    (E_next :
      EvenClusterOutput P.toPathOfSetsSystem (nextEvenClusterOrdinal i hi) q) :
    ∃ S : PerfectPathPacking G E.paths.targetSet E_next.paths.sourceSet,
      S.card = q ∧
        S.toPathPacking.StaysIn (betweenStitchingRegion P i hi) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g i)) ∧
            S.toPathPacking.InternallyDisjointFromSet
              (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) := by
  classical
  let e := evenClusterIndex g i
  let eOdd := oddClusterAfterEvenIndex g i hi
  have heOdd :
      e.1 + 1 < 2 * g * (g - 1) := by
    dsimp [e, evenClusterIndex]
    calc
      2 * i.1 + 1 + 1 = 2 * (i.1 + 1) := by omega
      _ < 2 * (g * (g - 1)) :=
        Nat.mul_lt_mul_of_pos_left hi (by decide : 0 < 2)
      _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]
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
  have heOdd_eq :
      (⟨e.1 + 1, heOdd⟩ : Fin (2 * g * (g - 1))) = eOdd := by
    apply Fin.ext
    simp [e, eOdd, evenClusterIndex, oddClusterAfterEvenIndex]
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
  rcases P.exists_twoGap_concatPacking_between_subsets e heOdd hOddSucc
      hR hL hcard with
    ⟨S, hS_card, hS_stays, hS_first, hS_last⟩
  refine ⟨S, ?_, ?_, by simpa [e] using hS_first, ?_⟩
  · exact hS_card.trans (by rw [PathPacking.targetSet_card, E.paths_card])
  · simpa [betweenStitchingRegion, e, eOdd, heOdd_eq, hnext] using hS_stays
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

/-- The first local even-cluster output can be connected back to the first
left nail set, retaining the region and first-even-cluster separation
certificates needed by the global concatenation.

The packing is still exposed as a `PathPacking` with the full first left nail
set as its left terminal set, matching the eventual row terminal interface. -/
theorem exists_startPacking_to_first_with_invariants
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P.toPathOfSetsSystem ⟨0, hN⟩ q) :
    ∃ S : PathPacking G (P.left P.firstIndex) E.paths.sourceSet,
      S.card = q ∧
        S.StaysIn (firstStitchingRegion P hN) ∧
          S.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g ⟨0, hN⟩)) := by
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
  let S : PathPacking G (P.left P.firstIndex) E.paths.sourceSet :=
    R.toPathPacking.widenTerminals hRsource (by intro v hv; exact hv)
  have hRstay :
      R.toPathPacking.StaysIn
        (P.cluster P.firstIndex ∪
          (P.connector P.firstIndex hgap).toPathPacking.vertexSet) := by
    intro a v hv
    have hvL : v ∈ (L.path a.1).vertexSet := by
      simpa [R, L, PerfectPathPacking.restrictTargetSet,
        PerfectPathPacking.copyTerminals, PerfectPathPacking.restrictIndexSet] using hv
    exact P.leftNextPacking_staysIn P.firstIndex hgap a.1 hvL
  have hRinternal :
      R.toPathPacking.InternallyDisjointFromSet
        (P.cluster (evenClusterIndex g firstEven)) := by
    intro a v hv hvC
    have hvL : v ∈ (L.path a.1).vertexSet := by
      simpa [R, L, PerfectPathPacking.restrictTargetSet,
        PerfectPathPacking.copyTerminals, PerfectPathPacking.restrictIndexSet] using hv
    have hendpoint :=
      P.leftNextPacking_internallyDisjoint_nextCluster P.firstIndex hgap a.1
        hvL (by simpa [hfirstEven] using hvC)
    simpa [L, GraphPath.IsEndpoint] using hendpoint
  refine ⟨S, ?_, ?_, ?_⟩
  · calc
      S.card = R.card := rfl
      _ = E.paths.sourceSet.card := by simp [R, L]
      _ = E.paths.card := by rw [PathPacking.sourceSet_card]
      _ = q := E.paths_card
  · intro a v hv
    have hvR : v ∈ (R.path a).vertexSet := by simpa [S] using hv
    simpa [firstStitchingRegion, hgap] using hRstay a hvR
  · intro a v hv hvC
    have hvR : v ∈ (R.path a).vertexSet := by simpa [S] using hv
    exact hRinternal a hvR (by simpa [firstEven] using hvC)

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

theorem toLastRight_staysIn
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P (lastEvenClusterOrdinal hN) q) :
    (E.toLastRight P hN).StaysIn (P.cluster P.lastIndex) := by
  intro i v hv
  have hvE : v ∈ (E.paths.path i).vertexSet := by
    simpa [toLastRight, PathPacking.widenTerminals] using hv
  have hstay := E.paths_staysIn i hvE
  simpa [evenClusterIndex_lastEven_eq_lastIndex P hN] using hstay

theorem toLastRight_hasPairwiseBridgesIn
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (hN : 0 < g * (g - 1))
    (E : EvenClusterOutput P (lastEvenClusterOrdinal hN) q) :
    (E.toLastRight P hN).HasPairwiseBridgesIn (P.cluster P.lastIndex) := by
  simpa [toLastRight, evenClusterIndex_lastEven_eq_lastIndex P hN] using
    E.paths.widenTerminals_hasPairwiseBridgesIn
      (by intro v hv; exact hv)
      (by
        intro v hv
        rw [← evenClusterIndex_lastEven_eq_lastIndex P hN]
        exact hv)
      E.pairwise_bridges

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

/-- Consecutive entries in a family of local even-cluster outputs can be
stitched through the intervening odd cluster, retaining the full two-gap region
and separation certificates. -/
theorem exists_stitchingPacking_to_next_with_invariants
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    {i : Fin (g * (g - 1))} (hi : i.1 + 1 < g * (g - 1)) :
    ∃ S : PerfectPathPacking G (E.output i).paths.targetSet
        ((E.output (nextEvenClusterOrdinal i hi)).paths.sourceSet),
      S.card = q ∧
        S.toPathPacking.StaysIn (betweenStitchingRegion P i hi) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g i)) ∧
          S.toPathPacking.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) :=
  (E.output i).exists_stitchingPacking_to_next_with_invariants P hi
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

/-- The first local output in a family can be connected back to the first left
nail set of the whole path-of-sets system, retaining region and separation
certificates. -/
theorem exists_startPacking_to_first_with_invariants
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (hN : 0 < g * (g - 1)) :
    ∃ S : PathPacking G (P.left P.firstIndex)
        ((E.output ⟨0, hN⟩).paths.sourceSet),
      S.card = q ∧
        S.StaysIn (firstStitchingRegion P hN) ∧
          S.InternallyDisjointFromSet
            (P.cluster (evenClusterIndex g ⟨0, hN⟩)) :=
  (E.output ⟨0, hN⟩).exists_startPacking_to_first_with_invariants P hN

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

theorem toLastRight_staysIn
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P q)
    (hN : 0 < g * (g - 1)) :
    (E.toLastRight P hN).StaysIn (P.cluster P.lastIndex) :=
  (E.output (lastEvenClusterOrdinal hN)).toLastRight_staysIn P hN

theorem toLastRight_hasPairwiseBridgesIn
    (P : PathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P q)
    (hN : 0 < g * (g - 1)) :
    (E.toLastRight P hN).HasPairwiseBridgesIn (P.cluster P.lastIndex) :=
  (E.output (lastEvenClusterOrdinal hN)).toLastRight_hasPairwiseBridgesIn P hN

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
  /-- The initial linkage is routed through the first cluster and first
  connector. -/
  start_staysIn : start.StaysIn (firstStitchingRegion P hN)
  /-- The initial linkage avoids the first even one-based cluster internally. -/
  start_internallyDisjoint_firstEven :
    start.InternallyDisjointFromSet (P.cluster (evenClusterIndex g ⟨0, hN⟩))
  /-- Stitching linkages between consecutive local even-cluster outputs. -/
  between :
    (i : Fin (g * (g - 1))) → (hi : i.1 + 1 < g * (g - 1)) →
      PerfectPathPacking G (E.output i).paths.targetSet
        ((E.output (nextEvenClusterOrdinal i hi)).paths.sourceSet)
  /-- Every between-cluster stitching linkage has the intended cardinality. -/
  between_card :
    ∀ (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)),
      (between i hi).card = q
  /-- Every between-cluster stitching linkage is routed through the two
  connectors and the intervening odd one-based cluster. -/
  between_staysIn :
    ∀ (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)),
      (between i hi).toPathPacking.StaysIn (betweenStitchingRegion P i hi)
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
  /-- The last local output stays inside the last cluster. -/
  last_output_staysIn : last.StaysIn (P.cluster P.lastIndex)
  /-- The last local output retains the pairwise bridges from the last even
  one-based cluster. -/
  last_output_pairwise_bridges :
    last.HasPairwiseBridgesIn (P.cluster P.lastIndex)

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
  start := Classical.choose
    (E.exists_startPacking_to_first_with_invariants P hN)
  start_card := (Classical.choose_spec
    (E.exists_startPacking_to_first_with_invariants P hN)).1
  start_staysIn := (Classical.choose_spec
    (E.exists_startPacking_to_first_with_invariants P hN)).2.1
  start_internallyDisjoint_firstEven := (Classical.choose_spec
    (E.exists_startPacking_to_first_with_invariants P hN)).2.2
  between := fun i hi =>
    Classical.choose (E.exists_stitchingPacking_to_next_with_invariants P hi)
  between_card := by
    intro i hi
    exact (Classical.choose_spec
      (E.exists_stitchingPacking_to_next_with_invariants P hi)).1
  between_staysIn := by
    intro i hi
    exact (Classical.choose_spec
      (E.exists_stitchingPacking_to_next_with_invariants P hi)).2.1
  between_internallyDisjoint_left := by
    intro i hi
    exact (Classical.choose_spec
      (E.exists_stitchingPacking_to_next_with_invariants P hi)).2.2.1
  between_internallyDisjoint_right := by
    intro i hi
    exact (Classical.choose_spec
      (E.exists_stitchingPacking_to_next_with_invariants P hi)).2.2.2
  last := E.toLastRight P.toPathOfSetsSystem hN
  last_card := by
    simp
  last_output_staysIn :=
    E.toLastRight_staysIn P.toPathOfSetsSystem hN
  last_output_pairwise_bridges :=
    E.toLastRight_hasPairwiseBridgesIn P.toPathOfSetsSystem hN

/-- For `g ≥ 2`, the canonical stitching pieces exist. -/
noncomputable def canonicalOfTwoLe
    (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w)
    (E : EvenClusterOutputs P.toPathOfSetsSystem q)
    (hg : 2 ≤ g) :
    StitchingPieces P E :=
  canonical P E (evenClusterOrdinal_count_pos_of_two_le hg)

/-- The initial stitching piece, promoted to a perfect packing on the source
terminals it actually uses and the full local source set of the first even
one-based cluster. -/
noncomputable def startPerfect
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    PerfectPathPacking G K.start.sourceSet ((E.output ⟨0, K.hN⟩).paths.sourceSet) :=
  K.start.toPerfectUsedTerminals.copyTerminals rfl
    (K.start.targetSet_eq_right_of_card_eq (by
      rw [K.start_card, PathPacking.sourceSet_card,
        (E.output ⟨0, K.hN⟩).paths_card]))

@[simp] theorem startPerfect_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.startPerfect.card = q := by
  simp [startPerfect, K.start_card]

theorem startPerfect_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.startPerfect.toPathPacking.StaysIn (firstStitchingRegion P K.hN) := by
  simpa [startPerfect] using
    K.start.toPerfectUsedTerminals_staysIn K.start_staysIn

theorem startPerfect_internallyDisjoint_firstEven
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.startPerfect.toPathPacking.InternallyDisjointFromSet
      (P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) := by
  simpa [startPerfect] using
    K.start.toPerfectUsedTerminals_internallyDisjointFromSet
      K.start_internallyDisjoint_firstEven

/-- A local even-cluster row output, promoted to a perfect packing on the
terminal sets it actually uses. -/
noncomputable def localPerfect
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (_K : StitchingPieces P E) (i : Fin (g * (g - 1))) :
    PerfectPathPacking G (E.output i).paths.sourceSet (E.output i).paths.targetSet :=
  (E.output i).paths.toPerfectUsedTerminals

@[simp] theorem localPerfect_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (i : Fin (g * (g - 1))) :
    (K.localPerfect i).card = q := by
  simp [localPerfect, (E.output i).paths_card]

theorem localPerfect_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (i : Fin (g * (g - 1))) :
    (K.localPerfect i).toPathPacking.StaysIn
      (P.cluster (evenClusterIndex g i)) := by
  simpa [localPerfect] using
    (E.output i).paths.toPerfectUsedTerminals_staysIn
      (E.output i).paths_staysIn

theorem localPerfect_hasPairwiseBridgesIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) (i : Fin (g * (g - 1))) :
    (K.localPerfect i).toPathPacking.HasPairwiseBridgesIn
      (P.cluster (evenClusterIndex g i)) := by
  simpa [localPerfect] using
    (E.output i).paths.toPerfectUsedTerminals_hasPairwiseBridgesIn
      (E.output i).pairwise_bridges

@[simp] theorem betweenPerfect_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (K.between i hi).card = q :=
  K.between_card i hi

theorem betweenPerfect_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (K.between i hi).toPathPacking.StaysIn (betweenStitchingRegion P i hi) :=
  K.between_staysIn i hi

theorem betweenPerfect_internallyDisjoint_left
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (K.between i hi).toPathPacking.InternallyDisjointFromSet
      (P.cluster (evenClusterIndex g i)) :=
  K.between_internallyDisjoint_left i hi

theorem betweenPerfect_internallyDisjoint_right
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (i : Fin (g * (g - 1))) (hi : i.1 + 1 < g * (g - 1)) :
    (K.between i hi).toPathPacking.InternallyDisjointFromSet
      (P.cluster (evenClusterIndex g (nextEvenClusterOrdinal i hi))) :=
  K.between_internallyDisjoint_right i hi

theorem last_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.last.StaysIn (P.cluster P.lastIndex) :=
  K.last_output_staysIn

theorem last_hasPairwiseBridgesIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.last.HasPairwiseBridgesIn (P.cluster P.lastIndex) :=
  K.last_output_pairwise_bridges

/-- The source terminals used by the initial perfect stitching piece are
disjoint from the first even one-based cluster. -/
theorem startPerfect_source_disjoint_firstEven
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    Disjoint K.start.sourceSet
      (P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvSource hvCluster
  have hvLeft : v ∈ P.left P.firstIndex :=
    K.start.sourceSet_subset_left hvSource
  have hvFirstCluster : v ∈ P.cluster P.firstIndex :=
    P.left_subset_cluster P.firstIndex hvLeft
  have hne : P.firstIndex ≠ evenClusterIndex g ⟨0, K.hN⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, evenClusterIndex] at hval
  exact Finset.disjoint_left.mp (P.cluster_disjoint hne)
    hvFirstCluster hvCluster

/-- The first stitched prefix: the initial linkage followed by the local row
pieces in the first even one-based cluster. -/
noncomputable def firstPrefix
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    PerfectPathPacking G K.start.sourceSet
      ((E.output ⟨0, K.hN⟩).paths.targetSet) :=
  K.startPerfect.concatOfFirstInternallyDisjointSecondStaysIn
    (K.localPerfect ⟨0, K.hN⟩)
    K.startPerfect_internallyDisjoint_firstEven
    (K.localPerfect_staysIn ⟨0, K.hN⟩)
    K.startPerfect_source_disjoint_firstEven

@[simp] theorem firstPrefix_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.firstPrefix.card = q := by
  simp [firstPrefix]

theorem firstPrefix_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E) :
    K.firstPrefix.toPathPacking.StaysIn
      (firstStitchingRegion P K.hN ∪
        P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) := by
  simpa [firstPrefix] using
    K.startPerfect.concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
      (K.localPerfect ⟨0, K.hN⟩)
      K.startPerfect_internallyDisjoint_firstEven
      (K.localPerfect_staysIn ⟨0, K.hN⟩)
      K.startPerfect_source_disjoint_firstEven
      K.startPerfect_staysIn

/-- The first between-cluster stitching packing is disjoint from the initial
stitching region. -/
theorem betweenPerfect_vertexSet_disjoint_firstStitchingRegion_first
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    Disjoint (K.between ⟨0, K.hN⟩ hi).toPathPacking.vertexSet
      (firstStitchingRegion P K.hN) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvBetween hvFirst
  have hvRegion :
      v ∈ betweenStitchingRegion P ⟨0, K.hN⟩ hi :=
    PathPacking.vertexSet_subset_of_staysIn
      (K.betweenPerfect_staysIn ⟨0, K.hN⟩ hi) hvBetween
  exact Finset.disjoint_left.mp
    (betweenStitchingRegion_first_disjoint_firstStitchingRegion P K.hN hi)
    hvRegion hvFirst

/-- The first between-cluster stitching packing is internally disjoint from
the full region already used by the first prefix. -/
theorem betweenPerfect_internallyDisjoint_firstPrefixRegion_first
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    (K.between ⟨0, K.hN⟩ hi).toPathPacking.InternallyDisjointFromSet
      (firstStitchingRegion P K.hN ∪
        P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) := by
  have h :=
    PathPacking.internallyDisjointFromSet_union_of_disjoint_vertexSet
      (K.between ⟨0, K.hN⟩ hi).toPathPacking
      (K.betweenPerfect_internallyDisjoint_left ⟨0, K.hN⟩ hi)
      (K.betweenPerfect_vertexSet_disjoint_firstStitchingRegion_first hi)
  simpa [Finset.union_comm] using h

/-- The source terminals of the next even-cluster local output are disjoint
from the first-prefix region. -/
theorem nextEvenSource_disjoint_firstPrefixRegion
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    Disjoint
      ((E.output (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi)).paths.sourceSet)
      (firstStitchingRegion P K.hN ∪
        P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) := by
  classical
  let first : Fin (g * (g - 1)) := ⟨0, K.hN⟩
  let next : Fin (g * (g - 1)) := nextEvenClusterOrdinal first hi
  let e0 : Fin (2 * g * (g - 1)) := evenClusterIndex g first
  let e1 : Fin (2 * g * (g - 1)) := evenClusterIndex g next
  let hgap0 := firstIndex_succ_lt_length_of_evenClusterOrdinal_pos
    P.toPathOfSetsSystem K.hN
  have he1_ne_firstIndex : e1 ≠ P.firstIndex := by
    intro h
    have hval := congrArg Fin.val h
    simp [e1, next, first, nextEvenClusterOrdinal, evenClusterIndex,
      PathOfSetsSystem.firstIndex] at hval
  have he1_ne_e0 : e1 ≠ e0 := by
    intro h
    have hval := congrArg Fin.val h
    simp [e1, e0, next, first, nextEvenClusterOrdinal, evenClusterIndex] at hval
  have he1_ne_after_first : e1 ≠ ⟨P.firstIndex.1 + 1, hgap0⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp [e1, next, first, nextEvenClusterOrdinal, evenClusterIndex,
      PathOfSetsSystem.firstIndex] at hval
  rw [Finset.disjoint_left]
  intro v hvSource hvRegion
  have hvE1 : v ∈ P.cluster e1 :=
    P.left_subset_cluster e1
      ((E.output next).paths.sourceSet_subset_left (by simpa [next, e1] using hvSource))
  rcases Finset.mem_union.mp hvRegion with hvFirstRegion | hvE0
  · rcases Finset.mem_union.mp (by simpa [firstStitchingRegion, hgap0] using hvFirstRegion)
        with hvFirstCluster | hvFirstConnector
    · exact Finset.disjoint_left.mp (P.cluster_disjoint he1_ne_firstIndex)
        hvE1 hvFirstCluster
    · exact Finset.disjoint_left.mp
        ((P.connector_vertexSet_disjoint_cluster_of_ne P.firstIndex hgap0 e1
          he1_ne_firstIndex he1_ne_after_first).symm)
        hvE1 hvFirstConnector
  · exact Finset.disjoint_left.mp (P.cluster_disjoint he1_ne_e0)
      hvE1 (by simpa [e0] using hvE0)

/-- The second stitched prefix: the first prefix followed by the stitching
packing from the first even one-based cluster to the next even one. -/
noncomputable def secondPrefix
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    PerfectPathPacking G K.start.sourceSet
      ((E.output (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi)).paths.sourceSet) :=
  K.firstPrefix.concatOfFirstStaysInSecondInternallyDisjoint
    (K.between ⟨0, K.hN⟩ hi)
    K.firstPrefix_staysIn
    (K.betweenPerfect_internallyDisjoint_firstPrefixRegion_first hi)
    (K.nextEvenSource_disjoint_firstPrefixRegion hi)

@[simp] theorem secondPrefix_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    (K.secondPrefix hi).card = q := by
  simp [secondPrefix]

theorem secondPrefix_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    (K.secondPrefix hi).toPathPacking.StaysIn
      ((firstStitchingRegion P K.hN ∪
          P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) ∪
        betweenStitchingRegion P ⟨0, K.hN⟩ hi) := by
  simpa [secondPrefix] using
    K.firstPrefix.concatOfFirstStaysInSecondInternallyDisjoint_staysIn_union
      (K.between ⟨0, K.hN⟩ hi)
      K.firstPrefix_staysIn
      (K.betweenPerfect_internallyDisjoint_firstPrefixRegion_first hi)
      (K.nextEvenSource_disjoint_firstPrefixRegion hi)
      (K.betweenPerfect_staysIn ⟨0, K.hN⟩ hi)

/-- The second even one-based cluster is disjoint from the full first-prefix
region. -/
theorem nextEvenCluster_disjoint_firstPrefixRegion
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    Disjoint
      (P.cluster (evenClusterIndex g
        (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi)))
      (firstStitchingRegion P K.hN ∪
        P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) := by
  classical
  let first : Fin (g * (g - 1)) := ⟨0, K.hN⟩
  let next : Fin (g * (g - 1)) := nextEvenClusterOrdinal first hi
  let e0 : Fin (2 * g * (g - 1)) := evenClusterIndex g first
  let e1 : Fin (2 * g * (g - 1)) := evenClusterIndex g next
  let hgap0 := firstIndex_succ_lt_length_of_evenClusterOrdinal_pos
    P.toPathOfSetsSystem K.hN
  have he1_ne_firstIndex : e1 ≠ P.firstIndex := by
    intro h
    have hval := congrArg Fin.val h
    simp [e1, next, first, nextEvenClusterOrdinal, evenClusterIndex,
      PathOfSetsSystem.firstIndex] at hval
  have he1_ne_e0 : e1 ≠ e0 := by
    intro h
    have hval := congrArg Fin.val h
    simp [e1, e0, next, first, nextEvenClusterOrdinal, evenClusterIndex] at hval
  have he1_ne_after_first : e1 ≠ ⟨P.firstIndex.1 + 1, hgap0⟩ := by
    intro h
    have hval := congrArg Fin.val h
    simp [e1, next, first, nextEvenClusterOrdinal, evenClusterIndex,
      PathOfSetsSystem.firstIndex] at hval
  rw [Finset.disjoint_left]
  intro v hvE1 hvRegion
  rcases Finset.mem_union.mp hvRegion with hvFirstRegion | hvE0
  · rcases Finset.mem_union.mp
        (by simpa [firstStitchingRegion, hgap0] using hvFirstRegion)
        with hvFirstCluster | hvFirstConnector
    · exact Finset.disjoint_left.mp
        (P.cluster_disjoint he1_ne_firstIndex) hvE1 hvFirstCluster
    · exact Finset.disjoint_left.mp
        ((P.connector_vertexSet_disjoint_cluster_of_ne P.firstIndex hgap0 e1
          he1_ne_firstIndex he1_ne_after_first).symm)
        hvE1 hvFirstConnector
  · exact Finset.disjoint_left.mp (P.cluster_disjoint he1_ne_e0)
      hvE1 (by simpa [e0] using hvE0)

/-- The first stitched prefix uses no vertex in the second even one-based
cluster. -/
theorem firstPrefix_vertexSet_disjoint_nextEvenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    Disjoint K.firstPrefix.toPathPacking.vertexSet
      (P.cluster (evenClusterIndex g
        (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvPrefix hvCluster
  have hvRegion :
      v ∈ firstStitchingRegion P K.hN ∪
        P.cluster (evenClusterIndex g ⟨0, K.hN⟩) :=
    PathPacking.vertexSet_subset_of_staysIn K.firstPrefix_staysIn hvPrefix
  exact Finset.disjoint_left.mp
    (K.nextEvenCluster_disjoint_firstPrefixRegion hi)
    hvCluster hvRegion

/-- The first local target set is disjoint from the second even one-based
cluster. -/
theorem firstEvenTarget_disjoint_nextEvenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    Disjoint ((E.output ⟨0, K.hN⟩).paths.targetSet)
      (P.cluster (evenClusterIndex g
        (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))) := by
  classical
  let first : Fin (g * (g - 1)) := ⟨0, K.hN⟩
  let next : Fin (g * (g - 1)) := nextEvenClusterOrdinal first hi
  let e0 : Fin (2 * g * (g - 1)) := evenClusterIndex g first
  let e1 : Fin (2 * g * (g - 1)) := evenClusterIndex g next
  have he0_ne_e1 : e0 ≠ e1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [e0, e1, first, next, nextEvenClusterOrdinal, evenClusterIndex] at hval
  rw [Finset.disjoint_left]
  intro v hvTarget hvCluster
  have hvE0 : v ∈ P.cluster e0 :=
    P.right_subset_cluster e0
      ((E.output first).paths.targetSet_subset_right
        (by simpa [first, e0] using hvTarget))
  exact Finset.disjoint_left.mp (P.cluster_disjoint he0_ne_e1)
    hvE0 (by simpa [next, e1] using hvCluster)

/-- The global start terminals used by the stitched prefix are disjoint from
the second even one-based cluster. -/
theorem startSource_disjoint_nextEvenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    Disjoint K.start.sourceSet
      (P.cluster (evenClusterIndex g
        (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))) := by
  classical
  let first : Fin (g * (g - 1)) := ⟨0, K.hN⟩
  let next : Fin (g * (g - 1)) := nextEvenClusterOrdinal first hi
  let e1 : Fin (2 * g * (g - 1)) := evenClusterIndex g next
  have hne : P.firstIndex ≠ e1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [PathOfSetsSystem.firstIndex, e1, next, first,
      nextEvenClusterOrdinal, evenClusterIndex] at hval
  rw [Finset.disjoint_left]
  intro v hvSource hvCluster
  have hvFirst : v ∈ P.cluster P.firstIndex :=
    P.left_subset_cluster P.firstIndex (K.start.sourceSet_subset_left hvSource)
  exact Finset.disjoint_left.mp (P.cluster_disjoint hne)
    hvFirst (by simpa [next, e1] using hvCluster)

/-- The second stitched prefix is internally disjoint from the second even
one-based cluster, so the second local row pieces can be appended next. -/
theorem secondPrefix_internallyDisjoint_nextEvenCluster
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    (K.secondPrefix hi).toPathPacking.InternallyDisjointFromSet
      (P.cluster (evenClusterIndex g
        (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))) := by
  dsimp [secondPrefix, PerfectPathPacking.concatOfFirstStaysInSecondInternallyDisjoint]
  apply PerfectPathPacking.concat_internallyDisjointFromSet_right
  · exact K.firstPrefix_vertexSet_disjoint_nextEvenCluster hi
  · exact K.firstEvenTarget_disjoint_nextEvenCluster hi
  · exact K.betweenPerfect_internallyDisjoint_right ⟨0, K.hN⟩ hi

/-- The prefix through the second local even-cluster output. -/
noncomputable def thirdPrefix
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    PerfectPathPacking G K.start.sourceSet
      ((E.output (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi)).paths.targetSet) :=
  (K.secondPrefix hi).concatOfFirstInternallyDisjointSecondStaysIn
    (K.localPerfect (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))
    (K.secondPrefix_internallyDisjoint_nextEvenCluster hi)
    (K.localPerfect_staysIn (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))
    (K.startSource_disjoint_nextEvenCluster hi)

@[simp] theorem thirdPrefix_card
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    (K.thirdPrefix hi).card = q := by
  simp [thirdPrefix]

theorem thirdPrefix_staysIn
    {P : StrongPathOfSetsSystem G (2 * g * (g - 1)) w}
    {E : EvenClusterOutputs P.toPathOfSetsSystem q}
    (K : StitchingPieces P E)
    (hi : 0 + 1 < g * (g - 1)) :
    (K.thirdPrefix hi).toPathPacking.StaysIn
      (((firstStitchingRegion P K.hN ∪
          P.cluster (evenClusterIndex g ⟨0, K.hN⟩)) ∪
        betweenStitchingRegion P ⟨0, K.hN⟩ hi) ∪
          P.cluster (evenClusterIndex g
            (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))) := by
  simpa [thirdPrefix] using
    (K.secondPrefix hi).concatOfFirstInternallyDisjointSecondStaysIn_staysIn_union
      (K.localPerfect (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))
      (K.secondPrefix_internallyDisjoint_nextEvenCluster hi)
      (K.localPerfect_staysIn (nextEvenClusterOrdinal ⟨0, K.hN⟩ hi))
      (K.startSource_disjoint_nextEvenCluster hi)
      (K.secondPrefix_staysIn hi)

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

/-- Faithful local input corresponding to Chekuri--Chuzhoy Theorem 3.1.

This version includes the connected-cluster hypothesis available in every
path-of-sets application.  It matches the paper/contract statement more
closely than `LocalRoutingInput`, which is a convenient stronger interface. -/
def LocalRoutingClusterInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {C A B : Finset V} {h q w : ℕ},
      1 < h →
        1 < q →
          IsCluster G C →
            NodeLinkedIn G C A B →
              A.card = w →
                B.card = w →
                  (16 * h + 10) * q ≤ w →
                    ContainsGridMinor G h ∨
                      ∃ P : PathPacking G A B,
                        P.card = q ∧ P.StaysIn C ∧
                          P.HasPairwiseBridgesIn C

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

/-- Cluster-faithful version of
`gridMinor_or_evenClusterOutputs_of_localRoutingInput`.

The connected-cluster hypothesis is supplied by the strong path-of-sets system
itself. -/
theorem gridMinor_or_evenClusterOutputs_of_localRoutingClusterInput
    (hlocal : LocalRoutingClusterInput.{u})
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
      rcases hlocal G hgt hgt (P.cluster_connected e)
          (P.left_right_nodeLinked e) hleft hright hw with hgrid' | hpaths
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

/-- Cluster-faithful specialization of the local routing step to the width
used in Chekuri--Chuzhoy Corollary 3.3. -/
theorem gridMinor_or_evenClusterOutputs_of_localRoutingClusterInput_corollary33Width
    (hlocal : LocalRoutingClusterInput.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) {g : ℕ}
    (hg : 2 ≤ g)
    (P : StrongPathOfSetsSystem G
      (2 * g * (g - 1)) (16 * g ^ 2 + 10 * g)) :
    ContainsGridMinor G g ∨
      Nonempty (EvenClusterOutputs P.toPathOfSetsSystem g) := by
  refine gridMinor_or_evenClusterOutputs_of_localRoutingClusterInput
    hlocal G hg ?_ P
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
