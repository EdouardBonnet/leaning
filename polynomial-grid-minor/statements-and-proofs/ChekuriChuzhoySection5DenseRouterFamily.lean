import «statements-and-proofs».ChekuriChuzhoySection5DenseBlockReplacement

/-!
# Dense bandwidth pieces for Chekuri--Chuzhoy Section 5.1

This module combines journal Claim 5.9 with the bandwidth decomposition and
minimum-good-clustering replacement argument.  Each dense contracted block
contains a large part with the source truncated-bandwidth guarantee.  Since
the contracted blocks are disjoint and avoid contracted terminals, the
chosen original-vertex parts are pairwise disjoint and avoid the original
terminal set.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5DenseRouterFamily

universe u

open Finset
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5BandwidthDecomposition
open ChekuriChuzhoySection5DenseBlockReplacement
open ChekuriChuzhoySection5DensePartition
open ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph
open ChekuriChuzhoySection5GoodClustering
open ChekuriChuzhoySection5RouterProduction

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The Section 5.1 dense blocks contain pairwise-disjoint, terminal-free
large bandwidth pieces.  The denominator is the source decomposition
denominator with recursion budget `20 * ell0`. -/
theorem exists_denseRouterFamily
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (cap ell0 : Nat) (hell0 : 0 < ell0)
    (P : VertexClustering V)
    (hminimum :
      IsMinimumGoodClustering G terminals
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0)
        cap 1
        (16 * (20 * ell0) * (Nat.log 2 cap + 1)) P)
    (hterminalTwo : 2 ≤ terminals.card)
    (hpendant : ∀ t ∈ terminals,
      (originalBoundary G ({t} : Finset V)).card = 1)
    (hterminalCard : terminals.card ≤
      3 * (nonterminalEdges (legalContractedGraph G P)
        (contractedTerminals P terminals)).card) :
    ∃ router : Fin ell0 → Finset V,
      Pairwise (fun i j => Disjoint (router i) (router j)) ∧
      ∀ i,
        Disjoint (router i) terminals ∧
        IsLargeCluster G
          (claim59SourceDegreeCap
            (contractedTerminals P terminals).card ell0)
          (router i) ∧
        TruncatedScaledBandwidth G (router i) cap 1
          (16 * (20 * ell0) * (Nat.log 2 cap + 1)) := by
  classical
  let H := legalContractedGraph G P
  let T := contractedTerminals P terminals
  let threshold := claim59SourceDegreeCap T.card ell0
  let denominator := 16 * (20 * ell0) * (Nat.log 2 cap + 1)
  let edgeCount := (nonterminalEdges H T).card
  have hgood :
      IsGood G terminals threshold cap 1 denominator P := by
    simpa [H, T, threshold, denominator] using hminimum.good
  obtain ⟨blocks, hblocksTerminal, _hpartition, hblocksDisjoint,
      hblockBoundary, hblockInternal⟩ :=
    exists_densePartition_of_goodClustering_source_parameters
      (G := G) (P := P) hell0 hgood hterminalTwo hpendant
        (by simpa [H, T, edgeCount] using hterminalCard)
  have hblockTerminalDisjoint :
      ∀ i, Disjoint (blocks i) T := by
    intro i
    rw [Finset.disjoint_left]
    intro C hCB hCT
    exact (Finset.mem_sdiff.mp (hblocksTerminal i hCB)).2 hCT
  have hpart :
      ∀ i : Fin ell0, ∃ U : Finset V,
        U ⊆ selectedUnion (blocks i) ∧
        IsLargeCluster G threshold U ∧
        TruncatedScaledBandwidth G U cap 1 denominator := by
    intro i
    obtain ⟨Q, hQband, hQcross⟩ :=
      BandwidthSplitTree.exists_bandwidthDecomposition_crossing_le
        G (selectedUnion (blocks i)) cap (20 * ell0) (by omega)
    have hboundary :
        ell0 *
            (Section44.clusterBoundary G
              (selectedUnion (blocks i))).card <
          10 * edgeCount := by
      rw [← legalContracted_boundary_card_eq_clusterBoundary_card
        G P (blocks i)]
      simpa [H, T, edgeCount] using hblockBoundary i
    have hinternal :
        edgeCount ≤
          2 * ell0 ^ 2 *
            (internalEdges H (blocks i)).card := by
      simpa [H, T, edgeCount] using hblockInternal i
    have hboundaryStrict :
        (Section44.clusterBoundary G
            (selectedUnion (blocks i))).card <
          20 * ell0 * (internalEdges H (blocks i)).card := by
      have hscaled :
          ell0 *
              (Section44.clusterBoundary G
                (selectedUnion (blocks i))).card <
            ell0 *
              (20 * ell0 * (internalEdges H (blocks i)).card) := by
        calc
          ell0 *
                (Section44.clusterBoundary G
                  (selectedUnion (blocks i))).card
              < 10 * edgeCount := hboundary
          _ ≤ 10 *
                (2 * ell0 ^ 2 *
                  (internalEdges H (blocks i)).card) :=
            Nat.mul_le_mul_left 10 hinternal
          _ = ell0 *
                (20 * ell0 * (internalEdges H (blocks i)).card) := by
            ring
      exact Nat.lt_of_mul_lt_mul_left hscaled
    have hsaving :
        (crossingEdges G (selectedUnion (blocks i)) Q).card <
          (internalEdges H (blocks i)).card := by
      have hscaled :
          (20 * ell0) *
              (crossingEdges G (selectedUnion (blocks i)) Q).card <
            (20 * ell0) * (internalEdges H (blocks i)).card := by
        exact lt_of_le_of_lt hQcross hboundaryStrict
      exact Nat.lt_of_mul_lt_mul_left hscaled
    obtain ⟨U, hUQ, hUlarge, hUband⟩ :=
      exists_large_bandwidth_part_of_dense_block_replacement
        G terminals threshold cap 1 denominator P
        (by simpa [threshold, denominator] using hminimum)
        (blocks i) (by simpa [T] using hblockTerminalDisjoint i)
        Q (by simpa [denominator] using hQband)
        (by simpa [H] using hsaving)
    exact ⟨U, Q.subset hUQ, hUlarge, hUband⟩
  let router : Fin ell0 → Finset V :=
    fun i => Classical.choose (hpart i)
  have hrouter :
      ∀ i : Fin ell0,
        router i ⊆ selectedUnion (blocks i) ∧
        IsLargeCluster G threshold (router i) ∧
        TruncatedScaledBandwidth G (router i) cap 1 denominator :=
    fun i => Classical.choose_spec (hpart i)
  refine ⟨router, ?_, ?_⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    have hviBlock :
        contractedVertex P v ∈ blocks i :=
      (mem_selectedUnion_iff (blocks i) v).1
        ((hrouter i).1 hvi)
    have hvjBlock :
        contractedVertex P v ∈ blocks j :=
      (mem_selectedUnion_iff (blocks j) v).1
        ((hrouter j).1 hvj)
    exact Finset.disjoint_left.mp (hblocksDisjoint i j hij)
      hviBlock hvjBlock
  · intro i
    refine ⟨?_, (hrouter i).2.1, (hrouter i).2.2⟩
    rw [Finset.disjoint_left]
    intro v hvi hvt
    have hviBlock :
        contractedVertex P v ∈ blocks i :=
      (mem_selectedUnion_iff (blocks i) v).1
        ((hrouter i).1 hvi)
    have hviTerminal : contractedVertex P v ∈ T := by
      apply (mem_contractedTerminals P terminals _).2
      exact ⟨v, hvt, rfl⟩
    exact Finset.disjoint_left.mp (hblockTerminalDisjoint i)
      hviBlock hviTerminal

end ChekuriChuzhoySection5DenseRouterFamily
end SimpleGraph
