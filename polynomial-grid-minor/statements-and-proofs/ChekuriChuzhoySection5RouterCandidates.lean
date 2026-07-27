import «statements-and-proofs».CNS13FailedRouterDeletion
import «statements-and-proofs».ChekuriChuzhoySection5ConnectedBandwidthCore
import «statements-and-proofs».ChekuriChuzhoySection5DenseRouterFamily

/-!
# Good-router production from dense blocks

The dense-block replacement theorem first returns large bandwidth sets that
need not be connected.  Passing to the component carrying their complete
boundary gives the exact `CNS13.RouterCandidate` records.  Edge-minimality
then invokes the one authorized CNS13 dependency to supply their terminal
routings.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5RouterCandidates

universe u

open Finset
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5ConnectedBandwidthCore
open ChekuriChuzhoySection5DensePartition
open ChekuriChuzhoySection5DensePartition.FiniteEdgeIndexedGraph
open ChekuriChuzhoySection5GoodClustering
open ChekuriChuzhoySection5MinimalHost
open ChekuriChuzhoySection5RouterProduction
open ChekuriChuzhoySection5Routers

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Dense replacement plus connected-component localization produces a
pairwise-disjoint family of actual router candidates. -/
theorem exists_routerCandidateFamily
    (G : _root_.SimpleGraph V) (terminals : Finset V)
    (cap ell0 : Nat) (hell0 : 0 < ell0) (hcap : 0 < cap)
    (P : VertexClustering V)
    (hminimum :
      IsMinimumGoodClustering G terminals
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0)
        cap 1
        (16 * (20 * ell0) * (Nat.log 2 cap + 1)) P)
    (hthreshold :
      0 < claim59SourceDegreeCap
        (contractedTerminals P terminals).card ell0)
    (hterminalTwo : 2 ≤ terminals.card)
    (hpendant : ∀ t ∈ terminals,
      (originalBoundary G ({t} : Finset V)).card = 1)
    (hterminalCard : terminals.card ≤
      3 * (nonterminalEdges (legalContractedGraph G P)
        (contractedTerminals P terminals)).card) :
    ∃ router : Fin ell0 → Finset V,
      Pairwise (fun i j => Disjoint (router i) (router j)) ∧
      ∀ i, CNS13.RouterCandidate G terminals (router i)
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0)
        cap 1
        (16 * (20 * ell0) * (Nat.log 2 cap + 1)) := by
  classical
  let threshold :=
    claim59SourceDegreeCap (contractedTerminals P terminals).card ell0
  let denominator := 16 * (20 * ell0) * (Nat.log 2 cap + 1)
  obtain ⟨piece, hpieceDisjoint, hpiece⟩ :=
    ChekuriChuzhoySection5DenseRouterFamily.exists_denseRouterFamily
      G terminals cap ell0 hell0 P hminimum hterminalTwo hpendant
        hterminalCard
  have hcore :
      ∀ i : Fin ell0, ∃ R : Finset V,
        R ⊆ piece i ∧
        CNS13.RouterCandidate G terminals R
          threshold cap 1 denominator := by
    intro i
    obtain ⟨R, hRpiece, hRconnected, hRlarge, hRterminal,
        _hboundary, hRband⟩ :=
      exists_connected_large_bandwidth_core
        (G := G) (threshold := threshold) (cap := cap)
        (D := denominator)
        (by simpa [threshold] using hthreshold) hcap
        (by simpa [threshold] using (hpiece i).2.1)
        (hpiece i).1
        (by simpa [denominator] using (hpiece i).2.2)
    exact ⟨R, hRpiece, {
      terminal_disjoint := hRterminal
      connected := hRconnected
      large := hRlarge
      bandwidth := hRband }⟩
  let router : Fin ell0 → Finset V :=
    fun i => Classical.choose (hcore i)
  have hrouter :
      ∀ i : Fin ell0,
        router i ⊆ piece i ∧
        CNS13.RouterCandidate G terminals (router i)
          threshold cap 1 denominator :=
    fun i => Classical.choose_spec (hcore i)
  refine ⟨router, ?_, ?_⟩
  · intro i j hij
    exact (hpieceDisjoint hij).mono (hrouter i).1 (hrouter j).1
  · intro i
    simpa [threshold, denominator] using (hrouter i).2

/-- In an edge-minimal host, the candidate family is a good-router family.
The only non-structural theorem used by this promotion is
`CNS13.exists_deletableEdge_of_failed_router`. -/
theorem exists_goodRouterFamily_of_minimumGoodClustering
    {G0 : _root_.SimpleGraph V}
    (M : EdgeMinimalNodeWellLinkedHost G0 terminals)
    (cap ell0 : Nat) (hell0 : 0 < ell0) (hcap : 0 < cap)
    (P : VertexClustering V)
    (hminimum :
      IsMinimumGoodClustering M.H terminals
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0)
        cap 1
        (16 * (20 * ell0) * (Nat.log 2 cap + 1)) P)
    (hthreshold :
      0 < claim59SourceDegreeCap
        (contractedTerminals P terminals).card ell0)
    (hterminalTwo : 2 ≤ terminals.card)
    (hterminalDegree : ∀ t ∈ terminals, DegreeEquals M.H t 1)
    (hpendant : ∀ t ∈ terminals,
      (originalBoundary M.H ({t} : Finset V)).card = 1)
    (hterminalCard : terminals.card ≤
      3 * (nonterminalEdges (legalContractedGraph M.H P)
        (contractedTerminals P terminals)).card) :
    Nonempty
      (GoodRouterFamily M.H terminals ell0
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0)
        cap 1
        (16 * (20 * ell0) * (Nat.log 2 cap + 1))
        (claim59SourceDegreeCap
          (contractedTerminals P terminals).card ell0 / 2)) := by
  obtain ⟨router, hdisjoint, hcandidate⟩ :=
    exists_routerCandidateFamily M.H terminals cap ell0 hell0 hcap P
      hminimum hthreshold hterminalTwo hpendant hterminalCard
  exact ⟨CNS13.goodRouterFamily_of_candidates_edgeMinimal
    M hterminalTwo hterminalDegree router hcandidate hdisjoint⟩

end ChekuriChuzhoySection5RouterCandidates
end SimpleGraph
