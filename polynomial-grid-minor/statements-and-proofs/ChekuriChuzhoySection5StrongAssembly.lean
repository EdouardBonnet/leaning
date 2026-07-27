import «statements-and-proofs».ChekuriChuzhoySection5Phase2Assembly
import «statements-and-proofs».TreeOfSetsSourceSharpStrongification

/-!
# Section 5 strong tree-of-sets assembly

This module composes the ordinary Phase 2 tree produced in journal Section 5
with the source-sharp two-pass strongification of Lemma 4.5.  The cluster
identity is retained so that a tree built in the pendant host can subsequently
be projected to the original graph.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5StrongAssembly

universe u

open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5Phase2Assembly
open ChekuriChuzhoySection5Superterminals

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Phase 2 followed by source-sharp strongification, with the original
router clusters exposed in the conclusion. -/
theorem exists_strongTreeOfSetsSystem_of_pairwise_direct_packings
    (G : _root_.SimpleGraph V)
    {m mu w cap alphaNum alphaDen Delta : Nat}
    {q0 groupedWidth0 carrierWidth0 passWidth
      q1 groupedWidth1 carrierWidth1 W : Nat}
    (cluster B : Fin m → Finset V)
    (hm : 2 ≤ m) (hmu : 1 ≤ mu) (hw : 0 < w)
    (hwidth : m ^ 4 * w ≤ 2 * mu)
    (hBcard : ∀ i : Fin m, (B i).card = mu)
    (hinterface :
      ∀ i : Fin m, B i ⊆ interfaceVertices G (cluster i))
    (hdirect : BoundaryPathsDirect G cluster B)
    (hpacking :
      ∀ i j : Fin m, i ≠ j →
        ∃ P : PathPacking G (B i) (B j), P.card = mu)
    (hclusterConnected : ∀ i : Fin m, IsCluster G (cluster i))
    (hclusterDisjoint :
      ∀ ⦃i j : Fin m⦄, i ≠ j → Disjoint (cluster i) (cluster j))
    (hband :
      ∀ i : Fin m,
        TruncatedScaledBandwidth
          G (cluster i) cap alphaNum alphaDen)
    (hcap : 3 * w ≤ cap)
    (hdegree : MaxDegreeAtMost G Delta) (hDelta : 3 ≤ Delta)
    (hq0 : 0 < q0) (hq0Width : q0 ≤ w)
    (hscale0 : alphaDen ≤ alphaNum * q0)
    (hgroupWidth0 : groupedWidth0 ≤ w / (3 * q0))
    (hextract0 : carrierWidth0 ≤ (3 * groupedWidth0) / (20 * Delta))
    (hpassCarrier : passWidth ≤ carrierWidth0)
    (hlink0 : 4 * Delta * passWidth ≤ carrierWidth0)
    (hq1 : 0 < q1) (hq1Width : q1 ≤ passWidth)
    (hscale1 : alphaDen ≤ alphaNum * q1)
    (hgroupWidth1 : groupedWidth1 ≤ passWidth / (3 * q1))
    (hextract1 : carrierWidth1 ≤ (3 * groupedWidth1) / (20 * Delta))
    (hWCarrier : W ≤ carrierWidth1)
    (hlink1 : 4 * Delta * W ≤ carrierWidth1)
    (hWpos : 0 < W) :
    ∃ S : StrongTreeOfSetsSystem G m W,
      ∀ i : Fin m, S.cluster i = cluster i := by
  obtain ⟨T, hTcluster⟩ :=
    exists_bandwidthTreeOfSetsSystem_of_pairwise_direct_packings_with_same_clusters
      G cluster B hm hmu hw hwidth hBcard hinterface hdirect hpacking
      hclusterConnected hclusterDisjoint hband hcap
  obtain ⟨S, hScluster⟩ :=
    T.exists_strongTreeOfSetsSystem_of_bandwidth_sourceSharp_with_same_clusters
      hdegree hDelta
      hq0 hq0Width hscale0 hgroupWidth0 hextract0 hpassCarrier hlink0
      hq1 hq1Width hscale1 hgroupWidth1 hextract1 hWCarrier hlink1 hWpos
  exact ⟨S, fun i => (hScluster i).trans (hTcluster i)⟩

end ChekuriChuzhoySection5StrongAssembly
end SimpleGraph
