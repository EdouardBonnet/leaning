import «statements-and-proofs».ChekuriChuzhoySection5BandwidthDecomposition
import «statements-and-proofs».PathOfSets

/-!
# Connected cores of truncated-bandwidth clusters

Chekuri--Chuzhoy, *Polynomial Bounds for the Grid-Minor Theorem*, journal
Section 5, requires every large cluster in an acceptable clustering to be
connected.  This module supplies the finite localization used for that
condition.  A positive-boundary set with truncated bandwidth has all of its
interface vertices in one connected component of its induced graph.  That
component therefore preserves the complete original boundary and the same
truncated bandwidth.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5ConnectedBandwidthCore

universe u

open Finset
open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5BandwidthDecomposition

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A positive-boundary truncated-bandwidth set has a connected subset with
the same complete outer boundary and the same bandwidth. -/
theorem exists_connected_subset_preserving_boundary_bandwidth
    {U : Finset V} {cap D : Nat}
    (hcap : 0 < cap)
    (hboundary : 0 < (originalBoundary G U).card)
    (hband : TruncatedScaledBandwidth G U cap 1 D) :
    ∃ R : Finset V,
      R ⊆ U ∧
      IsCluster G R ∧
      originalBoundary G R = originalBoundary G U ∧
      TruncatedScaledBandwidth G R cap 1 D := by
  classical
  obtain ⟨e, heBoundary⟩ := Finset.card_pos.mp hboundary
  rcases mem_originalBoundary_iff.mp heBoundary with
    ⟨heG, u₀, hu₀U, w₀, hw₀U, rfl⟩
  have hu₀w₀ : G.Adj u₀ w₀ := by
    simpa [_root_.SimpleGraph.mem_edgeSet] using heG
  have hu₀Interface : u₀ ∈ interfaceVertices G U :=
    mem_interfaceVertices.mpr ⟨hu₀U, w₀, hw₀U, hu₀w₀⟩

  let H : _root_.SimpleGraph {v : V // v ∈ U} :=
    G.induce {v : V | v ∈ U}
  let u₀U : {v : V // v ∈ U} := ⟨u₀, hu₀U⟩
  let component : H.ConnectedComponent := H.connectedComponentMk u₀U
  let A : Finset {v : V // v ∈ U} :=
    Finset.univ.filter fun v => v ∈ component.supp
  let emb : {v : V // v ∈ U} ↪ V := Function.Embedding.subtype _
  let R : Finset V := A.map emb

  have mem_A_iff (x : {v : V // v ∈ U}) :
      x ∈ A ↔ x ∈ component.supp := by
    simp [A]

  have mem_R_of_mem_component
      (x : {v : V // v ∈ U}) (hx : x ∈ component.supp) :
      x.1 ∈ R := by
    exact Finset.mem_map.mpr ⟨x, (mem_A_iff x).2 hx, rfl⟩

  have mem_component_of_mem_R {x : V} (hx : x ∈ R) :
      ∃ hxU : x ∈ U,
        (⟨x, hxU⟩ : {v : V // v ∈ U}) ∈ component.supp := by
    rcases Finset.mem_map.mp hx with ⟨xU, hxUA, hval⟩
    subst x
    exact ⟨xU.2, (mem_A_iff xU).1 hxUA⟩

  have hRU : R ⊆ U := by
    intro x hxR
    exact (mem_component_of_mem_R hxR).choose

  have hu₀Component : u₀U ∈ component.supp := by
    exact ConnectedComponent.connectedComponentMk_mem

  have hu₀R : u₀ ∈ R :=
    mem_R_of_mem_component u₀U hu₀Component

  have component_closed
      {x y : {v : V // v ∈ U}}
      (hx : x ∈ component.supp) (hxy : H.Adj x y) :
      y ∈ component.supp :=
    component.mem_supp_of_adj_mem_supp hx hxy

  have no_edge_to_remainder {x y : V}
      (hxR : x ∈ R) (hyU : y ∈ U) (hxy : G.Adj x y) :
      y ∈ R := by
    obtain ⟨hxU, hxComponent⟩ := mem_component_of_mem_R hxR
    let xU : {v : V // v ∈ U} := ⟨x, hxU⟩
    let yU : {v : V // v ∈ U} := ⟨y, hyU⟩
    have hxyH : H.Adj xU yU := hxy
    exact mem_R_of_mem_component yU
      (component_closed hxComponent hxyH)

  have hcutEmpty :
      Section44.edgeBoundary G R (U \ R) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ x y =>
        rcases (mk_mem_edgeBoundary_iff G R (U \ R) x y).1 hedge with
          ⟨hxy, h | h⟩
        · exact (Finset.mem_sdiff.mp h.2).2
            (no_edge_to_remainder h.1 (Finset.mem_sdiff.mp h.2).1 hxy)
        · exact (Finset.mem_sdiff.mp h.2).2
            (no_edge_to_remainder h.1 (Finset.mem_sdiff.mp h.2).1 hxy.symm)

  have all_interface_mem_R :
      interfaceVertices G U ⊆ R := by
    intro x hxInterface
    by_contra hxR
    have hxU : x ∈ U := (mem_interfaceVertices.mp hxInterface).1
    have hxDiff : x ∈ U \ R := Finset.mem_sdiff.mpr ⟨hxU, hxR⟩
    have hcover : R ∪ (U \ R) = U := Finset.union_sdiff_of_subset hRU
    have hdisjoint : Disjoint R (U \ R) := Finset.disjoint_sdiff
    have hcut := hband.2.2 R (U \ R) hRU
      Finset.sdiff_subset hcover hdisjoint
    have hleft :
        0 < (R ∩ interfaceVertices G U).card :=
      Finset.card_pos.mpr
        ⟨u₀, Finset.mem_inter.mpr ⟨hu₀R, hu₀Interface⟩⟩
    have hright :
        0 < ((U \ R) ∩ interfaceVertices G U).card :=
      Finset.card_pos.mpr
        ⟨x, Finset.mem_inter.mpr ⟨hxDiff, hxInterface⟩⟩
    have hdemand :
        0 < truncatedInterfaceDemand G U R (U \ R) cap := by
      simp only [truncatedInterfaceDemand]
      omega
    rw [hcutEmpty] at hcut
    simp only [one_mul, Finset.card_empty, Nat.mul_zero] at hcut
    exact (Nat.not_lt_of_ge hcut) hdemand

  have hboundaryEq :
      originalBoundary G R = originalBoundary G U := by
    simp only [originalBoundary]
    ext edge
    induction edge using Sym2.inductionOn with
    | _ x y =>
        simp only [mk_mem_clusterBoundary_iff]
        constructor
        · rintro ⟨hxy, h | h⟩
          · have hyU : y ∉ U := by
              intro hyU
              exact h.2 (no_edge_to_remainder h.1 hyU hxy)
            exact ⟨hxy, Or.inl ⟨hRU h.1, hyU⟩⟩
          · have hxU : x ∉ U := by
              intro hxU
              exact h.2 (no_edge_to_remainder h.1 hxU hxy.symm)
            exact ⟨hxy, Or.inr ⟨hRU h.1, hxU⟩⟩
        · rintro ⟨hxy, h | h⟩
          · have hxInterface : x ∈ interfaceVertices G U :=
              mem_interfaceVertices.mpr ⟨h.1, y, h.2, hxy⟩
            exact ⟨hxy, Or.inl
              ⟨all_interface_mem_R hxInterface, fun hyR => h.2 (hRU hyR)⟩⟩
          · have hyInterface : y ∈ interfaceVertices G U :=
              mem_interfaceVertices.mpr ⟨h.1, x, h.2, hxy.symm⟩
            exact ⟨hxy, Or.inr
              ⟨all_interface_mem_R hyInterface, fun hxR => h.2 (hRU hxR)⟩⟩

  have hinterfaceEq :
      interfaceVertices G R = interfaceVertices G U := by
    ext x
    constructor
    · intro hx
      rcases mem_interfaceVertices.mp hx with ⟨hxR, y, hyR, hxy⟩
      have hyU : y ∉ U := by
        intro hyU
        exact hyR (no_edge_to_remainder hxR hyU hxy)
      exact mem_interfaceVertices.mpr ⟨hRU hxR, y, hyU, hxy⟩
    · intro hx
      rcases mem_interfaceVertices.mp hx with ⟨hxU, y, hyU, hxy⟩
      exact mem_interfaceVertices.mpr
        ⟨all_interface_mem_R hx, y, fun hyR => hyU (hRU hyR), hxy⟩

  have hcluster : IsCluster G R := by
    let f : component.toSimpleGraph →g
        G.induce {v : V | v ∈ R} := {
      toFun := fun x =>
        ⟨x.1.1, mem_R_of_mem_component x.1 x.2⟩
      map_rel' := by
        intro x y hxy
        exact hxy }
    apply component.connected_toSimpleGraph.map f
    intro y
    rcases Finset.mem_map.mp y.2 with ⟨x, hxA, hxy⟩
    have hxComponent : x ∈ component.supp := (mem_A_iff x).1 hxA
    refine ⟨⟨x, hxComponent⟩, ?_⟩
    apply Subtype.ext
    exact hxy

  have hbandR : TruncatedScaledBandwidth G R cap 1 D := by
    refine ⟨hband.1, hband.2.1, ?_⟩
    intro X Y hXR hYR hcoverR hdisjointR
    let YU := Y ∪ (U \ R)
    have hXU : X ⊆ U := hXR.trans hRU
    have hYU : YU ⊆ U := by
      intro z hz
      rcases Finset.mem_union.mp hz with hzY | hzDiff
      · exact hRU (hYR hzY)
      · exact (Finset.mem_sdiff.mp hzDiff).1
    have hcoverU : X ∪ YU = U := by
      dsimp [YU]
      rw [← Finset.union_assoc, hcoverR]
      exact Finset.union_sdiff_of_subset hRU
    have hdisjointU : Disjoint X YU := by
      rw [Finset.disjoint_left]
      intro z hzX hzYU
      rcases Finset.mem_union.mp hzYU with hzY | hzDiff
      · exact Finset.disjoint_left.mp hdisjointR hzX hzY
      · exact (Finset.mem_sdiff.mp hzDiff).2 (hXR hzX)
    have hglobal := hband.2.2 X YU hXU hYU hcoverU hdisjointU
    have hleftInterface :
        X ∩ interfaceVertices G U =
          X ∩ interfaceVertices G R := by
      rw [hinterfaceEq]
    have hrightInterface :
        YU ∩ interfaceVertices G U =
          Y ∩ interfaceVertices G R := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_union,
        Finset.mem_sdiff, YU, hinterfaceEq]
      constructor
      · rintro ⟨hzY | ⟨hzU, hzR⟩, hzInterface⟩
        · exact ⟨hzY, hzInterface⟩
        · exact False.elim (hzR (all_interface_mem_R hzInterface))
      · exact fun hz => ⟨Or.inl hz.1, hz.2⟩
    have hcutEq :
        Section44.edgeBoundary G X YU =
          Section44.edgeBoundary G X Y := by
      ext edge
      induction edge using Sym2.inductionOn with
      | _ x y =>
          simp only [mk_mem_edgeBoundary_iff]
          constructor
          · rintro ⟨hxy, h | h⟩
            · rcases Finset.mem_union.mp h.2 with hyY | hyDiff
              · exact ⟨hxy, Or.inl ⟨h.1, hyY⟩⟩
              · have hxR : x ∈ R := hXR h.1
                exact False.elim <| (Finset.mem_sdiff.mp hyDiff).2
                  (no_edge_to_remainder hxR
                    (Finset.mem_sdiff.mp hyDiff).1 hxy)
            · rcases Finset.mem_union.mp h.2 with hxY | hxDiff
              · exact ⟨hxy, Or.inr ⟨h.1, hxY⟩⟩
              · have hyR : y ∈ R := hXR h.1
                exact False.elim <| (Finset.mem_sdiff.mp hxDiff).2
                  (no_edge_to_remainder hyR
                    (Finset.mem_sdiff.mp hxDiff).1 hxy.symm)
          · rintro ⟨hxy, h | h⟩
            · exact ⟨hxy, Or.inl ⟨h.1, Finset.mem_union_left _ h.2⟩⟩
            · exact ⟨hxy, Or.inr ⟨h.1, Finset.mem_union_left _ h.2⟩⟩
    simpa [truncatedInterfaceDemand, hleftInterface,
      hrightInterface, hcutEq] using hglobal

  exact ⟨R, hRU, hcluster, hboundaryEq, hbandR⟩

/-- Immediately usable large-cluster form.  Positivity of the threshold
provides the interface vertex used to choose the component, and disjointness
from a supplied terminal set is inherited by subset containment. -/
theorem exists_connected_large_bandwidth_core
    {U terminals : Finset V} {threshold cap D : Nat}
    (hthreshold : 0 < threshold)
    (hcap : 0 < cap)
    (hlarge : IsLargeCluster G threshold U)
    (hterminals : Disjoint U terminals)
    (hband : TruncatedScaledBandwidth G U cap 1 D) :
    ∃ R : Finset V,
      R ⊆ U ∧
      IsCluster G R ∧
      IsLargeCluster G threshold R ∧
      Disjoint R terminals ∧
      originalBoundary G R = originalBoundary G U ∧
      TruncatedScaledBandwidth G R cap 1 D := by
  have hboundary : 0 < (originalBoundary G U).card := by
    exact hthreshold.trans_le hlarge
  obtain ⟨R, hRU, hcluster, hboundaryEq, hbandR⟩ :=
    exists_connected_subset_preserving_boundary_bandwidth
      hcap hboundary hband
  refine ⟨R, hRU, hcluster, ?_, hterminals.mono_left hRU,
    hboundaryEq, hbandR⟩
  simpa [IsLargeCluster, hboundaryEq] using hlarge

end ChekuriChuzhoySection5ConnectedBandwidthCore
end SimpleGraph
