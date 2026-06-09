import Chapter01.cut_space_incidence_image
import Chapter01.proposition_1_9_6
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Field.ZMod

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter01

universe u

private noncomputable def incidenceMap {V : Type u} (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableEq V] :
    EdgeSpace G →ₗ[ZMod 2] VertexSpace V where
  toFun F v := ∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then F e else 0
  map_add' := by
    intro F D
    ext v
    dsimp
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hv : v ∈ (e : Sym2 V) <;> simp [hv]
  map_smul' := by
    intro a F
    ext v
    dsimp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hv : v ∈ (e : Sym2 V) <;> simp [hv]

private noncomputable def incidenceTransposeMap {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] :
    VertexSpace V →ₗ[ZMod 2] EdgeSpace G where
  toFun U e := ∑ v : V, if v ∈ (e : Sym2 V) then U v else 0
  map_add' := by
    intro U W
    ext e
    dsimp
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ (e : Sym2 V) <;> simp [hv]
  map_smul' := by
    intro a U
    ext e
    dsimp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ (e : Sym2 V) <;> simp [hv]

private theorem incidenceMap_apply {V : Type u} (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableEq V] (F : EdgeSpace G) (v : V) :
    incidenceMap G F v = ∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then F e else 0 := rfl

private theorem incidenceTransposeMap_apply {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] (U : VertexSpace V) (e : G.edgeSet) :
    incidenceTransposeMap G U e =
      ∑ v : V, if v ∈ (e : Sym2 V) then U v else 0 := rfl

private theorem incident_pair_sum {V : Type u} [Fintype V] [DecidableEq V]
    (U : VertexSpace V) {x y : V} (hxy : x ≠ y) :
    (∑ v : V, if v ∈ s(x, y) then U v else 0) = U x + U y := by
  classical
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun v : V => v ∈ s(x, y)) = ({x, y} : Finset V) := by
    ext v
    simp [Sym2.mem_iff, eq_comm]
  rw [hfilter]
  simp [hxy]

private theorem eq_of_add_eq_zero_zmod_two {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have ha : a = -b := eq_neg_of_add_eq_zero_left h
  simpa using ha

private theorem endpoint_eq_of_mem_ker_incidenceTranspose {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] {U : VertexSpace V}
    (hU : U ∈ LinearMap.ker (incidenceTransposeMap G)) {x y : V} (hxy : G.Adj x y) :
    U x = U y := by
  classical
  let e : G.edgeSet := ⟨s(x, y), hxy⟩
  have hzero := congr_fun (show incidenceTransposeMap G U = 0 from hU) e
  rw [incidenceTransposeMap_apply, incident_pair_sum U hxy.ne] at hzero
  exact eq_of_add_eq_zero_zmod_two hzero

private theorem eq_of_walk_of_mem_ker_incidenceTranspose {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] {U : VertexSpace V}
    (hU : U ∈ LinearMap.ker (incidenceTransposeMap G)) :
    ∀ ⦃x y : V⦄, G.Walk x y → U x = U y
  | _, _, SimpleGraph.Walk.nil => rfl
  | _, _, SimpleGraph.Walk.cons hxy p =>
      (endpoint_eq_of_mem_ker_incidenceTranspose G hU hxy).trans
        (eq_of_walk_of_mem_ker_incidenceTranspose G hU p)

private theorem incidenceTransposeMap_const_one_mem_ker {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] :
    (fun _ : V => (1 : ZMod 2)) ∈ LinearMap.ker (incidenceTransposeMap G) := by
  classical
  rw [LinearMap.mem_ker]
  ext e
  rcases e with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | hf x y =>
      have hxy_adj : G.Adj x y := by
        simpa [SimpleGraph.mem_edgeSet] using hedge
      change (∑ v : V, if v ∈ s(x, y) then (1 : ZMod 2) else 0) = 0
      rw [incident_pair_sum (fun _ : V => (1 : ZMod 2)) hxy_adj.ne]
      decide

private theorem incidenceTransposeMap_ker_eq_const_span {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] (hG : G.Connected) :
    LinearMap.ker (incidenceTransposeMap G) =
      Submodule.span (ZMod 2) ({fun _ : V => (1 : ZMod 2)} : Set (VertexSpace V)) := by
  classical
  apply le_antisymm
  · intro U hU
    let r : V := Classical.choice hG.nonempty
    have hconst : U = (U r) • (fun _ : V => (1 : ZMod 2)) := by
      ext v
      obtain ⟨p, _hp⟩ := hG.exists_isPath r v
      have hp_eq : U r = U v := eq_of_walk_of_mem_ker_incidenceTranspose G hU p
      rw [← hp_eq]
      simp
    rw [hconst]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.span_le.mpr fun U hU => by
      rcases hU with rfl
      exact incidenceTransposeMap_const_one_mem_ker G

private theorem incidenceTransposeMap_ker_finrank {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] (hG : G.Connected) :
    Module.finrank (ZMod 2) (LinearMap.ker (incidenceTransposeMap G)) = 1 := by
  classical
  rw [incidenceTransposeMap_ker_eq_const_span G hG]
  have hone_ne : (fun _ : V => (1 : ZMod 2)) ≠ (0 : VertexSpace V) := by
    intro h
    have h0 := congr_fun h (Classical.choice hG.nonempty)
    norm_num at h0
  simpa using (finrank_span_singleton (K := ZMod 2) (V := VertexSpace V) hone_ne)

private theorem cut_space_eq_incidenceTransposeMap_range {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] :
    cut_space G = LinearMap.range (incidenceTransposeMap G) := by
  classical
  ext D
  constructor
  · intro hD
    rcases (cut_space_incidence_image G D).mp hD with ⟨U, hU⟩
    exact ⟨U, by ext e; exact (hU e).symm⟩
  · rintro ⟨U, rfl⟩
    exact (cut_space_incidence_image G (incidenceTransposeMap G U)).mpr ⟨U, fun e => rfl⟩

theorem cut_space_finrank_connected {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] (hG : G.Connected) :
    Module.finrank (ZMod 2) (cut_space G) = Fintype.card V - 1 := by
  classical
  have hrank :=
    LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) (incidenceTransposeMap G)
  rw [incidenceTransposeMap_ker_finrank G hG] at hrank
  have hdomain : Module.finrank (ZMod 2) (VertexSpace V) = Fintype.card V := by
    exact Module.finrank_fintype_fun_eq_card (ZMod 2)
  rw [hdomain] at hrank
  rw [cut_space_eq_incidenceTransposeMap_range G]
  omega

private theorem cycle_space_eq_incidenceMap_ker {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet] :
    cycle_space G = LinearMap.ker (incidenceMap G) := by
  classical
  ext F
  constructor
  · intro hF
    rw [LinearMap.mem_ker]
    ext v
    simpa [incidenceMap_apply] using cycle_space_incidence_sum_zero hF v
  · intro hF
    exact ((proposition_1_9_6 G).1 F).mp fun v => by
      have hzero := congr_fun (show incidenceMap G F = 0 from hF) v
      simpa [incidenceMap_apply] using hzero

private theorem pi_dual_dot {α : Type u} [Fintype α] [DecidableEq α]
    (x y : α → ZMod 2) :
    ((Pi.basisFun (ZMod 2) α).toDualEquiv x) y = ∑ i, y i * x i := by
  classical
  have hy : y = ∑ i, Pi.single i (y i) := by
    ext j
    simpa [Finset.sum_apply] using (Fintype.sum_pi_single j y).symm
  rw [hy]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.Basis.toDualEquiv_apply]
  rw [show Pi.single i (y i) = y i • (Pi.basisFun (ZMod 2) α) i by
    ext j
    by_cases h : j = i
    · subst j
      simp [Pi.basisFun]
    · simp [Pi.basisFun, Pi.single_eq_of_ne h]]
  rw [map_smul]
  rw [Module.Basis.toDual_apply_left]
  simp [Pi.basisFun]

private theorem edge_dual_apply {V : Type u} (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableEq G.edgeSet] (D F : EdgeSpace G) :
    ((Pi.basisFun (ZMod 2) G.edgeSet).toDualEquiv D) F = edge_inner G F D := by
  rw [pi_dual_dot D F]
  rfl

private theorem vertex_dual_apply {V : Type u} [Fintype V] [DecidableEq V]
    (U W : VertexSpace V) :
    ((Pi.basisFun (ZMod 2) V).toDualEquiv U) W = ∑ v, W v * U v := by
  exact pi_dual_dot U W

private theorem edge_inner_incidenceTransposeMap {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet]
    (F : EdgeSpace G) (U : VertexSpace V) :
    edge_inner G F (incidenceTransposeMap G U) =
      ∑ v : V, incidenceMap G F v * U v := by
  classical
  simp only [edge_inner, incidenceTransposeMap_apply, incidenceMap_apply]
  calc
    (∑ e : G.edgeSet,
        F e * (∑ v : V, if v ∈ (e : Sym2 V) then U v else 0))
        = ∑ e : G.edgeSet, ∑ v : V,
            F e * (if v ∈ (e : Sym2 V) then U v else 0) := by
            apply Finset.sum_congr rfl
            intro e _
            rw [Finset.mul_sum]
    _ = ∑ v : V, ∑ e : G.edgeSet,
            F e * (if v ∈ (e : Sym2 V) then U v else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ v : V, ∑ e : G.edgeSet,
            (if v ∈ (e : Sym2 V) then F e else 0) * U v := by
          apply Finset.sum_congr rfl
          intro v _
          apply Finset.sum_congr rfl
          intro e _
          by_cases hv : v ∈ (e : Sym2 V) <;> simp [hv]
    _ = ∑ v : V,
            (∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then F e else 0) * U v := by
          apply Finset.sum_congr rfl
          intro v _
          rw [Finset.sum_mul]

private theorem incidence_dualMap_vertexDual {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    (U : VertexSpace V) :
    (incidenceMap G).dualMap ((Pi.basisFun (ZMod 2) V).toDualEquiv U) =
      (Pi.basisFun (ZMod 2) G.edgeSet).toDualEquiv
        (incidenceTransposeMap G U) := by
  classical
  apply LinearMap.ext
  intro F
  rw [LinearMap.dualMap_apply]
  rw [vertex_dual_apply]
  rw [edge_dual_apply]
  rw [edge_inner_incidenceTransposeMap]

private theorem incidenceTransposeMap_finrank_range_eq_incidenceMap {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [Fintype G.edgeSet] :
    Module.finrank (ZMod 2) (LinearMap.range (incidenceTransposeMap G)) =
      Module.finrank (ZMod 2) (LinearMap.range (incidenceMap G)) := by
  classical
  let A := incidenceMap G
  let AT := incidenceTransposeMap G
  let eDual := (Pi.basisFun (ZMod 2) G.edgeSet).toDualEquiv
  let vDual := (Pi.basisFun (ZMod 2) V).toDualEquiv
  have hcomp : A.dualMap.comp vDual.toLinearMap = eDual.toLinearMap.comp AT := by
    apply LinearMap.ext
    intro U
    change A.dualMap (vDual U) = eDual (AT U)
    exact incidence_dualMap_vertexDual G U
  have hleft :
      Module.finrank (ZMod 2) (LinearMap.range (A.dualMap.comp vDual.toLinearMap)) =
        Module.finrank (ZMod 2) (LinearMap.range A.dualMap) := by
    rw [LinearMap.range_comp_of_range_eq_top A.dualMap (LinearEquiv.range vDual)]
  have hright :
      Module.finrank (ZMod 2) (LinearMap.range (eDual.toLinearMap.comp AT)) =
        Module.finrank (ZMod 2) (LinearMap.range AT) := by
    rw [LinearMap.range_comp]
    exact LinearEquiv.finrank_map_eq eDual (LinearMap.range AT)
  calc
    Module.finrank (ZMod 2) (LinearMap.range AT)
        = Module.finrank (ZMod 2) (LinearMap.range (eDual.toLinearMap.comp AT)) := hright.symm
    _ = Module.finrank (ZMod 2) (LinearMap.range (A.dualMap.comp vDual.toLinearMap)) := by
          rw [hcomp]
    _ = Module.finrank (ZMod 2) (LinearMap.range A.dualMap) := hleft
    _ = Module.finrank (ZMod 2) (LinearMap.range A) :=
          LinearMap.finrank_range_dualMap_eq_finrank_range A

theorem cycle_space_finrank_connected {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet] (hG : G.Connected) :
    Module.finrank (ZMod 2) (cycle_space G) =
      G.edgeFinset.card + 1 - Fintype.card V := by
  classical
  let A := incidenceMap G
  have hcycle : cycle_space G = LinearMap.ker A := cycle_space_eq_incidenceMap_ker G
  have hA_rank :
      Module.finrank (ZMod 2) (LinearMap.range A) = Fintype.card V - 1 := by
    change Module.finrank (ZMod 2) (LinearMap.range (incidenceMap G)) =
      Fintype.card V - 1
    rw [← incidenceTransposeMap_finrank_range_eq_incidenceMap G]
    rw [← cut_space_eq_incidenceTransposeMap_range G]
    exact cut_space_finrank_connected G hG
  have hrank := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) A
  rw [← hcycle] at hrank
  rw [hA_rank] at hrank
  have hedge : Module.finrank (ZMod 2) (EdgeSpace G) = Fintype.card G.edgeSet := by
    exact Module.finrank_fintype_fun_eq_card (ZMod 2)
  rw [hedge] at hrank
  have hedge_card : Fintype.card G.edgeSet = G.edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_card]
  rw [hedge_card] at hrank
  have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hG.nonempty
  have hcycle :
      Module.finrank (ZMod 2) (cycle_space G) =
        G.edgeFinset.card - (Fintype.card V - 1) := by
    omega
  have hle_edges : Fintype.card V - 1 ≤ G.edgeFinset.card := by
    omega
  have hsub :
      G.edgeFinset.card - (Fintype.card V - 1) =
        G.edgeFinset.card + 1 - Fintype.card V := by
    omega
  rw [hcycle, hsub]

end Chapter01
end Diestel
