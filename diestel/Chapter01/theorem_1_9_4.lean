import Chapter01.proposition_1_9_6
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dual.Basis
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

private theorem edge_inner_comm {V : Type u} (G : SimpleGraph V)
    [Fintype G.edgeSet] (F D : EdgeSpace G) :
    edge_inner G F D = edge_inner G D F := by
  unfold edge_inner
  apply Finset.sum_congr rfl
  intro e _
  rw [mul_comm]

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

private theorem edge_inner_eq_zero_of_cycle_cut {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet]
    {C D : EdgeSpace G} (hC : C ∈ cycle_space G) (hD : D ∈ cut_space G) :
    edge_inner G C D = 0 := by
  classical
  rcases ((proposition_1_9_6 G).2 D).mp hD with ⟨U, hU⟩
  have hD_eq : D = incidenceTransposeMap G U := by
    ext e
    exact hU e
  subst D
  rw [edge_inner_incidenceTransposeMap]
  apply Finset.sum_eq_zero
  intro v _
  have hzero : incidenceMap G C v = 0 := by
    simpa [incidenceMap_apply] using cycle_space_incidence_sum_zero hC v
  rw [hzero]
  simp

private theorem cycle_of_orthogonal_cut_space {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet]
    {D : EdgeSpace G} (hD : D ∈ edge_orthogonal G (cut_space G)) :
    D ∈ cycle_space G := by
  classical
  exact ((proposition_1_9_6 G).1 D).mp fun v => by
    let U : VertexSpace V := Pi.single v 1
    let C : EdgeSpace G := incidenceTransposeMap G U
    have hCcut : C ∈ cut_space G := by
      exact ((proposition_1_9_6 G).2 C).mpr ⟨U, fun e => rfl⟩
    have hinner : edge_inner G C D = 0 := hD C hCcut
    have hinner' : edge_inner G D C = 0 := by
      rw [edge_inner_comm G D C]
      exact hinner
    rw [edge_inner_incidenceTransposeMap] at hinner'
    have hsingle :
        (∑ w : V, incidenceMap G D w * U w) = incidenceMap G D v := by
      rw [Finset.sum_eq_single v]
      · simp [U]
      · intro w _ hwv
        simp [U, hwv]
      · intro hv
        exact (hv (Finset.mem_univ v)).elim
    rw [hsingle] at hinner'
    exact hinner'

private theorem cut_of_orthogonal_cycle_space {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet]
    {D : EdgeSpace G} (hD : D ∈ edge_orthogonal G (cycle_space G)) :
    D ∈ cut_space G := by
  classical
  let A := incidenceMap G
  let eDual := (Pi.basisFun (ZMod 2) G.edgeSet).toDualEquiv
  let vDual := (Pi.basisFun (ZMod 2) V).toDualEquiv
  have hdual_mem : eDual D ∈ (LinearMap.ker A).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro F hF
    have hFcycle : F ∈ cycle_space G := by
      exact ((proposition_1_9_6 G).1 F).mp fun v => by
        have hzero := congr_fun (show A F = 0 from hF) v
        simpa [A, incidenceMap_apply] using hzero
    change ((Pi.basisFun (ZMod 2) G.edgeSet).toDualEquiv D) F = 0
    rw [edge_dual_apply]
    exact hD F hFcycle
  have hrange : eDual D ∈ LinearMap.range A.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker A]
    exact hdual_mem
  rcases (LinearMap.mem_range).mp hrange with ⟨φ, hφ⟩
  rcases (LinearEquiv.surjective vDual φ) with ⟨U, rfl⟩
  have hdual_eq :
      eDual D = eDual (incidenceTransposeMap G U) := by
    rw [← hφ]
    change (incidenceMap G).dualMap ((Pi.basisFun (ZMod 2) V).toDualEquiv U) =
      (Pi.basisFun (ZMod 2) G.edgeSet).toDualEquiv (incidenceTransposeMap G U)
    exact incidence_dualMap_vertexDual G U
  have hD_eq : D = incidenceTransposeMap G U := by
    exact LinearEquiv.injective eDual hdual_eq
  rw [hD_eq]
  exact ((proposition_1_9_6 G).2 (incidenceTransposeMap G U)).mpr ⟨U, fun e => rfl⟩

/--
Diestel, Theorem 1.9.4.
The cycle space and cut space are orthogonal complements:
`C = Bᗮ` and `B = Cᗮ`.
-/
theorem theorem_1_9_4 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet] :
  ((cycle_space G : Set (EdgeSpace G)) = edge_orthogonal G (cut_space G)) ∧
    ((cut_space G : Set (EdgeSpace G)) = edge_orthogonal G (cycle_space G)) := by
  classical
  constructor
  · ext D
    constructor
    · intro hD F hF
      rw [edge_inner_comm G F D]
      exact edge_inner_eq_zero_of_cycle_cut G hD hF
    · intro hD
      exact cycle_of_orthogonal_cut_space G hD
  · ext D
    constructor
    · intro hD F hF
      exact edge_inner_eq_zero_of_cycle_cut G hF hD
    · intro hD
      exact cut_of_orthogonal_cycle_space G hD

end Chapter01
end Diestel
