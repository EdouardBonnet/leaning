import TwinWidth.Graph.FlowDefs

/-!
# Elementary API for finite path flows

This file proves basic algebraic facts about the concrete path-flow structure
from `FlowDefs`.  Substantive external theorems such as max-flow/min-cut and
integral-flow decomposition live in `FlowContract`.
-/

namespace TwinWidth
namespace SimpleGraph

universe u

open Finset

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {S T : Finset V}

namespace OrientedPathFlow

/-- The unit path flow obtained from a node-disjoint path packing, orienting
each path from `S` to `T`. -/
noncomputable def ofPathPacking (P : PathPacking G S T) :
    OrientedPathFlow G S T where
  Index := P.Index
  path := fun i => (P.path i).orient (P.connects i)
  source_mem := fun i => GraphPath.orient_source_mem (P.path i) (P.connects i)
  target_mem := fun i => GraphPath.orient_target_mem (P.path i) (P.connects i)
  weight := fun _ => 1
  weight_nonneg := fun _ => by norm_num

@[simp] theorem ofPathPacking_value (P : PathPacking G S T) :
    (ofPathPacking P).value = P.card := by
  classical
  simp [ofPathPacking, value, PathPacking.card]
  rfl

/-- The unit path flow obtained from an edge-disjoint path packing, orienting
each path from `S` to `T`. -/
noncomputable def ofEdgePathPacking (P : EdgePathPacking G S T) :
    OrientedPathFlow G S T where
  Index := P.Index
  path := fun i => (P.path i).orient (P.connects i)
  source_mem := fun i => GraphPath.orient_source_mem (P.path i) (P.connects i)
  target_mem := fun i => GraphPath.orient_target_mem (P.path i) (P.connects i)
  weight := fun _ => 1
  weight_nonneg := fun _ => by norm_num

@[simp] theorem ofEdgePathPacking_value (P : EdgePathPacking G S T) :
    (ofEdgePathPacking P).value = P.card := by
  classical
  simp [ofEdgePathPacking, value, EdgePathPacking.card]
  rfl

/-- Re-express the value of a path flow as the sum of its source loads over the
source terminal set. -/
theorem value_eq_sum_sourceLoad (F : OrientedPathFlow G S T) :
    F.value = ∑ v ∈ S, F.sourceLoad v := by
  classical
  calc
    F.value = ∑ i : F.Index, ∑ v ∈ S,
        if (F.path i).source = v then F.weight i else 0 := by
      simp only [value]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [Finset.sum_eq_single (F.path i).source]
      · simp
      · intro b hb hne
        have hne' : (F.path i).source ≠ b := fun h => hne h.symm
        simp [hne']
      · intro hnot
        exact False.elim (hnot (F.source_mem i))
    _ = ∑ v ∈ S, F.sourceLoad v := by
      rw [Finset.sum_comm]
      rfl

/-- Re-express the value of a path flow as the sum of its target loads over the
target terminal set. -/
theorem value_eq_sum_targetLoad (F : OrientedPathFlow G S T) :
    F.value = ∑ v ∈ T, F.targetLoad v := by
  classical
  calc
    F.value = ∑ i : F.Index, ∑ v ∈ T,
        if (F.path i).target = v then F.weight i else 0 := by
      simp only [value]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [Finset.sum_eq_single (F.path i).target]
      · simp
      · intro b hb hne
        have hne' : (F.path i).target ≠ b := fun h => hne h.symm
        simp [hne']
      · intro hnot
        exact False.elim (hnot (F.target_mem i))
    _ = ∑ v ∈ T, F.targetLoad v := by
      rw [Finset.sum_comm]
      rfl

/-- A unit flow has value equal to the number of source terminals. -/
theorem value_eq_card_source_of_sourceLoadExactlyOne
    (F : OrientedPathFlow G S T) (h : F.SourceLoadExactlyOne) :
    F.value = S.card := by
  classical
  rw [F.value_eq_sum_sourceLoad]
  calc
    (∑ v ∈ S, F.sourceLoad v) = ∑ v ∈ S, (1 : ℚ) := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simp [h v hv]
    _ = S.card := by
      simp

/-- A unit flow has value equal to the number of target terminals. -/
theorem value_eq_card_target_of_targetLoadExactlyOne
    (F : OrientedPathFlow G S T) (h : F.TargetLoadExactlyOne) :
    F.value = T.card := by
  classical
  rw [F.value_eq_sum_targetLoad]
  calc
    (∑ v ∈ T, F.targetLoad v) = ∑ v ∈ T, (1 : ℚ) := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simp [h v hv]
    _ = T.card := by
      simp

/-- Vertices outside the source side have zero source load. -/
theorem sourceLoad_eq_zero_of_not_mem
    (F : OrientedPathFlow G S T) {v : V} (hv : v ∉ S) :
    F.sourceLoad v = 0 := by
  classical
  unfold sourceLoad
  refine Finset.sum_eq_zero ?_
  intro i _hi
  have hne : (F.path i).source ≠ v := by
    intro h
    exact hv (by simpa [h] using F.source_mem i)
  simp [hne]

/-- Vertices outside the target side have zero target load. -/
theorem targetLoad_eq_zero_of_not_mem
    (F : OrientedPathFlow G S T) {v : V} (hv : v ∉ T) :
    F.targetLoad v = 0 := by
  classical
  unfold targetLoad
  refine Finset.sum_eq_zero ?_
  intro i _hi
  have hne : (F.path i).target ≠ v := by
    intro h
    exact hv (by simpa [h] using F.target_mem i)
  simp [hne]

/-- A unit source-load condition bounds source load at every vertex by one. -/
theorem sourceLoad_le_one_of_sourceLoadExactlyOne
    (F : OrientedPathFlow G S T) (h : F.SourceLoadExactlyOne) (v : V) :
    F.sourceLoad v ≤ 1 := by
  classical
  by_cases hv : v ∈ S
  · simp [h v hv]
  · rw [F.sourceLoad_eq_zero_of_not_mem hv]
    norm_num

/-- A unit target-load condition bounds target load at every vertex by one. -/
theorem targetLoad_le_one_of_targetLoadExactlyOne
    (F : OrientedPathFlow G S T) (h : F.TargetLoadExactlyOne) (v : V) :
    F.targetLoad v ≤ 1 := by
  classical
  by_cases hv : v ∈ T
  · simp [h v hv]
  · rw [F.targetLoad_eq_zero_of_not_mem hv]
    norm_num

/-- Scaling a finite path flow by a nonnegative rational factor. -/
noncomputable def scale (F : OrientedPathFlow G S T) (c : ℚ) (hc : 0 ≤ c) :
    OrientedPathFlow G S T where
  Index := F.Index
  path := F.path
  source_mem := F.source_mem
  target_mem := F.target_mem
  weight := fun i => c * F.weight i
  weight_nonneg := fun i => mul_nonneg hc (F.weight_nonneg i)

omit [DecidableEq V] in
@[simp] theorem scale_value (F : OrientedPathFlow G S T)
    (c : ℚ) (hc : 0 ≤ c) :
    (F.scale c hc).value = c * F.value := by
  classical
  simp only [scale, value]
  rw [Finset.mul_sum]
  rfl

@[simp] theorem scale_sourceLoad (F : OrientedPathFlow G S T)
    (c : ℚ) (hc : 0 ≤ c) (v : V) :
    (F.scale c hc).sourceLoad v = c * F.sourceLoad v := by
  classical
  simp only [scale, sourceLoad]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases h : (F.path i).source = v <;> simp [h]

@[simp] theorem scale_targetLoad (F : OrientedPathFlow G S T)
    (c : ℚ) (hc : 0 ≤ c) (v : V) :
    (F.scale c hc).targetLoad v = c * F.targetLoad v := by
  classical
  simp only [scale, targetLoad]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases h : (F.path i).target = v <;> simp [h]

@[simp] theorem scale_edgeLoad (F : OrientedPathFlow G S T)
    (c : ℚ) (hc : 0 ≤ c) (e : Sym2 V) :
    (F.scale c hc).edgeLoad e = c * F.edgeLoad e := by
  classical
  simp only [scale, edgeLoad]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases h : e ∈ (F.path i).edgeSet <;> simp [h]

@[simp] theorem scale_vertexLoad (F : OrientedPathFlow G S T)
    (c : ℚ) (hc : 0 ≤ c) (v : V) :
    (F.scale c hc).vertexLoad v = c * F.vertexLoad v := by
  classical
  simp only [scale, vertexLoad]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases h : v ∈ (F.path i).vertexSet <;> simp [h]

/-- Scaling preserves source unit constraints after the expected rescaling. -/
theorem scale_sourceLoad_eq
    (F : OrientedPathFlow G S T) (c : ℚ) (hc : 0 ≤ c)
    (h : F.SourceLoadExactlyOne) :
    ∀ v ∈ S, (F.scale c hc).sourceLoad v = c := by
  intro v hv
  simp [h v hv]

/-- Scaling an edge-congestion bound. -/
theorem scale_edgeCongestionAtMost
    (F : OrientedPathFlow G S T) {η c : ℚ} (hc : 0 ≤ c)
    (hη : F.EdgeCongestionAtMost η) :
    (F.scale c hc).EdgeCongestionAtMost (c * η) := by
  intro e he
  rw [scale_edgeLoad]
  exact mul_le_mul_of_nonneg_left (hη e he) hc

/-- Scaling a vertex-congestion bound. -/
theorem scale_vertexCongestionAtMost
    (F : OrientedPathFlow G S T) {η c : ℚ} (hc : 0 ≤ c)
    (hη : F.VertexCongestionAtMost η) :
    (F.scale c hc).VertexCongestionAtMost (c * η) := by
  intro v
  rw [scale_vertexLoad]
  exact mul_le_mul_of_nonneg_left (hη v) hc

end OrientedPathFlow

end SimpleGraph
end TwinWidth
