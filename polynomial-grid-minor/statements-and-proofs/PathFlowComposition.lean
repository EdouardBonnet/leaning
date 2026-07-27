import «statements-and-proofs».ChekuriChuzhoySection5Phase1Flow

/-!
# Composition of finite unit path flows

At an intermediate terminal `v`, both unit flows carry total mass one.  Their
incoming and outgoing path distributions can therefore be coupled by the
product measure.  Incompatible path pairs receive weight zero; a fixed
compatible outgoing path is used only to give those zero-weight indices a
well-typed concatenated path.

This is the finite rational composition operation used in Claim 5.14.  It
preserves unit source and target loads, and its edge-congestion bound is the
sum of the two input bounds.
-/

namespace SimpleGraph
namespace OrientedPathFlow

universe u

open Finset
open ChekuriChuzhoySection5Phase1Flow

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {S T U : Finset V}

private theorem exists_source_match
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQ : Q.SourceLoadExactlyOne)
    (i : F.Index) :
    ∃ j : Q.Index, (F.path i).target = (Q.path j).source := by
  classical
  by_contra h
  push_neg at h
  have hload := hQ (F.path i).target (F.target_mem i)
  rw [sourceLoad] at hload
  have hzero :
      (∑ j : Q.Index,
        if (Q.path j).source = (F.path i).target
        then Q.weight j else 0) = 0 := by
    simp [fun j => (h j).symm]
  rw [hzero] at hload
  norm_num at hload

/-- A compatible outgoing path used only for zero-weight incompatible pairs. -/
noncomputable def couplingFallback
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQ : Q.SourceLoadExactlyOne)
    (i : F.Index) : Q.Index :=
  Classical.choose (exists_source_match F Q hQ i)

theorem couplingFallback_spec
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQ : Q.SourceLoadExactlyOne)
    (i : F.Index) :
    (F.path i).target = (Q.path (couplingFallback F Q hQ i)).source :=
  Classical.choose_spec (exists_source_match F Q hQ i)

/-- The concatenated path assigned to one pair of input path indices. -/
noncomputable def couplingPath
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQ : Q.SourceLoadExactlyOne)
    (i : F.Index) (j : Q.Index) :
    _root_.SimpleGraph.GraphPath G :=
  if h : (F.path i).target = (Q.path j).source then
    GraphPath.concatErase (F.path i) (Q.path j) h
  else
    GraphPath.concatErase (F.path i)
      (Q.path (couplingFallback F Q hQ i))
      (couplingFallback_spec F Q hQ i)

@[simp] theorem couplingPath_source
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQ : Q.SourceLoadExactlyOne)
    (i : F.Index) (j : Q.Index) :
    (couplingPath F Q hQ i j).source = (F.path i).source := by
  classical
  simp only [couplingPath]
  split <;> simp

theorem couplingPath_target_of_compatible
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQ : Q.SourceLoadExactlyOne)
    (i : F.Index) (j : Q.Index)
    (h : (F.path i).target = (Q.path j).source) :
    (couplingPath F Q hQ i j).target = (Q.path j).target := by
  simp [couplingPath, h]

/-- Product coupling of two unit path flows at their common terminal set. -/
noncomputable def couple
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQ : Q.SourceLoadExactlyOne) :
    OrientedPathFlow G S U where
  Index := F.Index × Q.Index
  path := fun z => couplingPath F Q hQ z.1 z.2
  source_mem := fun z => by
    rw [couplingPath_source]
    exact F.source_mem z.1
  target_mem := fun z => by
    classical
    by_cases h : (F.path z.1).target = (Q.path z.2).source
    · rw [couplingPath_target_of_compatible F Q hQ z.1 z.2 h]
      exact Q.target_mem z.2
    · simp [couplingPath, h]
      exact Q.target_mem (couplingFallback F Q hQ z.1)
  weight := fun z =>
    if (F.path z.1).target = (Q.path z.2).source then
      F.weight z.1 * Q.weight z.2
    else 0
  weight_nonneg := fun z => by
    split
    · exact mul_nonneg (F.weight_nonneg z.1) (Q.weight_nonneg z.2)
    · exact le_rfl

private theorem sum_compatible_right
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQ : Q.SourceLoadExactlyOne)
    (i : F.Index) :
    (∑ j : Q.Index,
      if (F.path i).target = (Q.path j).source
      then F.weight i * Q.weight j else 0) = F.weight i := by
  classical
  calc
    (∑ j : Q.Index,
        if (F.path i).target = (Q.path j).source
        then F.weight i * Q.weight j else 0) =
        F.weight i * Q.sourceLoad (F.path i).target := by
      rw [sourceLoad, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases h : (F.path i).target = (Q.path j).source
      · have h' : (Q.path j).source = (F.path i).target := h.symm
        simp only [if_pos h, if_pos h']
      · have h' : ¬(Q.path j).source = (F.path i).target :=
          fun h' => h h'.symm
        simp only [if_neg h, if_neg h', mul_zero]
    _ = F.weight i := by
      rw [hQ (F.path i).target (F.target_mem i)]
      ring

private theorem sum_compatible_left
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hF : F.TargetLoadExactlyOne)
    (j : Q.Index) :
    (∑ i : F.Index,
      if (F.path i).target = (Q.path j).source
      then F.weight i * Q.weight j else 0) = Q.weight j := by
  classical
  calc
    (∑ i : F.Index,
        if (F.path i).target = (Q.path j).source
        then F.weight i * Q.weight j else 0) =
        F.targetLoad (Q.path j).source * Q.weight j := by
      rw [targetLoad, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases h : (F.path i).target = (Q.path j).source
      · simp [h]
      · simp [h]
    _ = Q.weight j := by
      rw [hF (Q.path j).source (Q.source_mem j)]
      ring

theorem couple_sourceLoad
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQ : Q.SourceLoadExactlyOne)
    (v : V) :
    (couple F Q hQ).sourceLoad v = F.sourceLoad v := by
  classical
  rw [sourceLoad, sourceLoad]
  change
    (∑ z : F.Index × Q.Index,
      if (couplingPath F Q hQ z.1 z.2).source = v
      then (if (F.path z.1).target = (Q.path z.2).source
        then F.weight z.1 * Q.weight z.2 else 0)
      else 0) =
    ∑ i : F.Index,
      if (F.path i).source = v then F.weight i else 0
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show (∑ j : Q.Index,
      if (couplingPath F Q hQ i j).source = v
      then (if (F.path i).target = (Q.path j).source
        then F.weight i * Q.weight j else 0)
      else 0) =
      if (F.path i).source = v then
        (∑ j : Q.Index,
          if (F.path i).target = (Q.path j).source
          then F.weight i * Q.weight j else 0)
      else 0 by
        by_cases h : (F.path i).source = v
        · simp [couplingPath_source, h]
        · simp [couplingPath_source, h]]
  rw [sum_compatible_right F Q hQ i]

theorem couple_targetLoad
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hF : F.TargetLoadExactlyOne)
    (hQ : Q.SourceLoadExactlyOne)
    (v : V) :
    (couple F Q hQ).targetLoad v = Q.targetLoad v := by
  classical
  rw [targetLoad, targetLoad]
  change
    (∑ z : F.Index × Q.Index,
      if (couplingPath F Q hQ z.1 z.2).target = v
      then (if (F.path z.1).target = (Q.path z.2).source
        then F.weight z.1 * Q.weight z.2 else 0)
      else 0) =
    ∑ j : Q.Index,
      if (Q.path j).target = v then Q.weight j else 0
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [show (∑ i : F.Index,
      if (couplingPath F Q hQ i j).target = v
      then (if (F.path i).target = (Q.path j).source
        then F.weight i * Q.weight j else 0)
      else 0) =
      if (Q.path j).target = v then
        (∑ i : F.Index,
          if (F.path i).target = (Q.path j).source
          then F.weight i * Q.weight j else 0)
      else 0 by
        by_cases hv : (Q.path j).target = v
        · simp only [if_pos hv]
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases h : (F.path i).target = (Q.path j).source
          · simp [h, couplingPath_target_of_compatible, hv]
          · simp only [if_neg h]
            split <;> simp
        · simp only [if_neg hv]
          apply Finset.sum_eq_zero
          intro i _hi
          by_cases h : (F.path i).target = (Q.path j).source
          · simp [h, couplingPath_target_of_compatible, hv]
          · simp [h]]
  rw [sum_compatible_left F Q hF j]

theorem couple_isUnitFlow
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hF : F.IsUnitFlow)
    (hQ : Q.IsUnitFlow) :
    (couple F Q hQ.1).IsUnitFlow := by
  constructor
  · intro v hv
    rw [couple_sourceLoad F Q hQ.1 v]
    exact hF.1 v hv
  · intro v hv
    rw [couple_targetLoad F Q hF.2 hQ.1 v]
    exact hQ.2 v hv

theorem couplingPath_edgeSet_subset_of_compatible
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQ : Q.SourceLoadExactlyOne)
    (i : F.Index) (j : Q.Index)
    (h : (F.path i).target = (Q.path j).source) :
    (couplingPath F Q hQ i j).edgeSet ⊆
      (F.path i).edgeSet ∪ (Q.path j).edgeSet := by
  simpa [couplingPath, h] using
    GraphPath.concatErase_edgeSet_subset (F.path i) (Q.path j) h

private theorem couple_edgeTerm_le
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQ : Q.SourceLoadExactlyOne)
    (e : Sym2 V) (i : F.Index) (j : Q.Index) :
    (if e ∈ (couplingPath F Q hQ i j).edgeSet then
        (if (F.path i).target = (Q.path j).source
          then F.weight i * Q.weight j else 0)
      else 0) ≤
      (if e ∈ (F.path i).edgeSet then
          (if (F.path i).target = (Q.path j).source
            then F.weight i * Q.weight j else 0)
        else 0) +
      (if e ∈ (Q.path j).edgeSet then
          (if (F.path i).target = (Q.path j).source
            then F.weight i * Q.weight j else 0)
        else 0) := by
  classical
  by_cases hmatch : (F.path i).target = (Q.path j).source
  · have hnonneg : 0 ≤ F.weight i * Q.weight j :=
      mul_nonneg (F.weight_nonneg i) (Q.weight_nonneg j)
    have hFterm :
        0 ≤ if e ∈ (F.path i).edgeSet
          then F.weight i * Q.weight j else 0 := by
      split <;> simp_all
    have hQterm :
        0 ≤ if e ∈ (Q.path j).edgeSet
          then F.weight i * Q.weight j else 0 := by
      split <;> simp_all
    by_cases he : e ∈ (couplingPath F Q hQ i j).edgeSet
    · have heUnion :
          e ∈ (F.path i).edgeSet ∪ (Q.path j).edgeSet :=
        couplingPath_edgeSet_subset_of_compatible F Q hQ i j hmatch he
      rcases Finset.mem_union.mp heUnion with heF | heQ
      · simp only [if_pos hmatch, if_pos he, if_pos heF]
        exact le_add_of_nonneg_right hQterm
      · simp only [if_pos hmatch, if_pos he, if_pos heQ]
        exact le_add_of_nonneg_left hFterm
    · simp only [if_pos hmatch, if_neg he]
      exact add_nonneg hFterm hQterm
  · simp [hmatch]

private theorem couple_firstEdgeSum
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQ : Q.SourceLoadExactlyOne)
    (e : Sym2 V) :
    (∑ i : F.Index, ∑ j : Q.Index,
      if e ∈ (F.path i).edgeSet then
        (if (F.path i).target = (Q.path j).source
          then F.weight i * Q.weight j else 0)
      else 0) = F.edgeLoad e := by
  classical
  rw [edgeLoad]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases he : e ∈ (F.path i).edgeSet
  · simp only [if_pos he]
    exact sum_compatible_right F Q hQ i
  · simp [he]

private theorem couple_secondEdgeSum
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hF : F.TargetLoadExactlyOne)
    (e : Sym2 V) :
    (∑ i : F.Index, ∑ j : Q.Index,
      if e ∈ (Q.path j).edgeSet then
        (if (F.path i).target = (Q.path j).source
          then F.weight i * Q.weight j else 0)
      else 0) = Q.edgeLoad e := by
  classical
  rw [Finset.sum_comm, edgeLoad]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases he : e ∈ (Q.path j).edgeSet
  · simp only [if_pos he]
    exact sum_compatible_left F Q hF j
  · simp [he]

/-- Edge loads add under product coupling and loop-erased concatenation. -/
theorem couple_edgeLoad_le
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hF : F.TargetLoadExactlyOne)
    (hQ : Q.SourceLoadExactlyOne)
    (e : Sym2 V) :
    (couple F Q hQ).edgeLoad e ≤ F.edgeLoad e + Q.edgeLoad e := by
  classical
  rw [edgeLoad]
  change
    (∑ z : F.Index × Q.Index,
      if e ∈ (couplingPath F Q hQ z.1 z.2).edgeSet then
        (if (F.path z.1).target = (Q.path z.2).source
          then F.weight z.1 * Q.weight z.2 else 0)
      else 0) ≤ F.edgeLoad e + Q.edgeLoad e
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : F.Index, ∑ j : Q.Index,
        if e ∈ (couplingPath F Q hQ i j).edgeSet then
          (if (F.path i).target = (Q.path j).source
            then F.weight i * Q.weight j else 0)
        else 0) ≤
        ∑ i : F.Index, ∑ j : Q.Index,
          ((if e ∈ (F.path i).edgeSet then
              (if (F.path i).target = (Q.path j).source
                then F.weight i * Q.weight j else 0)
            else 0) +
          (if e ∈ (Q.path j).edgeSet then
              (if (F.path i).target = (Q.path j).source
                then F.weight i * Q.weight j else 0)
            else 0)) := by
      exact Finset.sum_le_sum fun i _hi =>
        Finset.sum_le_sum fun j _hj => couple_edgeTerm_le F Q hQ e i j
    _ =
        (∑ i : F.Index, ∑ j : Q.Index,
          if e ∈ (F.path i).edgeSet then
            (if (F.path i).target = (Q.path j).source
              then F.weight i * Q.weight j else 0)
          else 0) +
        (∑ i : F.Index, ∑ j : Q.Index,
          if e ∈ (Q.path j).edgeSet then
            (if (F.path i).target = (Q.path j).source
              then F.weight i * Q.weight j else 0)
          else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = F.edgeLoad e + Q.edgeLoad e := by
      rw [couple_firstEdgeSum F Q hQ e, couple_secondEdgeSum F Q hF e]

/-- Congestion budgets add under product coupling. -/
theorem couple_edgeCongestionAtMost
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    {etaF etaQ : Rat}
    (hFunit : F.TargetLoadExactlyOne)
    (hQunit : Q.SourceLoadExactlyOne)
    (hF : F.EdgeCongestionAtMost etaF)
    (hQ : Q.EdgeCongestionAtMost etaQ) :
    (couple F Q hQunit).EdgeCongestionAtMost (etaF + etaQ) := by
  intro e he
  exact (couple_edgeLoad_le F Q hFunit hQunit e).trans
    (add_le_add (hF e he) (hQ e he))

private theorem concatErase_internallyDisjointFromSet
    (P Q : _root_.SimpleGraph.GraphPath G)
    (hmatch : P.target = Q.source)
    {A : Finset V}
    (hP : P.InternallyDisjointFromSet A)
    (hQ : Q.InternallyDisjointFromSet A)
    (hmiddle : P.target ∉ A) :
    (GraphPath.concatErase P Q hmatch).InternallyDisjointFromSet A := by
  intro v hvPath hvA
  have hvUnion : v ∈ P.vertexSet ∪ Q.vertexSet :=
    GraphPath.concatErase_vertexSet_subset P Q hmatch hvPath
  rcases Finset.mem_union.mp hvUnion with hvP | hvQ
  · rcases hP hvP hvA with hvSource | hvTarget
    · exact Or.inl hvSource
    · exact False.elim (hmiddle (hvTarget ▸ hvA))
  · rcases hQ hvQ hvA with hvSource | hvTarget
    · exact False.elim (hmiddle (hmatch ▸ hvSource ▸ hvA))
    · exact Or.inr hvTarget

/-- Internal avoidance is preserved when the coupled-through terminal set is
disjoint from the forbidden set. -/
theorem couple_internallyDisjointFromSet
    (F : OrientedPathFlow G S T)
    (Q : OrientedPathFlow G T U)
    (hQunit : Q.SourceLoadExactlyOne)
    {A : Finset V}
    (hF : ∀ i, (F.path i).InternallyDisjointFromSet A)
    (hQ : ∀ j, (Q.path j).InternallyDisjointFromSet A)
    (hT : Disjoint T A) :
    ∀ z : (couple F Q hQunit).Index,
      ((couple F Q hQunit).path z).InternallyDisjointFromSet A := by
  intro z
  change (couplingPath F Q hQunit z.1 z.2).InternallyDisjointFromSet A
  classical
  by_cases hmatch : (F.path z.1).target = (Q.path z.2).source
  · simpa [couplingPath, hmatch] using
      concatErase_internallyDisjointFromSet
        (F.path z.1) (Q.path z.2) hmatch
        (hF z.1) (hQ z.2)
        (Finset.disjoint_left.mp hT (F.target_mem z.1))
  · simpa [couplingPath, hmatch] using
      concatErase_internallyDisjointFromSet
        (F.path z.1) (Q.path (couplingFallback F Q hQunit z.1))
        (couplingFallback_spec F Q hQunit z.1)
        (hF z.1) (hQ (couplingFallback F Q hQunit z.1))
        (Finset.disjoint_left.mp hT (F.target_mem z.1))

end OrientedPathFlow
end SimpleGraph
