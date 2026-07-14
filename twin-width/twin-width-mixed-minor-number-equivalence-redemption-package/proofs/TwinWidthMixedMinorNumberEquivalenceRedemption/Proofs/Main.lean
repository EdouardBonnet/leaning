import Mathlib.Combinatorics.SimpleGraph.Acyclic
import TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Equivalence.MainContract
import TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Main

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Proofs.Main

open TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth

noncomputable section

def submittedStateOfSource {V : Type} [DecidableEq V]
    (T : TrigraphState V) :
    TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.State V :=
  ⟨T.bags, T.blackAdj, T.redAdj,
    ⟨T.bag_nonempty, T.bag_disjoint, T.bag_cover, T.black_symm, T.red_symm,
      T.black_irrefl, T.red_irrefl, T.black_red_disjoint⟩⟩

def sourceStateOfSubmitted {V : Type} [DecidableEq V]
    (T : TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.State V) :
    TrigraphState V where
  bags := TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags T
  blackAdj := TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.blackAdj T
  redAdj := TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.redAdj T
  bag_nonempty := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.1
  bag_disjoint := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.1
  bag_cover := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.2.1
  black_symm := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.2.2.1
  red_symm := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.2.2.2.1
  black_irrefl := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.2.2.2.2.1
  red_irrefl := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.2.2.2.2.2.1
  black_red_disjoint := by
    rcases T with ⟨bags, blackAdj, redAdj, h⟩
    exact h.down.2.2.2.2.2.2.2

def submittedInitialStateOfSource
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (T : TrigraphState V)
    (h : SimpleGraph.IsInitialState G T) :
    TwinWidthTreewidthExponentialRedemption2.Statements.InitialTrigraphState.InitialState G :=
  ⟨submittedStateOfSource T, ⟨by
    refine ⟨?_, ?_, ?_⟩
    ·
      simpa [submittedStateOfSource,
        TwinWidthTreewidthExponentialRedemption2.Statements.SingletonBags.singletonBags,
        TrigraphState.singletonBags] using h.1
    ·
      intro A B hA hB
      simpa [submittedStateOfSource] using h.2.1 hA hB
    ·
      intro A B hA hB
      simpa [submittedStateOfSource] using h.2.2 hA hB⟩⟩

def submittedFinalStateOfSource {V : Type} [DecidableEq V]
    (T : TrigraphState V)
    (h : SimpleGraph.IsFinalState T) :
    TwinWidthTreewidthExponentialRedemption2.Statements.FinalTrigraphState.FinalState V :=
  ⟨submittedStateOfSource T, ⟨by
    simpa [submittedStateOfSource,
      TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags] using h⟩⟩

def submittedStepOfSource {V : Type} [DecidableEq V]
    {T U : TrigraphState V}
    (h : SimpleGraph.IsContractionStep T U) :
    TwinWidthTreewidthExponentialRedemption2.Statements.ContractionStep.Step
      (submittedStateOfSource T) (submittedStateOfSource U) := by
  classical
  let A : Finset V := Classical.choose h
  have hApack := Classical.choose_spec h
  let B : Finset V := Classical.choose hApack.2
  have hBpack := Classical.choose_spec hApack.2
  have hA : A ∈ T.bags := hApack.1
  have hB : B ∈ T.bags := hBpack.1
  have hAB : A ≠ B := hBpack.2.1
  have hbags : U.bags = insert (A ∪ B) ((T.bags.erase A).erase B) := hBpack.2.2.1
  have hred :
      ∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
        (U.redAdj X Y ↔ SimpleGraph.contractedRed T A B X Y) :=
    hBpack.2.2.2.1
  have hblack :
      ∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
        (U.blackAdj X Y ↔ SimpleGraph.contractedBlack T A B X Y) :=
    hBpack.2.2.2.2
  refine ⟨A, B, ⟨?_, ?_, hAB, ?_, ?_, ?_⟩⟩
  · simpa [submittedStateOfSource] using hA
  · simpa [submittedStateOfSource] using hB
  · simpa [submittedStateOfSource,
      TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags] using hbags
  · intro X Y hX hY
    simpa [submittedStateOfSource,
      TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.redAdj,
      TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.blackAdj,
      TwinWidthTreewidthExponentialRedemption2.Statements.ContractedRed.contractedRed,
      SimpleGraph.contractedRed] using hred hX hY
  · intro X Y hX hY
    simpa [submittedStateOfSource,
      TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.redAdj,
      TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.blackAdj,
      TwinWidthTreewidthExponentialRedemption2.Statements.ContractedRed.contractedRed,
      TwinWidthTreewidthExponentialRedemption2.Statements.ContractedBlack.contractedBlack,
      SimpleGraph.contractedRed, SimpleGraph.contractedBlack] using hblack hX hY

def submittedContractionSequenceOfSource
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (S : SimpleGraph.ContractionSequence G d) :
    TwinWidthTreewidthExponentialRedemption2.Statements.ContractionSequenceWidth.ContractionSequence
      G d :=
  ⟨S.stepCount, fun i => submittedStateOfSource (S.state i),
    submittedInitialStateOfSource (S.state 0) S.starts,
    submittedFinalStateOfSource (S.state S.stepCount) S.ends,
    ⟨rfl⟩, ⟨rfl⟩,
    (fun i hi => submittedStepOfSource (S.step_contracts i hi)),
    ⟨by
      intro i hi A hA
      simpa [submittedStateOfSource,
        TwinWidthTreewidthExponentialRedemption2.Statements.RedDegree.redDegree,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.redAdj,
        SimpleGraph.redDegree, TrigraphState.redDegree]
        using S.redDegree_le i hi hA⟩⟩

theorem source_contractionSequence_of_submitted
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (h : Nonempty
      (TwinWidthTreewidthExponentialRedemption2.Statements.ContractionSequenceWidth.ContractionSequence
        G d)) :
    SimpleGraph.HasTwinWidthAtMost G d := by
  rcases h with ⟨S⟩
  rcases S with ⟨stepCount, state, start, final, hstart, hfinal, hsteps, hred⟩
  let sourceState : ℕ → TrigraphState V :=
    fun i => sourceStateOfSubmitted (state i)
  refine ⟨?_⟩
  refine
    { stepCount := stepCount
      state := sourceState
      starts := ?_
      ends := ?_
      step_contracts := ?_
      redDegree_le := ?_ }
  · change SimpleGraph.IsInitialState G
      (sourceStateOfSubmitted (state 0))
    rw [hstart.down]
    have hstartProp := start.2.down
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceState, sourceStateOfSubmitted,
        TwinWidthTreewidthExponentialRedemption2.Statements.SingletonBags.singletonBags,
        TrigraphState.singletonBags] using hstartProp.1
    · intro A B hA hB
      simpa [sourceState, sourceStateOfSubmitted,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.blackAdj]
        using hstartProp.2.1 hA hB
    · intro A B hA hB
      simpa [sourceState, sourceStateOfSubmitted,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.redAdj]
        using hstartProp.2.2 hA hB
  · change SimpleGraph.IsFinalState
      (sourceStateOfSubmitted (state stepCount))
    rw [hfinal.down]
    simpa [sourceState, sourceStateOfSubmitted,
      TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags]
      using final.2.down
  · intro i hi
    rcases hsteps i hi with ⟨A, B, hstepLift⟩
    rcases hstepLift.down with ⟨hA, hB, hAB, hbags, hredStep, hblackStep⟩
    refine ⟨A, ?_, B, ?_, hAB, ?_, ?_, ?_⟩
    · simpa [sourceState, sourceStateOfSubmitted,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags] using hA
    · simpa [sourceState, sourceStateOfSubmitted,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags] using hB
    · simpa [sourceState, sourceStateOfSubmitted,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags] using hbags
    · intro X Y hX hY
      simpa [sourceState, sourceStateOfSubmitted,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.redAdj,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.blackAdj,
        TwinWidthTreewidthExponentialRedemption2.Statements.ContractedRed.contractedRed,
        SimpleGraph.contractedRed] using hredStep hX hY
    · intro X Y hX hY
      simpa [sourceState, sourceStateOfSubmitted,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.redAdj,
        TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.blackAdj,
        TwinWidthTreewidthExponentialRedemption2.Statements.ContractedRed.contractedRed,
        TwinWidthTreewidthExponentialRedemption2.Statements.ContractedBlack.contractedBlack,
        SimpleGraph.contractedRed, SimpleGraph.contractedBlack] using hblackStep hX hY
  · intro i hi A hA
    simpa [sourceState, sourceStateOfSubmitted,
      TwinWidthTreewidthExponentialRedemption2.Statements.RedDegree.redDegree,
      TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.bags,
      TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState.redAdj,
      SimpleGraph.redDegree, TrigraphState.redDegree]
      using hred.down i hi hA

theorem submitted_twinWidth_le_of_contractionSequence
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (h : Nonempty
      (TwinWidthTreewidthExponentialRedemption2.Statements.ContractionSequenceWidth.ContractionSequence
        G d)) :
    TwinWidthTreewidthExponentialRedemption2.Statements.TwinWidth.twinWidth G ≤ d := by
  classical
  let P : ℕ → Prop := fun e =>
    Nonempty
      (TwinWidthTreewidthExponentialRedemption2.Statements.ContractionSequenceWidth.ContractionSequence
        G e)
  have hex : ∃ e, P e := ⟨d, h⟩
  change TwinWidthTreewidthExponentialRedemption2.Statements.LeastNatural.leastNat P ≤ d
  rw [TwinWidthTreewidthExponentialRedemption2.Statements.LeastNatural.leastNat, dif_pos hex]
  exact Nat.find_min' hex h

theorem submitted_contractionSequence_twinWidth
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hex : ∃ d,
      Nonempty
        (TwinWidthTreewidthExponentialRedemption2.Statements.ContractionSequenceWidth.ContractionSequence
          G d)) :
    Nonempty
      (TwinWidthTreewidthExponentialRedemption2.Statements.ContractionSequenceWidth.ContractionSequence
        G (TwinWidthTreewidthExponentialRedemption2.Statements.TwinWidth.twinWidth G)) := by
  classical
  rw [TwinWidthTreewidthExponentialRedemption2.Statements.TwinWidth.twinWidth,
    TwinWidthTreewidthExponentialRedemption2.Statements.LeastNatural.leastNat, dif_pos hex]
  exact Nat.find_spec hex

theorem source_twinWidth_eq_submitted_twinWidth
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    SimpleGraph.twinWidth G =
      TwinWidthTreewidthExponentialRedemption2.Statements.TwinWidth.twinWidth G := by
  apply le_antisymm
  · have hexSubmitted :
        ∃ d,
          Nonempty
            (TwinWidthTreewidthExponentialRedemption2.Statements.ContractionSequenceWidth.ContractionSequence
              G d) := by
      let S : SimpleGraph.ContractionSequence G (Fintype.card V) :=
        Classical.choice (SimpleGraph.hasTwinWidthAtMost_card G)
      exact ⟨Fintype.card V, ⟨submittedContractionSequenceOfSource S⟩⟩
    exact SimpleGraph.twinWidth_le_of_hasTwinWidthAtMost
      (source_contractionSequence_of_submitted
        (submitted_contractionSequence_twinWidth G hexSubmitted))
  · let S : SimpleGraph.ContractionSequence G (SimpleGraph.twinWidth G) :=
      Classical.choice (SimpleGraph.hasTwinWidthAtMost_twinWidth' G)
    exact submitted_twinWidth_le_of_contractionSequence
      ⟨submittedContractionSequenceOfSource S⟩

def sourceDivisionOfSubmitted
    {n k : ℕ}
    (D : TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.IntervalDivision.Division n k) :
    Division n k where
  part := TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.IntervalDivision.part D
  part_nonempty := D.property.1
  part_disjoint := D.property.2.1
  part_cover := D.property.2.2.1
  part_convex := D.property.2.2.2.1
  part_ordered := D.property.2.2.2.2

def submittedDivisionOfSource {n k : ℕ} (D : Division n k) :
    TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.IntervalDivision.Division n k :=
  ⟨D.part, D.part_nonempty, D.part_disjoint, D.part_cover, D.part_convex,
    D.part_ordered⟩

theorem source_hasMixedMinor_of_submitted
    {α : Type*} {n m k : ℕ} {M : _root_.Matrix (Fin n) (Fin m) α} :
    TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedMinor.HasMixedMinor M k →
      Matrix.HasMixedMinor M k := by
  intro h
  rcases h with hzero | hminor
  · exact Or.inl hzero
  · rcases hminor with ⟨R, C, hcells⟩
    refine Or.inr ⟨sourceDivisionOfSubmitted R, sourceDivisionOfSubmitted C, ?_⟩
    intro i j
    simpa [
      sourceDivisionOfSubmitted,
      TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedCell.Mixed,
      TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.Cell.Vertical,
      TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.Cell.Horizontal,
      Matrix.CellMixed, Matrix.CellVertical, Matrix.CellHorizontal] using hcells i j

theorem submitted_hasMixedMinor_of_source
    {α : Type*} {n m k : ℕ} {M : _root_.Matrix (Fin n) (Fin m) α} :
    Matrix.HasMixedMinor M k →
      TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedMinor.HasMixedMinor M k := by
  intro h
  rcases h with hzero | hminor
  · exact Or.inl hzero
  · rcases hminor with ⟨R, C, hcells⟩
    refine Or.inr ⟨submittedDivisionOfSource R, submittedDivisionOfSource C, ?_⟩
    intro i j
    simpa [
      submittedDivisionOfSource,
      TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedCell.Mixed,
      TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.Cell.Vertical,
      TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.Cell.Horizontal,
      Matrix.CellMixed, Matrix.CellVertical, Matrix.CellHorizontal] using hcells i j

theorem submitted_mixedNumber_eq_source
    {α : Type*} {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) :
    TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedNumber.matrixMixedNumber M =
      Matrix.matrixMixedNumber M := by
  classical
  apply le_antisymm
  · unfold TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedNumber.matrixMixedNumber
      Matrix.matrixMixedNumber
    refine csSup_le (s :=
      { k : ℕ | k ≤ min n m ∧
        TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedMinor.HasMixedMinor M k })
      ?_ ?_
    · exact ⟨0, ⟨Nat.zero_le (min n m), Or.inl rfl⟩⟩
    intro k hk
    exact Nat.le_findGreatest hk.1
      (source_hasMixedMinor_of_submitted (M := M) hk.2)
  · unfold TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedNumber.matrixMixedNumber
      Matrix.matrixMixedNumber
    refine le_csSup (s :=
      { k : ℕ | k ≤ min n m ∧
        TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedMinor.HasMixedMinor M k })
      ?_ ?_
    · exact ⟨min n m, by
        intro k hk
        exact hk.1⟩
    exact ⟨Nat.findGreatest_le (P := Matrix.HasMixedMinor M) (min n m),
      submitted_hasMixedMinor_of_source (M := M)
        (Nat.findGreatest_spec (P := Matrix.HasMixedMinor M)
          (Nat.zero_le (min n m)) (Matrix.hasMixedMinor_zero M))⟩

def sourceVertexOrderOfSubmitted {V : Type*} {n : ℕ}
    (σ : TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.VertexOrder.Order V n) :
    VertexOrder V n :=
  ⟨σ⟩

def submittedVertexOrderOfSource {V : Type*} {n : ℕ} (σ : VertexOrder V n) :
    TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.VertexOrder.Order V n :=
  σ.equiv

theorem submitted_orderedAdjacency_eq_source
    {V : Type*} {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.VertexOrder.Order V n) :
    TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacency.orderedAdjacency
        G σ =
      Matrix.orderedAdjacency G (sourceVertexOrderOfSubmitted σ) := by
  funext i j
  by_cases h : G.Adj ((show Fin n ≃ V from σ) i) ((show Fin n ≃ V from σ) j)
  · simp [
      TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacency.orderedAdjacency,
      Matrix.orderedAdjacency, sourceVertexOrderOfSubmitted, h]
  · simp [
      TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacency.orderedAdjacency,
      Matrix.orderedAdjacency, sourceVertexOrderOfSubmitted, h]

theorem submitted_orderedMixedNumber_eq_source_of_submitted
    {V : Type*} {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.VertexOrder.Order V n) :
    TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacencyMixedNumber.orderedAdjacencyMixedNumber
        G σ =
      Matrix.orderedAdjacencyMixedNumber G (sourceVertexOrderOfSubmitted σ) := by
  unfold TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacencyMixedNumber.orderedAdjacencyMixedNumber
    Matrix.orderedAdjacencyMixedNumber
  rw [submitted_mixedNumber_eq_source]
  rw [submitted_orderedAdjacency_eq_source]

theorem submitted_orderedMixedNumber_eq_source_of_source
    {V : Type*} {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : VertexOrder V n) :
    TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacencyMixedNumber.orderedAdjacencyMixedNumber
        G (submittedVertexOrderOfSource σ) =
      Matrix.orderedAdjacencyMixedNumber G σ := by
  unfold TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacencyMixedNumber.orderedAdjacencyMixedNumber
    Matrix.orderedAdjacencyMixedNumber
  rw [submitted_mixedNumber_eq_source]
  rw [submitted_orderedAdjacency_eq_source]
  rfl

theorem submitted_mixedMinorNumber_eq_source
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.SimpleGraph.mixedMinorNumber G =
      SimpleGraph.mixedMinorNumber G := by
  classical
  let S : Set ℕ := { k : ℕ |
    ∃ σ : TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.VertexOrder.Order
        V (Fintype.card V),
      TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacencyMixedNumber.orderedAdjacencyMixedNumber
        G σ = k }
  have hS : S.Nonempty := by
    refine ⟨
      TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacencyMixedNumber.orderedAdjacencyMixedNumber
        G ((Fintype.equivFin V).symm), ?_⟩
    exact ⟨(Fintype.equivFin V).symm, rfl⟩
  apply le_antisymm
  · rcases SimpleGraph.exists_order_mixedNumber_eq_mixedMinorNumber G with ⟨σ, hσ⟩
    have hvalue :
        TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacencyMixedNumber.orderedAdjacencyMixedNumber
            G (submittedVertexOrderOfSource σ) =
          SimpleGraph.mixedMinorNumber G := by
      simpa [hσ] using submitted_orderedMixedNumber_eq_source_of_source G σ
    unfold TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.SimpleGraph.mixedMinorNumber
    simpa [S] using
      (Nat.sInf_le (show SimpleGraph.mixedMinorNumber G ∈ S from
        ⟨submittedVertexOrderOfSource σ, hvalue⟩))
  · have hspec :
        ∃ σ : TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.VertexOrder.Order
            V (Fintype.card V),
          TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacencyMixedNumber.orderedAdjacencyMixedNumber
              G σ =
            TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.SimpleGraph.mixedMinorNumber G := by
      unfold TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.SimpleGraph.mixedMinorNumber
      simpa [S] using (Nat.sInf_mem hS)
    rcases hspec with ⟨σ, hσ⟩
    have hvalue :
        Matrix.orderedAdjacencyMixedNumber G (sourceVertexOrderOfSubmitted σ) =
          TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.SimpleGraph.mixedMinorNumber G := by
      rw [← submitted_orderedMixedNumber_eq_source_of_submitted G σ, hσ]
    unfold SimpleGraph.mixedMinorNumber
    exact Nat.find_min' _ ⟨sourceVertexOrderOfSubmitted σ, hvalue⟩

theorem functionalEquivalence :
    TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.FunctionalEquivalence.FunctionallyEquivalent
      (fun {V : Type} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] =>
        TwinWidthTreewidthExponentialRedemption2.Statements.TwinWidth.twinWidth G)
      (fun {V : Type} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] =>
        TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.SimpleGraph.mixedMinorNumber G) := by
  rcases MainContract.twin_width_functionally_equivalent_mixed_minor_number with
    ⟨hTwinToMixed, hMixedToTwin⟩
  constructor
  · rcases hTwinToMixed with ⟨f, hf⟩
    refine ⟨f, ?_⟩
    intro V _ _ G _
    have htww := source_twinWidth_eq_submitted_twinWidth G
    have hmix := submitted_mixedMinorNumber_eq_source G
    simpa [htww, hmix] using hf G
  · rcases hMixedToTwin with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    intro V _ _ G _
    have htww := source_twinWidth_eq_submitted_twinWidth G
    have hmix := submitted_mixedMinorNumber_eq_source G
    simpa [htww, hmix] using hg G

end

end TwinWidthMixedMinorNumberEquivalenceRedemption.Proofs.Main
