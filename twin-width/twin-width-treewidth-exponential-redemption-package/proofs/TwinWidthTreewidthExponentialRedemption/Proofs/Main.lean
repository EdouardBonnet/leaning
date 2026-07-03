import TwinWidthTreewidthExponentialRedemption.Statements.Source.TwinWidth.Graph.BonnetDepresLower
import TwinWidthTreewidthExponentialRedemption.Statements.Main

namespace TwinWidthTreewidthExponentialRedemption.Proofs.Main


theorem hasTreeDecompositionWidthAtMost_of_source
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {width : ℕ}
    (D : TwinWidth.SimpleGraph.TreeDecomposition G)
    (hwidth : D.width ≤ width) :
    TwinWidthTreewidthExponentialRedemption.Statements.TreeDecompositionWidth.HasTreeDecompositionWidthAtMost G width := by
  refine ⟨D.Node, D.nodeFintype, D.nodeDecidableEq, D.tree, D.isTree, D.bag,
    D.vertex_mem_bag, ?_, D.bag_indices_connected, ?_⟩
  · intro u v huv
    exact D.edge_mem_bag huv
  · simpa [TwinWidth.SimpleGraph.TreeDecomposition.width] using hwidth

theorem treewidth_le_of_hasTreeDecompositionWidthAtMost
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {width : ℕ}
    (h : TwinWidthTreewidthExponentialRedemption.Statements.TreeDecompositionWidth.HasTreeDecompositionWidthAtMost G width) :
    TwinWidthTreewidthExponentialRedemption.Statements.Treewidth.treewidth G ≤ width := by
  classical
  have hex : ∃ e, TwinWidthTreewidthExponentialRedemption.Statements.TreeDecompositionWidth.HasTreeDecompositionWidthAtMost G e := ⟨width, h⟩
  rw [TwinWidthTreewidthExponentialRedemption.Statements.Treewidth.treewidth, dif_pos hex]
  exact Nat.find_min' hex h

theorem isTrigraphState_of_source {V : Type} [DecidableEq V]
    (T : TwinWidth.TrigraphState V) :
    TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState.IsTrigraphState T.bags T.blackAdj T.redAdj := by
  exact
    ⟨T.bag_nonempty, T.bag_disjoint, T.bag_cover, T.black_symm, T.red_symm,
      T.black_irrefl, T.red_irrefl, T.black_red_disjoint⟩

def sourceTrigraphStateOfSubmitted {V : Type} [DecidableEq V]
    (bags : Finset (Finset V))
    (blackAdj redAdj : Finset V → Finset V → Prop)
    (h : TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState.IsTrigraphState bags blackAdj redAdj) :
    TwinWidth.TrigraphState V where
  bags := bags
  bag_nonempty := h.1
  bag_disjoint := h.2.1
  bag_cover := h.2.2.1
  blackAdj := blackAdj
  redAdj := redAdj
  black_symm := h.2.2.2.1
  red_symm := h.2.2.2.2.1
  black_irrefl := h.2.2.2.2.2.1
  red_irrefl := h.2.2.2.2.2.2.1
  black_red_disjoint := h.2.2.2.2.2.2.2

theorem hasContractionSequenceWidthAtMost_of_source
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (S : TwinWidth.SimpleGraph.ContractionSequence G d) :
    TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth.HasContractionSequenceWidthAtMost G d := by
  refine ⟨S.stepCount, fun i => (S.state i).bags, fun i => (S.state i).blackAdj,
    fun i => (S.state i).redAdj, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact isTrigraphState_of_source (S.state i)
  · rcases S.starts with ⟨hbags, hblack, hred⟩
    refine ⟨?_, hblack, hred⟩
    simpa [TwinWidthTreewidthExponentialRedemption.Statements.SingletonBags.singletonBags, TwinWidth.TrigraphState.singletonBags] using hbags
  · exact S.ends
  · intro i hi
    simpa [TwinWidthTreewidthExponentialRedemption.Statements.ContractionStep.IsContractionStep, TwinWidthTreewidthExponentialRedemption.Statements.ContractedRed.contractedRed,
      TwinWidthTreewidthExponentialRedemption.Statements.ContractedBlack.contractedBlack, TwinWidth.SimpleGraph.IsContractionStep,
      TwinWidth.SimpleGraph.contractedRed, TwinWidth.SimpleGraph.contractedBlack]
      using S.step_contracts i hi
  · intro i hi A hA
    simpa [TwinWidthTreewidthExponentialRedemption.Statements.RedDegree.redDegree, TwinWidth.SimpleGraph.redDegree,
      TwinWidth.TrigraphState.redDegree] using S.redDegree_le i hi hA

theorem source_contractionSequence_of_submitted
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (h : TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth.HasContractionSequenceWidthAtMost G d) :
    TwinWidth.SimpleGraph.HasTwinWidthAtMost G d := by
  rcases h with ⟨stepCount, bags, blackAdj, redAdj, hstates, hstarts, hends, hsteps, hred⟩
  let state : ℕ → TwinWidth.TrigraphState V :=
    fun i => sourceTrigraphStateOfSubmitted (bags i) (blackAdj i) (redAdj i) (hstates i)
  refine ⟨?_⟩
  refine
    { stepCount := stepCount
      state := state
      starts := ?_
      ends := ?_
      step_contracts := ?_
      redDegree_le := ?_ }
  · rcases hstarts with ⟨hbags, hblack, hred0⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [state, sourceTrigraphStateOfSubmitted, TwinWidthTreewidthExponentialRedemption.Statements.SingletonBags.singletonBags,
        TwinWidth.TrigraphState.singletonBags] using hbags
    · intro A B hA hB
      simpa [state, sourceTrigraphStateOfSubmitted] using hblack hA hB
    · intro A B hA hB
      simpa [state, sourceTrigraphStateOfSubmitted] using hred0 hA hB
  · simpa [state, sourceTrigraphStateOfSubmitted] using hends
  · intro i hi
    simpa [state, sourceTrigraphStateOfSubmitted, TwinWidthTreewidthExponentialRedemption.Statements.ContractionStep.IsContractionStep,
      TwinWidthTreewidthExponentialRedemption.Statements.ContractedRed.contractedRed, TwinWidthTreewidthExponentialRedemption.Statements.ContractedBlack.contractedBlack,
      TwinWidth.SimpleGraph.IsContractionStep, TwinWidth.SimpleGraph.contractedRed,
      TwinWidth.SimpleGraph.contractedBlack] using hsteps i hi
  · intro i hi A hA
    simpa [state, sourceTrigraphStateOfSubmitted, TwinWidthTreewidthExponentialRedemption.Statements.RedDegree.redDegree,
      TwinWidth.SimpleGraph.redDegree, TwinWidth.TrigraphState.redDegree] using hred i hi hA

theorem hasContractionSequenceWidthAtMost_mono
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d e : ℕ}
    (h : TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth.HasContractionSequenceWidthAtMost G d) (hde : d ≤ e) :
    TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth.HasContractionSequenceWidthAtMost G e := by
  rcases h with ⟨stepCount, bags, blackAdj, redAdj, hstates, hstarts, hends, hsteps, hred⟩
  refine ⟨stepCount, bags, blackAdj, redAdj, hstates, hstarts, hends, hsteps, ?_⟩
  intro i hi A hA
  exact le_trans (hred i hi hA) hde

theorem hasContractionSequenceWidthAtMost_twinWidth
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hex : ∃ d, TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth.HasContractionSequenceWidthAtMost G d) :
    TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth.HasContractionSequenceWidthAtMost G (TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth.twinWidth G) := by
  classical
  rw [TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth.twinWidth, dif_pos hex]
  exact Nat.find_spec hex

theorem lt_twinWidth_of_not_hasContractionSequenceWidthAtMost
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d : ℕ}
    (hnot : ¬ TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth.HasContractionSequenceWidthAtMost G d)
    (hex : ∃ e, TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth.HasContractionSequenceWidthAtMost G e) :
    d < TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth.twinWidth G := by
  by_contra hle
  exact hnot
    (hasContractionSequenceWidthAtMost_mono
      (hasContractionSequenceWidthAtMost_twinWidth G hex) (Nat.le_of_not_gt hle))

theorem twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      TwinWidthTreewidthExponentialRedemption.Statements.Treewidth.treewidth G ≤ 2 * k + 4 ∧ 2 ^ k < TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth.twinWidth G := by
  refine
    ⟨TwinWidth.SimpleGraph.BonnetDepresVertex k, inferInstance, inferInstance,
      TwinWidth.SimpleGraph.bonnetDepresGraph k, ?_, ?_⟩
  · simpa [
      TwinWidth.SimpleGraph.bonnetDepresApexCount
    ] using treewidth_le_of_hasTreeDecompositionWidthAtMost
      (hasTreeDecompositionWidthAtMost_of_source
        (TwinWidth.SimpleGraph.bonnetDepresTreeDecomposition k)
        (TwinWidth.SimpleGraph.bonnetDepresTreeDecomposition_width_le k))
  · have hsource :
        ¬ TwinWidth.SimpleGraph.HasTwinWidthAtMost
          (TwinWidth.SimpleGraph.bonnetDepresGraph k) (2 ^ k) :=
      TwinWidth.SimpleGraph.BonnetDepres.bonnetDepres_not_hasTwinWidthAtMost_two_pow k
    have hsubmitted :
        ¬ TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth.HasContractionSequenceWidthAtMost
          (TwinWidth.SimpleGraph.bonnetDepresGraph k) (2 ^ k) := by
      intro h
      exact hsource (source_contractionSequence_of_submitted h)
    have hex :
        ∃ e, TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth.HasContractionSequenceWidthAtMost
          (TwinWidth.SimpleGraph.bonnetDepresGraph k) e := by
      refine ⟨Fintype.card (TwinWidth.SimpleGraph.BonnetDepresVertex k), ?_⟩
      exact hasContractionSequenceWidthAtMost_of_source
        (Classical.choice
          (TwinWidth.SimpleGraph.hasTwinWidthAtMost_card
            (TwinWidth.SimpleGraph.bonnetDepresGraph k)))
    exact lt_twinWidth_of_not_hasContractionSequenceWidthAtMost hsubmitted hex

end TwinWidthTreewidthExponentialRedemption.Proofs.Main
