import Chapter02.cycle_packing_short_cycle_aux
import Chapter02.cycle_packing_small_k_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

/--
An abstract way to record that every cycle packing in `H` can be lifted to a
cycle packing in `G`.  The suppression construction in Diestel's proof will
eventually instantiate this for the cubic kernel of `G - C`.
-/
def CyclePackingTransfer {V' : Type u} {E' : Type v}
    (H : MultiGraph V' E') (G : MultiGraph V E) : Prop :=
  ∀ k : ℕ, H.HasKDisjointCycles k → G.HasKDisjointCycles k

/--
The exact reduction needed for the induction step of Lemma 2.3.1: after
choosing a cycle `C`, the deleted graph contains, up to cycle-packing
transfer, a sufficiently large cubic multigraph.
-/
def HasCyclePackingReduction (G : MultiGraph V E) [Finite V] [Finite E]
    (k : ℕ) : Prop :=
  ∃ C : G.CycleIn, ∃ V' : Type u, ∃ E' : Type v,
    ∃ hfinV' : Finite V', ∃ hfinE' : Finite E',
    ∃ H : MultiGraph V' E',
      @IsCubic V' E' H hfinE' ∧
        erdosPosaS (k - 1) < (H.vertexSet.ncard : ℝ) ∧
          CyclePackingTransfer H (G.deleteVerts C.support)

private theorem lemma_2_3_1_from_reduction_aux :
    ∀ k : ℕ,
      (∀ l < k, ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
        [Finite V] [Finite E],
          G.IsCubic →
            erdosPosaS l < (G.vertexSet.ncard : ℝ) →
              G.HasKDisjointCycles l) →
        ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
          [Finite V] [Finite E],
          (2 ≤ k → G.IsCubic →
            erdosPosaS k < (G.vertexSet.ncard : ℝ) →
              HasCyclePackingReduction G k) →
            G.IsCubic →
              erdosPosaS k < (G.vertexSet.ncard : ℝ) →
                G.HasKDisjointCycles k := by
  intro k ih V E G _ _ hreduce hCubic hLarge
  by_cases hsmall : k ≤ 1
  · exact lemma_2_3_1_small_k G k hsmall hCubic hLarge
  · have hk : 2 ≤ k := by omega
    obtain ⟨C, V', E', hfinV', hfinE', H, hHCubic, hHLarge, htransfer⟩ :=
      hreduce hk hCubic hLarge
    haveI : Finite V' := hfinV'
    haveI : Finite E' := hfinE'
    have hkpred_lt : k - 1 < k := by omega
    have hHpack : H.HasKDisjointCycles (k - 1) :=
      ih (k - 1) hkpred_lt H hHCubic hHLarge
    have hDeletePack : HasKDisjointCycles (G.deleteVerts C.support) (k - 1) :=
      htransfer (k - 1) hHpack
    have hSuccPack : G.HasKDisjointCycles ((k - 1) + 1) :=
      hasKDisjointCycles_succ_of_deleteVerts (G := G) C hDeletePack
    have hk_eq : (k - 1) + 1 = k := by omega
    simpa [hk_eq] using hSuccPack

/--
Strong-induction wrapper for the abstract reduction.  This is the formal
induction skeleton of Diestel's proof of Lemma 2.3.1.
-/
theorem lemma_2_3_1_from_reductions
    (hreduce : ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E] (k : ℕ),
        2 ≤ k →
          G.IsCubic →
            erdosPosaS k < (G.vertexSet.ncard : ℝ) →
              HasCyclePackingReduction G k) :
    ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E] (k : ℕ),
      G.IsCubic →
        erdosPosaS k < (G.vertexSet.ncard : ℝ) →
          G.HasKDisjointCycles k := by
  intro V E G _ _ k
  exact Nat.strong_induction_on k
    (p := fun k => ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E],
      G.IsCubic →
        erdosPosaS k < (G.vertexSet.ncard : ℝ) →
          G.HasKDisjointCycles k)
    (fun k ih => by
    intro V E G _ _ hCubic hLarge
    exact lemma_2_3_1_from_reduction_aux k ih G
      (fun hk => hreduce G k hk) hCubic hLarge) G

end MultiGraph

end Chapter02
end Diestel
