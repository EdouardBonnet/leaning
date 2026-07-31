import «statements-and-proofs».Exponent7.CutResponder.FractionalMatchingPeeling
import «statements-and-proofs».GridMinorArithmetic

/-!
# A logarithmic bound for constant-fraction matching peeling

`FractionalMatchingPeeling` constructs an exact matching but records only the
elementary linear bound on the number of batches.  This file retains the size
of every batch and proves the quantitative estimate needed by the fresh-cluster
consumer:

```
batchCount ≤ responseConstant * (Nat.log 2 initialCardinality + 1).
```

The proof is division-free at the responder interface.  A block of
`responseConstant` consecutive batches removes at least half of the currently
unmatched side.  Strong induction on that cardinality then gives the logarithmic
bound.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- The numerical trace of a legal constant-fraction peeling.  At a state of
size `n`, the next batch has size `k`, satisfies `n ≤ c*k`, and leaves the
state of size `n-k`. -/
inductive FractionalPeelingProfile (c : ℕ) : ℕ → List ℕ → Prop
  | nil : FractionalPeelingProfile c 0 []
  | cons {n k : ℕ} {ks : List ℕ}
      (k_pos : 0 < k)
      (k_le : k ≤ n)
      (fraction : n ≤ c * k)
      (tail : FractionalPeelingProfile c (n - k) ks) :
      FractionalPeelingProfile c n (k :: ks)

namespace FractionalPeelingProfile

variable {c n : ℕ} {ks : List ℕ}

/-- A peeling profile partitions its initial cardinality into its batch
sizes. -/
theorem sum_eq
    (h : FractionalPeelingProfile c n ks) :
    ks.sum = n := by
  induction h with
  | nil =>
      simp
  | @cons n k ks hkpos hkle hfraction htail ih =>
      simp only [List.sum_cons, ih]
      omega

/-- A nonempty profile starts from a positive cardinality. -/
theorem card_pos_of_ne_nil
    (h : FractionalPeelingProfile c n ks)
    (hks : ks ≠ []) :
    0 < n := by
  cases h with
  | nil =>
      exact False.elim (hks rfl)
  | cons hkpos _ _ _ =>
      omega

/-- After `t` batches, write the initial cardinality as the consumed prefix
plus the residual cardinality.  The final inequality is the summed
constant-fraction estimate for that prefix. -/
theorem exists_drop_profile_and_prefix_bound
    (h : FractionalPeelingProfile c n ks)
    (t : ℕ) (ht : t ≤ ks.length) :
    ∃ r : ℕ,
      FractionalPeelingProfile c r (ks.drop t) ∧
      n = (ks.take t).sum + r ∧
      t * r ≤ c * (ks.take t).sum := by
  induction t generalizing n ks with
  | zero =>
      refine ⟨n, ?_, ?_, ?_⟩
      · simpa using h
      · simp
      · simp
  | succ t ih =>
      cases h with
      | nil =>
          simp at ht
      | @cons n k ks hkpos hkle hfraction htail =>
          have ht' : t ≤ ks.length := by
            simpa using ht
          rcases ih htail ht' with
            ⟨r, hrProfile, hrDecomp, hrBound⟩
          refine ⟨r, ?_, ?_, ?_⟩
          · simpa using hrProfile
          · simp only [List.take_succ_cons, List.sum_cons]
            have hnSplit : n = k + (n - k) := by
              omega
            calc
              n = k + (n - k) := hnSplit
              _ = k + ((ks.take t).sum + r) := by rw [hrDecomp]
              _ = k + (ks.take t).sum + r := by omega
          · simp only [List.take_succ_cons, List.sum_cons]
            have hrle : r ≤ c * k := by
              have hrleResidual : r ≤ n - k := by
                rw [hrDecomp]
                omega
              exact hrleResidual.trans (Nat.sub_le n k) |>.trans hfraction
            calc
              (t + 1) * r = t * r + r := by ring
              _ ≤ c * (ks.take t).sum + c * k :=
                Nat.add_le_add hrBound hrle
              _ = c * (k + (ks.take t).sum) := by ring

/-- Any full block of `c` legal batches leaves at most half of the cardinality
present at the start of the block. -/
theorem two_mul_drop_card_le
    (h : FractionalPeelingProfile c n ks)
    (hc : 0 < c)
    (hlen : c ≤ ks.length) :
    ∃ r : ℕ,
      FractionalPeelingProfile c r (ks.drop c) ∧
      n = (ks.take c).sum + r ∧
      2 * r ≤ n := by
  rcases h.exists_drop_profile_and_prefix_bound c hlen with
    ⟨r, hrProfile, hrDecomp, hrBound⟩
  have hrle :
      r ≤ (ks.take c).sum :=
    Nat.le_of_mul_le_mul_left hrBound hc
  refine ⟨r, hrProfile, hrDecomp, ?_⟩
  omega

/-- The number of constant-fraction batches is logarithmic in the initial
cardinality. -/
theorem length_le_mul_log_succ
    (h : FractionalPeelingProfile c n ks)
    (hc : 0 < c) :
    ks.length ≤ c * (Nat.log 2 n + 1) := by
  induction n using Nat.strong_induction_on generalizing ks with
  | h n ih =>
      by_cases hshort : ks.length ≤ c
      · exact hshort.trans
          (Nat.le_mul_of_pos_right c (Nat.succ_pos (Nat.log 2 n)))
      · have hclen : c ≤ ks.length := by omega
        rcases h.two_mul_drop_card_le hc hclen with
          ⟨r, hrProfile, hrDecomp, hrHalf⟩
        have hdropLenPos : 0 < (ks.drop c).length := by
          rw [List.length_drop]
          omega
        have hdropNe : ks.drop c ≠ [] := by
          intro hnil
          simp [hnil] at hdropLenPos
        have hrPos : 0 < r :=
          hrProfile.card_pos_of_ne_nil hdropNe
        have hrLt : r < n := by
          omega
        have htail :=
          ih r hrLt hrProfile
        have hrDiv : r ≤ n / 2 := by
          rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
          simpa [Nat.mul_comm] using hrHalf
        have hlogDiv :
            Nat.log 2 r ≤ Nat.log 2 (n / 2) :=
          Nat.log_mono_right hrDiv
        rw [Nat.log_div_base] at hlogDiv
        have hnTwo : 2 ≤ n := by omega
        have hnLogPos : 0 < Nat.log 2 n :=
          Nat.log_pos (by decide : 1 < 2) hnTwo
        have hlog :
            Nat.log 2 r + 1 ≤ Nat.log 2 n := by
          omega
        have hlenSplit :
            ks.length = c + (ks.drop c).length := by
          rw [List.length_drop]
          omega
        calc
          ks.length = c + (ks.drop c).length := hlenSplit
          _ ≤ c + c * (Nat.log 2 r + 1) :=
            Nat.add_le_add_left htail c
          _ ≤ c + c * Nat.log 2 n :=
            Nat.add_le_add_left (Nat.mul_le_mul_left c hlog) c
          _ = c * (Nat.log 2 n + 1) := by ring

end FractionalPeelingProfile

/-- A possibly unfinished peeling trace.  The final parameter is the
cardinality still unmatched after the listed batches. -/
inductive FractionalPeelingPrefixProfile
    (c : ℕ) : ℕ → List ℕ → ℕ → Prop
  | nil (n : ℕ) :
      FractionalPeelingPrefixProfile c n [] n
  | cons {n k r : ℕ} {ks : List ℕ}
      (k_pos : 0 < k)
      (k_le : k ≤ n)
      (fraction : n ≤ c * k)
      (tail :
        FractionalPeelingPrefixProfile c (n - k) ks r) :
      FractionalPeelingPrefixProfile c n (k :: ks) r

namespace FractionalPeelingPrefixProfile

variable {c n r : ℕ} {ks : List ℕ}

/-- A positive unfinished residual can be consumed as one final batch. -/
theorem complete
    (h : FractionalPeelingPrefixProfile c n ks r)
    (hc : 0 < c) (hr : 0 < r) :
    FractionalPeelingProfile c n (ks ++ [r]) := by
  induction h with
  | nil n =>
      simp only [List.nil_append]
      exact FractionalPeelingProfile.cons hr le_rfl
        (by
          have : n ≤ c * n :=
            Nat.le_mul_of_pos_left n hc
          simpa using this)
        (by simpa using
          (FractionalPeelingProfile.nil (c := c)))
  | @cons n k r ks hkpos hkle hfraction htail ih =>
      exact
        FractionalPeelingProfile.cons
          hkpos hkle hfraction (ih hr)

/-- No legal unfinished prefix can already use the full logarithmic budget:
one more batch consuming its positive residual would contradict the complete
profile bound. -/
theorem length_lt_mul_log_succ
    (h : FractionalPeelingPrefixProfile c n ks r)
    (hc : 0 < c) (hr : 0 < r) :
    ks.length < c * (Nat.log 2 n + 1) := by
  have hcomplete := h.complete hc hr
  have hbound := hcomplete.length_le_mul_log_succ hc
  simpa using hbound

end FractionalPeelingPrefixProfile

/-- An exact peeled matching together with the numerical trace of all batches
used to construct it. -/
structure ProfiledPeeledMatching
    (U W : Finset X) (responseConstant : ℕ)
    extends PeeledMatching U W where
  batchSizes : List ℕ
  profile :
    FractionalPeelingProfile responseConstant U.card batchSizes
  batchCount_eq : batchCount = batchSizes.length

namespace ProfiledPeeledMatching

instance {U W : Finset X} {c : ℕ}
    (M : ProfiledPeeledMatching U W c) : Fintype M.Edge :=
  M.edgeFintype

instance {U W : Finset X} {c : ℕ}
    (M : ProfiledPeeledMatching U W c) : DecidableEq M.Edge :=
  M.edgeDecidableEq

/-- Empty sides give the empty profiled matching. -/
noncomputable def empty
    {U W : Finset X} {c : ℕ}
    (hU : U = ∅) (hW : W = ∅) :
    ProfiledPeeledMatching U W c := by
  classical
  let M := PeeledMatching.empty hU hW
  exact
    { M with
      batchSizes := []
      profile := by
        simpa [hU] using (FractionalPeelingProfile.nil (c := c))
      batchCount_eq := by
        simp [M, PeeledMatching.empty, hU] }

/-- Prepend one legal batch to a profiled matching of the residual sides. -/
noncomputable def cons
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c)
    (hU : U.Nonempty)
    (M : ProfiledPeeledMatching
      K.residualLeft K.residualRight c) :
    ProfiledPeeledMatching U W c := by
  classical
  let P := PeeledMatching.cons K M.toPeeledMatching
  have hkPos :
      0 < Fintype.card K.Edge :=
    K.edge_card_pos hU
  have hkLe :
      Fintype.card K.Edge ≤ U.card := by
    calc
      Fintype.card K.Edge = K.leftSet.card :=
        K.leftSet_card.symm
      _ ≤ U.card := Finset.card_le_card K.leftSet_subset
  have hres :
      U.card - Fintype.card K.Edge =
        K.residualLeft.card := by
    rw [FractionalMatchingBatch.residualLeft,
      Finset.card_sdiff_of_subset K.leftSet_subset,
      K.leftSet_card]
  have htail :
      FractionalPeelingProfile c
        (U.card - Fintype.card K.Edge) M.batchSizes := by
    rw [hres]
    exact M.profile
  exact
    { P with
      batchSizes := Fintype.card K.Edge :: M.batchSizes
      profile :=
        FractionalPeelingProfile.cons
          hkPos hkLe K.fraction htail
      batchCount_eq := by
        dsimp [P, PeeledMatching.cons]
        simp [M.batchCount_eq] }

end ProfiledPeeledMatching

/-- Strong induction constructs an exact matching while retaining its full
constant-fraction profile. -/
theorem exists_profiledPeeledMatching
    {responseConstant : ℕ}
    (respond : FractionalBatchResponder
      (X := X) responseConstant)
    (U W : Finset X)
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card) :
    Nonempty (ProfiledPeeledMatching U W responseConstant) := by
  classical
  induction hn : U.card using Nat.strong_induction_on generalizing U W with
  | h n ih =>
      subst hn
      by_cases hUempty : U = ∅
      · have hWcard : W.card = 0 := by
          simpa [hUempty] using hcard.symm
        have hWempty : W = ∅ := Finset.card_eq_zero.mp hWcard
        exact ⟨ProfiledPeeledMatching.empty hUempty hWempty⟩
      · have hUne : U.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hUempty
        rcases respond U W hdisjoint hcard hUne with ⟨K⟩
        have hlt : K.residualLeft.card < U.card :=
          K.residualLeft_card_lt hUne
        rcases ih K.residualLeft.card hlt
            K.residualLeft K.residualRight
            (FractionalMatchingBatch.residual_disjoint K hdisjoint)
            (FractionalMatchingBatch.residual_card_eq K hcard) rfl with
          ⟨M⟩
        exact ⟨ProfiledPeeledMatching.cons K hUne M⟩

/-- Quantitative exact-matching output: a constant-fraction responder needs
only `c * (log₂ |U| + 1)` fresh batches. -/
theorem exists_profiledPeeledMatching_with_log_bound
    {responseConstant : ℕ}
    (respond : FractionalBatchResponder
      (X := X) responseConstant)
    (hc : 0 < responseConstant)
    (U W : Finset X)
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card) :
    ∃ M : ProfiledPeeledMatching U W responseConstant,
      M.batchCount ≤
        responseConstant * (Nat.log 2 U.card + 1) := by
  rcases
      exists_profiledPeeledMatching
        respond U W hdisjoint hcard with
    ⟨M⟩
  refine ⟨M, ?_⟩
  rw [M.batchCount_eq]
  exact M.profile.length_le_mul_log_succ hc

end CutResponder
end Exponent7
end SimpleGraph
