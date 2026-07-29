import «statements-and-proofs».Exponent8.Claim53Strong
import «statements-and-proofs».Exponent8.Lemma48Additive

/-!
# Three-round recursive slicing interface

This experimental module isolates the proposed exponent-eight-and-a-half
refinement of Chuzhoy--Tan Section 5.  It is deliberately not imported by the
degree-ten endpoint.

The source proof performs one re-slicing round.  Here the initial slicing has
about `g^2 * sqrt(g)` slices and is followed by three rounds, each with
fanout `ceil(sqrt(g))`.  A majority of large-row slices exits to the
Section 4.4--4.5 assembly; otherwise at least half of the slices can be
refined.  Three refinements recover about `g^4` final slices.

All numerical costs are division-free.  In particular, a refinement from
width `w` to width `wNext`, through a small row family of size at most
`rowCap`, consumes

`fanout * wNext + (fanout + 1) * rowCap`

paths in Theorem 4.6.  Lemma 4.8 first retains half of the slice paths, and
the strengthened Claim 5.3 then loses at most `4 * g^4`; this explains the
three `refineBudget` fields below.

The only project axiom in this file is `threeRoundRecursiveSlicing`.  It
records the genuinely future proof: Observation 5.4 for each cleaned slice,
composition of the local cut systems, and propagation of the localization
certificate through three rounds.  The additive Lemma 4.8 cleanup used in
its input and output is proved below.
-/

namespace SimpleGraph
namespace Exponent8

universe u v

/-- The explicit local terminal threshold targeted by this experiment.

The internal fanout is `Nat.sqrt g + 1`, which is a ceiling surrogate valid
also when the exponent of the paper's power-of-two parameter is odd.  For
`2 <= g`, this is at most `2 * Nat.sqrt g`, so its constant factor is absorbed
in `C`; the external threshold can retain the literal `Nat.sqrt g` shown
here. -/
def exponentEightLocalThreshold
    (C logExp g : ℕ) : ℕ :=
  C * g ^ 8 * Nat.sqrt g * (Nat.log 2 g + 1) ^ logExp

/-- Exact arithmetic data for the initial slicing and three recursive
re-slicing rounds.

`m0,...,m3` are the available slice counts, `w0,...,w3` their widths, and
`cap0,...,cap2` the row-cardinality thresholds distinguishing the
large-slice exit from the small-slice refinement. -/
structure ThreeRoundParameters (g N Dhat : ℕ) where
  /-- Constant and logarithmic exponent in the advertised local threshold. -/
  C : ℕ
  logExp : ℕ
  /-- Fanout of each of the three recursive re-slicing rounds. -/
  fanout : ℕ
  /-- Slice counts at depths zero through three. -/
  m0 : ℕ
  m1 : ℕ
  m2 : ℕ
  m3 : ℕ
  /-- Slice widths at depths zero through three. -/
  w0 : ℕ
  w1 : ℕ
  w2 : ℕ
  w3 : ℕ
  /-- A slice exits as large at depth `j` when its retained row family has
  at least `capj` members. -/
  cap0 : ℕ
  cap1 : ℕ
  cap2 : ℕ
  /-- Aggregate retained-row mass required by the later Theorems 4.11 and
  4.15 assembly. -/
  assemblyMass : ℕ
  /-- The integer fanout is a rounding-safe square-root surrogate. -/
  fanout_eq : fanout = Nat.sqrt g + 1
  /-- Three fanouts have enough multiplicative room; this elementary
  square-root fact is stored explicitly for later arithmetic. -/
  g_le_fanout_sq : g ≤ fanout * fanout
  /-- The paper's nondegenerate parameter range. -/
  g_at_least_two : 2 ≤ g
  /-- The Lemma 4.8 / Theorem 4.11 degree parameter is positive. -/
  Dhat_pos : 0 < Dhat
  /-- Theorem 4.11 requires `Dhat >= 8 * g^2` when `wHat = g^2`. -/
  theorem411_scale : 8 * g ^ 2 ≤ Dhat
  /-- Every declared slicing has a positive count and width. -/
  counts_pos : 0 < m0 ∧ 0 < m1 ∧ 0 < m2 ∧ 0 < m3
  widths_pos : 0 < w0 ∧ 0 < w1 ∧ 0 < w2 ∧ 0 < w3
  /-- If fewer than half the depth-zero slices are large, their refinements
  contain at least `m1` slices. -/
  count01 : 2 * m1 ≤ m0 * fanout
  /-- The analogous depth-one count. -/
  count12 : 2 * m2 ≤ m1 * fanout
  /-- The analogous depth-two count. -/
  count23 : 2 * m3 ≤ m2 * fanout
  /-- Exact path budget for the first refinement. -/
  refineBudget01 :
    2 * (fanout * w1 + (fanout + 1) * cap0 + 4 * g ^ 4) ≤ w0
  /-- Exact path budget for the second refinement. -/
  refineBudget12 :
    2 * (fanout * w2 + (fanout + 1) * cap1 + 4 * g ^ 4) ≤ w1
  /-- Exact path budget for the third refinement. -/
  refineBudget23 :
    2 * (fanout * w3 + (fanout + 1) * cap2 + 4 * g ^ 4) ≤ w2
  /-- A majority-large exit at depth zero has enough total row mass. -/
  largeMass0 : 2 * assemblyMass ≤ m0 * cap0
  /-- A majority-large exit at depth one has enough total row mass. -/
  largeMass1 : 2 * assemblyMass ≤ m1 * cap1
  /-- A majority-large exit at depth two has enough total row mass. -/
  largeMass2 : 2 * assemblyMass ≤ m2 * cap2
  /-- The all-small branch recovers the Section 4 number of slices. -/
  finalSliceCount :
    8 * g ^ 4 * (Nat.log 2 g + 1) ≤ m3
  /-- The final width suffices for additive Lemma 4.8 with
  `wHat = 4 * g^2`.  Since the refinement budgets force earlier widths to
  be larger, this is the decisive pruning inequality. -/
  finalPruning :
    2 * N * (4 * g ^ 2) ≤ Dhat * w3
  /-- The initial Theorem 4.6 cost, including the Section 4 factor-eight
  retained-path loss, fits the advertised local terminal threshold. -/
  localCost :
    8 * (m0 * w0 + (m0 + 1) * N) ≤
      exponentEightLocalThreshold C logExp g

namespace ThreeRoundParameters

theorem fanout_pos {g N Dhat : ℕ}
    (p : ThreeRoundParameters g N Dhat) : 0 < p.fanout := by
  rw [p.fanout_eq]
  omega

end ThreeRoundParameters

/-- Additive form of the one-slice Lemma 4.8 output.

This retains all fields of `PathSlicing.SliceIntersectingSubfamilies` and
also records the exact charge from discarded auxiliary paths to discarded
rows. -/
structure AdditiveSliceCleanup
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {M : ℕ} (sigma : PathSlicing Rbar M)
    (i : Fin M) (wHat Dhat : ℕ) where
  /-- Rows retained by Lemma 4.8. -/
  rows : Finset Rbar.Index
  /-- Auxiliary paths retained by Lemma 4.8. -/
  paths : Finset Qbar.Index
  rows_subset : rows ⊆ Finset.univ
  paths_subset : paths ⊆ sigma.pathsInSlice Qbar i
  intersecting :
    sigma.SliceIntersectingPathSetPair
      Qbar i rows paths wHat Dhat
  half_paths :
    (sigma.pathsInSlice Qbar i).card ≤ 2 * paths.card
  discarded_rows_sparse :
    ∀ r ∈ (Finset.univ : Finset Rbar.Index) \ rows,
      (sigma.segmentIntersectingRightIndices Qbar i paths r).card ≤ wHat
  additive_loss :
    ((sigma.pathsInSlice Qbar i) \ paths).card * Dhat ≤
      ((Finset.univ : Finset Rbar.Index) \ rows).card * wHat

/-- Axiom-free producer for `AdditiveSliceCleanup`.

The proof uses the additive pruning trace exposed in
`Exponent8.Lemma48Additive`; the weaker half-retention statement is derived
inside that theorem from the same trace and is not reproved here. -/
noncomputable def exists_additiveSliceCleanup
    {W : Type v} [Fintype W] [DecidableEq W]
    {H : _root_.SimpleGraph W}
    {Abar Bbar Sbar Tbar : Finset W}
    (Rbar : PerfectPathPacking H Abar Bbar)
    (Qbar : PathPacking H Sbar Tbar)
    {M : ℕ} (sigma : PathSlicing Rbar M)
    (i : Fin M) {wHat Dhat : ℕ}
    (hDhat : 0 < Dhat)
    (hdense :
      ∀ q ∈ sigma.pathsInSlice Qbar i,
        2 * Dhat ≤
          (sigma.segmentIntersectingLeftIndices Qbar i
            (Finset.univ : Finset Rbar.Index) q).card)
    (hcard :
      2 * Rbar.card * wHat ≤
        Dhat * (sigma.pathsInSlice Qbar i).card) :
    AdditiveSliceCleanup (Qbar := Qbar) sigma i wHat Dhat := by
  classical
  let rel : Rbar.Index → Qbar.Index → Prop :=
    fun r q => sigma.SliceSegmentIntersectsPath Qbar i r q
  have hdense' :
      ∀ q ∈ sigma.pathsInSlice Qbar i,
        2 * Dhat ≤
          ((Finset.univ : Finset Rbar.Index).bipartiteBelow rel q).card := by
    intro q hq
    simpa [PathSlicing.segmentIntersectingLeftIndices, rel] using
      hdense q hq
  have hcard' :
      2 * (Finset.univ : Finset Rbar.Index).card * wHat ≤
        Dhat * (sigma.pathsInSlice Qbar i).card := by
    simpa [PathPacking.card] using hcard
  let hex :=
    FiniteBipartitePruning.PruneTrace.exists_intersecting_subsets_additive
      (rel := rel) (wHat := wHat) (Dhat := Dhat)
      (Finset.univ : Finset Rbar.Index)
      (sigma.pathsInSlice Qbar i)
      hDhat hdense' hcard'
  let rows := Classical.choose hex
  let hex2 := Classical.choose_spec hex
  let paths := Classical.choose hex2
  have hspec := Classical.choose_spec hex2
  have hrows := hspec.1
  have hpaths := hspec.2.1
  have hleft := hspec.2.2.1
  have hright := hspec.2.2.2.1
  have hloss := hspec.2.2.2.2.1
  have hhalf := hspec.2.2.2.2.2.1
  have hsparse := hspec.2.2.2.2.2.2
  refine
    { rows := rows
      paths := paths
      rows_subset := hrows
      paths_subset := hpaths
      intersecting := ?_
      half_paths := hhalf
      discarded_rows_sparse := ?_
      additive_loss := hloss }
  · constructor
    · intro r hr
      simpa [PathSlicing.segmentIntersectingRightIndices, paths, rel] using
        hleft r hr
    · intro q hq
      simpa [PathSlicing.segmentIntersectingLeftIndices, rows, rel] using
        hright q hq
  · intro r hr
    simpa [PathSlicing.segmentIntersectingRightIndices, paths, rel] using
      hsparse r hr

/-- A recursive layer contains actual cuts, a width certificate, the
additive cleanup of every slice, and the original/contracted localization
data needed by the last-hit construction. -/
structure RecursiveSliceLayer
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    (A B X : Finset V)
    (P : PerfectPathPacking G A B)
    (Q : PerfectPathPacking G A X)
    {Abar Bbar Sbar Tbar : Finset W}
    (Rbar : PerfectPathPacking H Abar Bbar)
    (Qbar : PathPacking H Sbar Tbar)
    (m width wHat Dhat : ℕ) where
  sigma : PathSlicing Rbar m
  width_at_least : sigma.WidthAtLeast Qbar width
  unique_linkage : Rbar.IsUniqueLinkage
  cleanup :
    ∀ i : Fin m, AdditiveSliceCleanup sigma i wHat Dhat
  localization :
    ∀ i : Fin m,
      SliceLocalizationInvariant
        G H A B X P Q Rbar Qbar sigma i
  localized_eq :
    ∀ i : Fin m,
      (localization i).localizedQ = (cleanup i).paths

namespace RecursiveSliceLayer

/-- The strengthened Claim 5.3 applied directly to one recursive layer.

The bad rows are exactly the rows discarded by additive Lemma 4.8, and the
candidate auxiliary family is exactly the retained `paths` field.  The
localization equality turns `discarded_rows_sparse` into the bounded-hit
hypothesis of `claim53Strong_four_mul_g_pow_four`.  Thus this bridge is an
ordinary theorem, not part of the recursive-slicing axiom. -/
theorem claim53Strong_cleanup
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m width Dhat g : ℕ}
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (i : Fin m)
    (hg : 0 < g)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    (L.cleanup i).paths.card ≤
      ((L.localization i).goodQ
        ((Finset.univ : Finset Rbar.Index) \ (L.cleanup i).rows)
        (L.cleanup i).paths).card +
          4 * g ^ 4 := by
  classical
  let bad : Finset Rbar.Index :=
    (Finset.univ : Finset Rbar.Index) \ (L.cleanup i).rows
  have hQset :
      (L.cleanup i).paths ⊆ (L.localization i).localizedQ := by
    rw [L.localized_eq i]
  have hcap :
      ∀ b ∈ bad,
        ((L.localization i).hitQAt (L.cleanup i).paths b).card ≤
          4 * g ^ 2 := by
    intro b hb
    have hsparse :=
      (L.cleanup i).discarded_rows_sparse b (by simpa [bad] using hb)
    have heq :
        (L.localization i).hitQAt (L.cleanup i).paths b =
          L.sigma.segmentIntersectingRightIndices
            Qbar i (L.cleanup i).paths b := by
      ext q
      rw [(L.localization i).mem_hitQAt]
      rw [L.sigma.mem_segmentIntersectingRightIndices]
      constructor
      · rintro ⟨hq, _hlocalized, hhit⟩
        exact ⟨hq, hhit⟩
      · rintro ⟨hq, hhit⟩
        exact
          ⟨hq, by
            rw [L.localized_eq i]
            exact hq, hhit⟩
    rw [heq]
    exact hsparse
  simpa [bad] using
    (L.localization i).claim53Strong_four_mul_g_pow_four
      bad (L.cleanup i).paths g hg hQset hcap hnoCrossbar

end RecursiveSliceLayer

/-- A majority of the slices at one recursion depth has enough retained rows
to exit to the Section 4.4--4.5 assembly. -/
structure LargeSliceLayer
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m width wHat Dhat : ℕ}
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (rowCap : ℕ) where
  large : Finset (Fin m)
  majority : m ≤ 2 * large.card
  rows_large :
    ∀ i ∈ large, rowCap ≤ (L.cleanup i).rows.card

/-- Four possible outcomes of the three-round recursion.

The first three constructors are the majority-large exits at depths zero,
one, and two.  `final` is the all-small branch after all three refinements. -/
inductive ThreeRoundRecursiveSlicingResult
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    (A B X : Finset V)
    (P : PerfectPathPacking G A B)
    (Q : PerfectPathPacking G A X)
    {Abar Bbar Sbar Tbar : Finset W}
    (Rbar : PerfectPathPacking H Abar Bbar)
    (Qbar : PathPacking H Sbar Tbar)
    (g Dhat : ℕ)
    (p : ThreeRoundParameters g Rbar.card Dhat)
    (L0 : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      p.m0 p.w0 (4 * g ^ 2) Dhat) : Type (max u v)
  | large0
      (output : LargeSliceLayer L0 p.cap0)
  | large1
      (L1 : RecursiveSliceLayer
        G H A B X P Q Rbar Qbar
        p.m1 p.w1 (4 * g ^ 2) Dhat)
      (output : LargeSliceLayer L1 p.cap1)
  | large2
      (L2 : RecursiveSliceLayer
        G H A B X P Q Rbar Qbar
        p.m2 p.w2 (4 * g ^ 2) Dhat)
      (output : LargeSliceLayer L2 p.cap2)
  | final
      (L3 : RecursiveSliceLayer
        G H A B X P Q Rbar Qbar
        p.m3 p.w3 (4 * g ^ 2) Dhat)

/-- The single permitted placeholder for the later three-round recursive
slicing proof.

Its hypotheses contain actual slice cuts, additive Lemma 4.8 outputs, and
original/contracted localization data.  Its numerical parameters are
constrained by the exact three Theorem 4.6 budgets; consequently the axiom
does not assert a slicing with arbitrary target counts or widths.

What remains to prove is precisely the recursive semantic step described in
the module header: hereditary unique linkage (Observation 5.4), local-to-
global cut composition, localization preservation, and the finite three-level
majority recursion. -/
axiom threeRoundRecursiveSlicing
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {g Dhat : ℕ}
    (p : ThreeRoundParameters g Rbar.card Dhat)
    (L0 : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      p.m0 p.w0 (4 * g ^ 2) Dhat)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    Nonempty
      (ThreeRoundRecursiveSlicingResult
        G H A B X P Q Rbar Qbar g Dhat p L0)

end Exponent8
end SimpleGraph
