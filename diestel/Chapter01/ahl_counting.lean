import Chapter01.ahl_analytic
import Chapter01.moore_bound
import Mathlib.Analysis.MeanInequalities

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
The AHL continuations of length `l` from a directed edge `d = uv`.
This is `Ω_{d,l}` in `Chapter01/ahl.pdf`: after the initial directed edge
`uv`, it records non-returning continuations of `l` further steps from `v`,
with the first step forbidden to go back to `u`.
-/
abbrev AhlDartContinuation {V : Type u} (G : SimpleGraph V)
    (d : G.Dart) (l : ℕ) :=
  AvoidingPathOfLength G d.toProd.2 d.toProd.1 l

/-- The finite average `N_l` of AHL continuation counts over all directed edges. -/
noncomputable def ahlN {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (l : ℕ) : ℝ :=
  (Fintype.card G.Dart : ℝ)⁻¹ *
    ∑ d : G.Dart, (Nat.card (AhlDartContinuation G d l) : ℝ)

/--
The probability weight of one AHL continuation, conditional on its initial dart.
For a continuation `v₀ v₁ ... v_l`, this is
`∏_{i<l} (degree v_i - 1)⁻¹`.
-/
noncomputable def ahlContinuationWeight {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ} {d : G.Dart}
    (A : AhlDartContinuation G d l) : ℝ :=
  ∏ i ∈ Finset.range l, (((G.degree (A.2.1.getVert i) : ℝ) - 1)⁻¹)

/-- The reciprocal denominator of `ahlContinuationWeight`, i.e. `1 / p(ω)`. -/
noncomputable def ahlContinuationInvWeight {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ} {d : G.Dart}
    (A : AhlDartContinuation G d l) : ℝ :=
  ∏ i ∈ Finset.range l, ((G.degree (A.2.1.getVert i) : ℝ) - 1)

theorem ahlContinuationWeight_nonneg {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ} {d : G.Dart}
    (hdeg : ∀ v : V, 2 ≤ G.degree v) (A : AhlDartContinuation G d l) :
    0 ≤ ahlContinuationWeight G A := by
  dsimp [ahlContinuationWeight]
  apply Finset.prod_nonneg
  intro i hi
  apply inv_nonneg.mpr
  have h : (2 : ℝ) ≤ (G.degree (A.2.1.getVert i) : ℝ) := by
    exact_mod_cast hdeg (A.2.1.getVert i)
  linarith

theorem ahlContinuationWeight_pos {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ} {d : G.Dart}
    (hdeg : ∀ v : V, 2 ≤ G.degree v) (A : AhlDartContinuation G d l) :
    0 < ahlContinuationWeight G A := by
  dsimp [ahlContinuationWeight]
  apply Finset.prod_pos
  intro i hi
  apply inv_pos.mpr
  have h : (2 : ℝ) ≤ (G.degree (A.2.1.getVert i) : ℝ) := by
    exact_mod_cast hdeg (A.2.1.getVert i)
  linarith

theorem ahlContinuationInvWeight_nonneg {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ} {d : G.Dart}
    (hdeg : ∀ v : V, 2 ≤ G.degree v) (A : AhlDartContinuation G d l) :
    0 ≤ ahlContinuationInvWeight G A := by
  dsimp [ahlContinuationInvWeight]
  apply Finset.prod_nonneg
  intro i hi
  have h : (2 : ℝ) ≤ (G.degree (A.2.1.getVert i) : ℝ) := by
    exact_mod_cast hdeg (A.2.1.getVert i)
  linarith

theorem ahlContinuationInvWeight_pos {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ} {d : G.Dart}
    (hdeg : ∀ v : V, 2 ≤ G.degree v) (A : AhlDartContinuation G d l) :
    0 < ahlContinuationInvWeight G A := by
  dsimp [ahlContinuationInvWeight]
  apply Finset.prod_pos
  intro i hi
  have h : (2 : ℝ) ≤ (G.degree (A.2.1.getVert i) : ℝ) := by
    exact_mod_cast hdeg (A.2.1.getVert i)
  linarith

theorem ahlContinuationWeight_zero {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {d : G.Dart}
    (A : AhlDartContinuation G d 0) :
    ahlContinuationWeight G A = 1 := by
  simp [ahlContinuationWeight]

theorem ahlContinuationInvWeight_zero {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {d : G.Dart}
    (A : AhlDartContinuation G d 0) :
    ahlContinuationInvWeight G A = 1 := by
  simp [ahlContinuationInvWeight]

def ahlContinuationPred {V : Type u} (G : SimpleGraph V)
    {l : ℕ} {d : G.Dart} (A : AhlDartContinuation G d l) : V :=
  if l = 0 then d.toProd.1 else pathLastPred (avoidingToPathOfLength A)

theorem ahlContinuationPred_adj {V : Type u} {G : SimpleGraph V}
    {l : ℕ} {d : G.Dart} (A : AhlDartContinuation G d l) :
    G.Adj A.1 (ahlContinuationPred G A) := by
  dsimp [ahlContinuationPred]
  by_cases hl : l = 0
  · rw [if_pos hl]
    subst l
    rcases A with ⟨x, p, hp, hplen, havoid⟩
    cases p with
    | nil =>
        simpa using d.adj.symm
    | cons h q =>
        simp at hplen
  · rw [if_neg hl]
    exact pathEndpoint_adj_lastPred (by omega) (avoidingToPathOfLength A)

/-- The directed edge occupied after an AHL continuation. -/
def ahlContinuationCurrentDart {V : Type u} (G : SimpleGraph V)
    {l : ℕ} {d : G.Dart} (A : AhlDartContinuation G d l) : G.Dart :=
  ⟨(ahlContinuationPred G A, A.1), (ahlContinuationPred_adj A).symm⟩

@[simp]
theorem ahlContinuationCurrentDart_zero {V : Type u} (G : SimpleGraph V)
    {d : G.Dart} (A : AhlDartContinuation G d 0) :
    ahlContinuationCurrentDart G A = d := by
  rcases A with ⟨x, p, hp, hplen, havoid⟩
  cases p with
  | nil =>
      ext <;> rfl
  | cons h q =>
      simp at hplen

abbrev AhlContinuationExtensionChoice {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {l : ℕ} {d : G.Dart} (A : AhlDartContinuation G d l) :=
  (↑((G.neighborFinset A.1).erase (ahlContinuationPred G A)) : Type u)

theorem ahlContinuationExtensionChoice_card {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {l : ℕ} {d : G.Dart}
    (A : AhlDartContinuation G d l) :
    Nat.card (AhlContinuationExtensionChoice G A) = G.degree A.1 - 1 := by
  classical
  have hmem :
      ahlContinuationPred G A ∈ G.neighborFinset A.1 := by
    rw [SimpleGraph.mem_neighborFinset]
    exact ahlContinuationPred_adj A
  rw [Nat.card_eq_fintype_card]
  dsimp [AhlContinuationExtensionChoice]
  rw [Fintype.card_coe]
  rw [Finset.card_erase_of_mem hmem]
  rw [SimpleGraph.card_neighborFinset_eq_degree]

theorem sum_transitionWeight_extensionChoice {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {l : ℕ} {d : G.Dart}
    (hdeg : ∀ v : V, 2 ≤ G.degree v) (A : AhlDartContinuation G d l) :
    ∑ y : AhlContinuationExtensionChoice G A,
        (((G.degree A.1 : ℝ) - 1)⁻¹) = 1 := by
  have hcard :
      Fintype.card (AhlContinuationExtensionChoice G A) = G.degree A.1 - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact ahlContinuationExtensionChoice_card G A
  have hdeg_one : 1 ≤ G.degree A.1 := by
    have htwo := hdeg A.1
    omega
  have hcast : ((G.degree A.1 - 1 : ℕ) : ℝ) = (G.degree A.1 : ℝ) - 1 := by
    rw [Nat.cast_sub hdeg_one]
    norm_num
  have hpos : 0 < (G.degree A.1 : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ (G.degree A.1 : ℝ) := by
      exact_mod_cast hdeg A.1
    linarith
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ]
  rw [hcard, hcast]
  exact mul_inv_cancel₀ hpos.ne'

noncomputable def ahlContinuationExtend {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (A : AhlDartContinuation G d l)
    (Y : AhlContinuationExtensionChoice G A) :
    AhlDartContinuation G d (l + 1) :=
  let y : V := Y.1
  let hY := Finset.mem_erase.mp Y.2
  let hy_ne_pred : y ≠ ahlContinuationPred G A := hY.1
  let hxy : G.Adj A.1 y := (SimpleGraph.mem_neighborFinset G A.1 y).mp hY.2
  have hnot_prev : A.2.1.length = 0 ∨ y ≠ A.2.1.getVert (A.2.1.length - 1) := by
    by_cases hl : l = 0
    · left
      rw [A.2.2.2.1, hl]
    · right
      intro hy
      apply hy_ne_pred
      have hpred_eq :
          ahlContinuationPred G A = A.2.1.getVert (A.2.1.length - 1) := by
        dsimp [ahlContinuationPred, avoidingToPathOfLength, pathLastPred]
        rw [if_neg hl]
        congr
        rw [A.2.2.2.1]
      rw [hpred_eq]
      exact hy
  ⟨y, ⟨A.2.1.concat hxy,
    concat_isPath_of_girth_ge hg A.2.2.1 hxy
      (by
        rw [A.2.2.2.1]
        exact hshort)
      hnot_prev,
    by
      rw [SimpleGraph.Walk.length_concat, A.2.2.2.1],
    by
      intro _
      by_cases hl : l = 0
      · have hy_ne_forbidden : y ≠ d.toProd.1 := by
          simpa [ahlContinuationPred, hl] using hy_ne_pred
        have hconcat_len : (A.2.1.concat hxy).length = 1 := by
          rw [SimpleGraph.Walk.length_concat, A.2.2.2.1, hl]
        have hget : (A.2.1.concat hxy).getVert 1 = y := by
          have h := SimpleGraph.Walk.getVert_length (A.2.1.concat hxy)
          rw [hconcat_len] at h
          exact h
        rw [hget]
        exact hy_ne_forbidden
      · have hle_one : 1 ≤ A.2.1.length := by
          rw [A.2.2.2.1]
          omega
        rw [getVert_concat_of_le_length A.2.1 hxy hle_one]
        exact A.2.2.2.2 (by omega)⟩⟩

theorem ahlContinuationExtend_fst {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (A : AhlDartContinuation G d l)
    (Y : AhlContinuationExtensionChoice G A) :
    (ahlContinuationExtend G hg hshort A Y).1 = Y.1 := by
  rcases A with ⟨x, p, hp, hplen, havoid⟩
  simp [ahlContinuationExtend]

theorem ahlContinuationCurrentDart_extend {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (A : AhlDartContinuation G d l)
    (Y : AhlContinuationExtensionChoice G A) :
    ahlContinuationCurrentDart G (ahlContinuationExtend G hg hshort A Y) =
      (⟨(A.1, Y.1),
        (SimpleGraph.mem_neighborFinset G A.1 Y.1).mp
          (Finset.mem_erase.mp Y.2).2⟩ : G.Dart) := by
  rcases A with ⟨x, p, hp, hplen, havoid⟩
  subst l
  ext
  · dsimp [ahlContinuationCurrentDart, ahlContinuationExtend,
      ahlContinuationPred, avoidingToPathOfLength, pathLastPred]
    exact getVert_concat_length p _
  · dsimp [ahlContinuationCurrentDart, ahlContinuationExtend]

theorem ahlContinuationExtend_weight {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (A : AhlDartContinuation G d l)
    (Y : AhlContinuationExtensionChoice G A) :
    ahlContinuationWeight G (ahlContinuationExtend G hg hshort A Y) =
      ahlContinuationWeight G A * (((G.degree A.1 : ℝ) - 1)⁻¹) := by
  rcases A with ⟨x, p, hp, hplen, havoid⟩
  subst l
  dsimp [ahlContinuationWeight, ahlContinuationExtend]
  rw [Finset.prod_range_succ]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    have hile : i ≤ p.length := by
      have hi' : i < p.length := Finset.mem_range.mp hi
      omega
    rw [getVert_concat_of_le_length p _ hile]
  · rw [getVert_concat_of_le_length p _ le_rfl]
    rw [SimpleGraph.Walk.getVert_length]

theorem ahlContinuationExtend_invWeight {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (A : AhlDartContinuation G d l)
    (Y : AhlContinuationExtensionChoice G A) :
    ahlContinuationInvWeight G (ahlContinuationExtend G hg hshort A Y) =
      ahlContinuationInvWeight G A * ((G.degree A.1 : ℝ) - 1) := by
  rcases A with ⟨x, p, hp, hplen, havoid⟩
  subst l
  dsimp [ahlContinuationInvWeight, ahlContinuationExtend]
  rw [Finset.prod_range_succ]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    have hile : i ≤ p.length := by
      have hi' : i < p.length := Finset.mem_range.mp hi
      omega
    rw [getVert_concat_of_le_length p _ hile]
  · rw [getVert_concat_of_le_length p _ le_rfl]
    rw [SimpleGraph.Walk.getVert_length]

def ahlContinuationDropLast {V : Type u} {G : SimpleGraph V}
    {l : ℕ} {d : G.Dart} (B : AhlDartContinuation G d (l + 1)) :
    AhlDartContinuation G d l :=
  let q := B.2.1
  have hnil : ¬ q.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    rw [B.2.2.2.1]
    omega
  ⟨q.penultimate, ⟨q.dropLast,
    by
      dsimp [q, SimpleGraph.Walk.dropLast]
      exact B.2.2.1.take (q.length - 1),
    by
      rw [SimpleGraph.Walk.length_dropLast, B.2.2.2.1]
      omega,
    by
      intro hlpos
      have hle_one : 1 ≤ q.dropLast.length := by
        rw [SimpleGraph.Walk.length_dropLast, B.2.2.2.1]
        omega
      have hget : q.dropLast.getVert 1 = q.getVert 1 := by
        have h := getVert_concat_of_le_length q.dropLast (q.adj_penultimate hnil) hle_one
        rw [SimpleGraph.Walk.concat_dropLast] at h
        exact h.symm
      rw [hget]
      exact B.2.2.2.2 (by omega)⟩⟩

def ahlContinuationLastChoice {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {l : ℕ} {d : G.Dart} (B : AhlDartContinuation G d (l + 1)) :
    AhlContinuationExtensionChoice G (ahlContinuationDropLast B) := by
  rcases B with ⟨y, q, hq, hqlen, havoid⟩
  have hnil : ¬ q.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    rw [hqlen]
    omega
  refine ⟨y, ?_⟩
  rw [Finset.mem_erase]
  constructor
  · by_cases hl : l = 0
    · intro hy
      have hget_one : q.getVert 1 = y := by
        have hlen : q.length = 1 := by
          rw [hqlen, hl]
        rw [← hlen, SimpleGraph.Walk.getVert_length]
      have hy_forbidden : q.getVert 1 ≠ d.toProd.1 := havoid (by omega)
      apply hy_forbidden
      rw [hget_one]
      simpa [ahlContinuationDropLast, ahlContinuationPred, hl] using hy
    · intro hy
      have hpred_eq :
          ahlContinuationPred G
              (ahlContinuationDropLast
                (⟨y, ⟨q, hq, hqlen, havoid⟩⟩ :
                  AhlDartContinuation G d (l + 1))) =
            q.getVert (l - 1) := by
        dsimp [ahlContinuationDropLast, ahlContinuationPred,
          avoidingToPathOfLength, pathLastPred]
        rw [if_neg hl]
        have hle : l - 1 ≤ q.dropLast.length := by
          rw [SimpleGraph.Walk.length_dropLast, hqlen]
          omega
        have hget := getVert_concat_of_le_length q.dropLast (q.adj_penultimate hnil) hle
        rw [SimpleGraph.Walk.concat_dropLast] at hget
        exact hget.symm
      have hget_eq : q.getVert q.length = q.getVert (l - 1) := by
        calc
          q.getVert q.length = y := SimpleGraph.Walk.getVert_length q
          _ = ahlContinuationPred G
              (ahlContinuationDropLast
                (⟨y, ⟨q, hq, hqlen, havoid⟩⟩ :
                  AhlDartContinuation G d (l + 1))) := hy
          _ = q.getVert (l - 1) := hpred_eq
      have hidx :
          q.length = l - 1 := by
        apply hq.getVert_injOn
        · simp
        · simp
          rw [hqlen]
          omega
        · exact hget_eq
      omega
  · rw [SimpleGraph.mem_neighborFinset]
    exact q.adj_penultimate hnil

theorem ahlContinuationExtend_dropLast_lastChoice {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (hsmall : (l + 1) + (l + 1) < g)
    (B : AhlDartContinuation G d (l + 1)) :
    ahlContinuationExtend G hg hshort
        (ahlContinuationDropLast B) (ahlContinuationLastChoice G B) = B := by
  apply avoiding_endpoint_injective (G := G) hg hsmall
  change (ahlContinuationExtend G hg hshort
      (ahlContinuationDropLast B) (ahlContinuationLastChoice G B)).1 = B.1
  rw [ahlContinuationExtend_fst]
  rcases B with ⟨y, q, hq, hqlen, havoid⟩
  rfl

theorem ahlContinuationDropLast_extend {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (hsmall : l + l < g)
    (A : AhlDartContinuation G d l)
    (Y : AhlContinuationExtensionChoice G A) :
    ahlContinuationDropLast (ahlContinuationExtend G hg hshort A Y) = A := by
  apply avoiding_endpoint_injective (G := G) hg hsmall
  rcases A with ⟨x, p, hp, hplen, havoid⟩
  subst l
  change (ahlContinuationDropLast (ahlContinuationExtend G hg hshort
      (⟨x, ⟨p, hp, rfl, havoid⟩⟩ : AhlDartContinuation G d p.length) Y)).1 = x
  simp [ahlContinuationDropLast, ahlContinuationExtend, SimpleGraph.Walk.penultimate_concat]

theorem ahlContinuationExtend_injective {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (hsmall : l + l < g) :
    Function.Injective
      (fun S : Σ A : AhlDartContinuation G d l,
          AhlContinuationExtensionChoice G A =>
        ahlContinuationExtend G hg hshort S.1 S.2) := by
  intro S T hST
  rcases S with ⟨A, Y⟩
  rcases T with ⟨B, Z⟩
  have hAB : A = B := by
    have hdrop := congrArg ahlContinuationDropLast hST
    rw [ahlContinuationDropLast_extend G hg hshort hsmall A Y] at hdrop
    rw [ahlContinuationDropLast_extend G hg hshort hsmall B Z] at hdrop
    exact hdrop
  cases hAB
  have hYZ_val : Y.1 = Z.1 := by
    have hend := congrArg (fun Q : AhlDartContinuation G d (l + 1) => Q.1) hST
    change (ahlContinuationExtend G hg hshort A Y).1 =
        (ahlContinuationExtend G hg hshort A Z).1 at hend
    rw [ahlContinuationExtend_fst] at hend
    rw [ahlContinuationExtend_fst] at hend
    exact hend
  have hYZ : Y = Z := by
    apply Subtype.ext
    exact hYZ_val
  cases hYZ
  rfl

theorem ahlContinuationExtend_surjective {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (hnextsmall : (l + 1) + (l + 1) < g) :
    Function.Surjective
      (fun S : Σ A : AhlDartContinuation G d l,
          AhlContinuationExtensionChoice G A =>
        ahlContinuationExtend G hg hshort S.1 S.2) := by
  intro B
  refine ⟨⟨ahlContinuationDropLast B, ahlContinuationLastChoice G B⟩, ?_⟩
  exact ahlContinuationExtend_dropLast_lastChoice G hg hshort hnextsmall B

noncomputable def ahlContinuationExtensionEquiv {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (hnextsmall : (l + 1) + (l + 1) < g) :
    (Σ A : AhlDartContinuation G d l, AhlContinuationExtensionChoice G A) ≃
      AhlDartContinuation G d (l + 1) :=
  Equiv.ofBijective
    (fun S : Σ A : AhlDartContinuation G d l,
        AhlContinuationExtensionChoice G A =>
      ahlContinuationExtend G hg hshort S.1 S.2)
    ⟨ahlContinuationExtend_injective G hg hshort (by omega),
      ahlContinuationExtend_surjective G hg hshort hnextsmall⟩

theorem sum_ahlContinuationWeight_succ {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (hnextsmall : (l + 1) + (l + 1) < g)
    [Fintype (AhlDartContinuation G d l)]
    [Fintype (AhlDartContinuation G d (l + 1))]
    (hdeg : ∀ v : V, 2 ≤ G.degree v)
    (hprob : ∑ A : AhlDartContinuation G d l,
      ahlContinuationWeight G A = 1) :
    ∑ B : AhlDartContinuation G d (l + 1),
      ahlContinuationWeight G B = 1 := by
  let e := ahlContinuationExtensionEquiv G hg hshort hnextsmall (d := d)
  have hsum_equiv :
      (∑ S : Σ A : AhlDartContinuation G d l,
          AhlContinuationExtensionChoice G A,
        ahlContinuationWeight G
          (ahlContinuationExtend G hg hshort S.1 S.2)) =
        ∑ B : AhlDartContinuation G d (l + 1),
          ahlContinuationWeight G B := by
    rw [Fintype.sum_equiv e
      (fun S : Σ A : AhlDartContinuation G d l,
          AhlContinuationExtensionChoice G A =>
        ahlContinuationWeight G (ahlContinuationExtend G hg hshort S.1 S.2))
      (fun B : AhlDartContinuation G d (l + 1) =>
        ahlContinuationWeight G B)
      (by intro S; rfl)]
  calc
    ∑ B : AhlDartContinuation G d (l + 1), ahlContinuationWeight G B =
        ∑ S : Σ A : AhlDartContinuation G d l,
          AhlContinuationExtensionChoice G A,
        ahlContinuationWeight G (ahlContinuationExtend G hg hshort S.1 S.2) := hsum_equiv.symm
    _ =
        ∑ A : AhlDartContinuation G d l,
          ∑ Y : AhlContinuationExtensionChoice G A,
            ahlContinuationWeight G (ahlContinuationExtend G hg hshort A Y) := by
      rw [Fintype.sum_sigma]
    _ =
        ∑ A : AhlDartContinuation G d l,
          ∑ Y : AhlContinuationExtensionChoice G A,
            ahlContinuationWeight G A * (((G.degree A.1 : ℝ) - 1)⁻¹) := by
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro Y hY
      rw [ahlContinuationExtend_weight G hg hshort A Y]
    _ =
        ∑ A : AhlDartContinuation G d l,
          ahlContinuationWeight G A *
            ∑ Y : AhlContinuationExtensionChoice G A,
              (((G.degree A.1 : ℝ) - 1)⁻¹) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [← Finset.mul_sum]
    _ =
        ∑ A : AhlDartContinuation G d l,
          ahlContinuationWeight G A * 1 := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [sum_transitionWeight_extensionChoice G hdeg A]
    _ = ∑ A : AhlDartContinuation G d l,
          ahlContinuationWeight G A := by
      simp
    _ = 1 := hprob

def ahlDartContinuationZeroEquiv {V : Type u} (G : SimpleGraph V)
    (d : G.Dart) : AhlDartContinuation G d 0 ≃ Unit where
  toFun _ := ()
  invFun _ :=
    ⟨d.toProd.2, ⟨SimpleGraph.Walk.nil,
      by
        constructor
        · simp [SimpleGraph.Walk.isPath_def]
        constructor
        · simp
        · intro h
          simp at h⟩⟩
  left_inv A := by
    rcases A with ⟨x, p, hp, hplen, havoid⟩
    cases p with
    | nil =>
        rfl
    | cons h q =>
        simp at hplen
  right_inv _ := by
    rfl

theorem sum_ahlContinuationWeight_zero {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {d : G.Dart}
    [Fintype (AhlDartContinuation G d 0)] :
    ∑ A : AhlDartContinuation G d 0, ahlContinuationWeight G A = 1 := by
  rw [Fintype.sum_equiv (ahlDartContinuationZeroEquiv G d)
    (fun A : AhlDartContinuation G d 0 => ahlContinuationWeight G A)
    (fun _ : Unit => (1 : ℝ))
    (by
      intro A
      simpa using ahlContinuationWeight_zero G A)]
  simp

theorem ahlDartContinuation_zero_natCard_eq_one {V : Type u}
    (G : SimpleGraph V) (d : G.Dart) :
    Nat.card (AhlDartContinuation G d 0) = 1 := by
  calc
    Nat.card (AhlDartContinuation G d 0) = Nat.card Unit :=
      Nat.card_congr (ahlDartContinuationZeroEquiv G d)
    _ = 1 := by simp

theorem ahlN_zero_eq_one {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj]
    (hD : Fintype.card G.Dart ≠ 0) :
    ahlN G 0 = 1 := by
  have hDreal : (Fintype.card G.Dart : ℝ) ≠ 0 := by exact_mod_cast hD
  dsimp [ahlN]
  have hsum :
      (∑ d : G.Dart, (Nat.card (AhlDartContinuation G d 0) : ℝ)) =
        (Fintype.card G.Dart : ℝ) := by
    simp [ahlDartContinuation_zero_natCard_eq_one]
  rw [hsum]
  field_simp [hDreal]

theorem ahlContinuationWeight_mul_invWeight {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ} {d : G.Dart}
    (hdeg : ∀ v : V, 2 ≤ G.degree v) (A : AhlDartContinuation G d l) :
    ahlContinuationWeight G A * ahlContinuationInvWeight G A = 1 := by
  dsimp [ahlContinuationWeight, ahlContinuationInvWeight]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i hi
  have hpos : 0 < (G.degree (A.2.1.getVert i) : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ (G.degree (A.2.1.getVert i) : ℝ) := by
      exact_mod_cast hdeg (A.2.1.getVert i)
    linarith
  exact inv_mul_cancel₀ hpos.ne'

abbrev AhlAllContinuations {V : Type u} (G : SimpleGraph V) (l : ℕ) :=
  Σ d : G.Dart, AhlDartContinuation G d l

noncomputable def ahlGlobalWeight {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ}
    (X : AhlAllContinuations G l) : ℝ :=
  (Fintype.card G.Dart : ℝ)⁻¹ * ahlContinuationWeight G X.2

noncomputable def ahlGlobalInvWeight {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ}
    (X : AhlAllContinuations G l) : ℝ :=
  ahlContinuationInvWeight G X.2

noncomputable def ahlLogGeom {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ}
    [∀ d : G.Dart, Fintype (AhlDartContinuation G d l)] : ℝ :=
  ∑ X : AhlAllContinuations G l,
    ahlGlobalWeight G X * Real.log (ahlGlobalInvWeight G X)

theorem ahlGlobalWeight_extend {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (A : AhlDartContinuation G d l)
    (Y : AhlContinuationExtensionChoice G A) :
    ahlGlobalWeight G ⟨d, ahlContinuationExtend G hg hshort A Y⟩ =
      ahlGlobalWeight G ⟨d, A⟩ * (((G.degree A.1 : ℝ) - 1)⁻¹) := by
  dsimp [ahlGlobalWeight]
  rw [ahlContinuationExtend_weight G hg hshort A Y]
  ring

theorem ahlLogGlobalInvWeight_extend {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (hdeg : ∀ v : V, 2 ≤ G.degree v)
    (A : AhlDartContinuation G d l)
    (Y : AhlContinuationExtensionChoice G A) :
    Real.log (ahlGlobalInvWeight G
        ⟨d, ahlContinuationExtend G hg hshort A Y⟩) =
      Real.log (ahlGlobalInvWeight G ⟨d, A⟩) +
        Real.log ((G.degree A.1 : ℝ) - 1) := by
  have hstep_pos : 0 < (G.degree A.1 : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ (G.degree A.1 : ℝ) := by
      exact_mod_cast hdeg A.1
    linarith
  dsimp [ahlGlobalInvWeight]
  rw [ahlContinuationExtend_invWeight G hg hshort A Y]
  rw [Real.log_mul (ahlContinuationInvWeight_pos G hdeg A).ne'
    hstep_pos.ne']

theorem sum_extension_globalWeight_logInvWeight {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart} (hshort : l + 1 < g)
    (hdeg : ∀ v : V, 2 ≤ G.degree v)
    (A : AhlDartContinuation G d l) :
    ∑ Y : AhlContinuationExtensionChoice G A,
        ahlGlobalWeight G
            ⟨d, ahlContinuationExtend G hg hshort A Y⟩ *
          Real.log (ahlGlobalInvWeight G
            ⟨d, ahlContinuationExtend G hg hshort A Y⟩) =
      ahlGlobalWeight G ⟨d, A⟩ *
          Real.log (ahlGlobalInvWeight G ⟨d, A⟩) +
        ahlGlobalWeight G ⟨d, A⟩ *
          Real.log ((G.degree A.1 : ℝ) - 1) := by
  let T : ℝ := (((G.degree A.1 : ℝ) - 1)⁻¹)
  let L : ℝ := Real.log (ahlGlobalInvWeight G ⟨d, A⟩)
  let M : ℝ := Real.log ((G.degree A.1 : ℝ) - 1)
  let W : ℝ := ahlGlobalWeight G ⟨d, A⟩
  have hsumT : ∑ _Y : AhlContinuationExtensionChoice G A, T = 1 := by
    dsimp [T]
    exact sum_transitionWeight_extensionChoice G hdeg A
  calc
    ∑ Y : AhlContinuationExtensionChoice G A,
        ahlGlobalWeight G
            ⟨d, ahlContinuationExtend G hg hshort A Y⟩ *
          Real.log (ahlGlobalInvWeight G
            ⟨d, ahlContinuationExtend G hg hshort A Y⟩)
        =
        ∑ Y : AhlContinuationExtensionChoice G A, (W * T) * (L + M) := by
      apply Finset.sum_congr rfl
      intro Y hY
      dsimp [W, T, L, M]
      rw [ahlGlobalWeight_extend G hg hshort A Y]
      rw [ahlLogGlobalInvWeight_extend G hg hshort hdeg A Y]
    _ =
        ∑ Y : AhlContinuationExtensionChoice G A,
            ((W * L) * T + (W * M) * T) := by
      apply Finset.sum_congr rfl
      intro Y hY
      ring
    _ =
        (W * L) * (∑ _Y : AhlContinuationExtensionChoice G A, T) +
          (W * M) * (∑ _Y : AhlContinuationExtensionChoice G A, T) := by
      rw [Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
    _ = W * L + W * M := by
      rw [hsumT]
      ring
    _ =
      ahlGlobalWeight G ⟨d, A⟩ *
          Real.log (ahlGlobalInvWeight G ⟨d, A⟩) +
        ahlGlobalWeight G ⟨d, A⟩ *
          Real.log ((G.degree A.1 : ℝ) - 1) := by
      rfl

theorem ahlGlobalWeight_nonneg {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ}
    (hdeg : ∀ v : V, 2 ≤ G.degree v) (X : AhlAllContinuations G l) :
    0 ≤ ahlGlobalWeight G X := by
  dsimp [ahlGlobalWeight]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (ahlContinuationWeight_nonneg G hdeg X.2)

theorem sum_ahlGlobalWeight_eq_one {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ}
    [∀ d : G.Dart, Fintype (AhlDartContinuation G d l)]
    (hD : Fintype.card G.Dart ≠ 0)
    (hprob : ∀ d : G.Dart, ∑ A : AhlDartContinuation G d l,
      ahlContinuationWeight G A = 1) :
    ∑ X : AhlAllContinuations G l, ahlGlobalWeight G X = 1 := by
  have hDreal : (Fintype.card G.Dart : ℝ) ≠ 0 := by exact_mod_cast hD
  calc
    ∑ X : AhlAllContinuations G l, ahlGlobalWeight G X =
        ∑ d : G.Dart, ∑ A : AhlDartContinuation G d l,
          (Fintype.card G.Dart : ℝ)⁻¹ * ahlContinuationWeight G A := by
      rw [Fintype.sum_sigma]
      rfl
    _ = ∑ d : G.Dart, (Fintype.card G.Dart : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.mul_sum]
      rw [hprob d]
      simp
    _ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_univ]
      field_simp [hDreal]

theorem sum_global_weight_mul_invWeight_eq_ahlN {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ}
    [∀ d : G.Dart, Fintype (AhlDartContinuation G d l)]
    (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    ∑ X : AhlAllContinuations G l,
        ahlGlobalWeight G X * ahlGlobalInvWeight G X = ahlN G l := by
  calc
    ∑ X : AhlAllContinuations G l,
        ahlGlobalWeight G X * ahlGlobalInvWeight G X =
        ∑ d : G.Dart, ∑ A : AhlDartContinuation G d l,
          ((Fintype.card G.Dart : ℝ)⁻¹ *
            ahlContinuationWeight G A) * ahlContinuationInvWeight G A := by
      rw [Fintype.sum_sigma]
      rfl
    _ = ∑ d : G.Dart, ∑ A : AhlDartContinuation G d l,
          (Fintype.card G.Dart : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro A hA
      rw [mul_assoc, ahlContinuationWeight_mul_invWeight G hdeg A]
      simp
    _ = (Fintype.card G.Dart : ℝ)⁻¹ *
          ∑ d : G.Dart, (Nat.card (AhlDartContinuation G d l) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [Nat.card_eq_fintype_card, mul_comm]
    _ = ahlN G l := by
      rfl

theorem ahl_amgm_lower_of_probabilities {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ}
    [∀ d : G.Dart, Fintype (AhlDartContinuation G d l)]
    (hD : Fintype.card G.Dart ≠ 0)
    (hdeg : ∀ v : V, 2 ≤ G.degree v)
    (hprob : ∀ d : G.Dart, ∑ A : AhlDartContinuation G d l,
      ahlContinuationWeight G A = 1) :
    (∏ X : AhlAllContinuations G l,
        ahlGlobalInvWeight G X ^ ahlGlobalWeight G X) ≤ ahlN G l := by
  have h :=
    Real.geom_mean_le_arith_mean_weighted (Finset.univ)
      (fun X : AhlAllContinuations G l => ahlGlobalWeight G X)
      (fun X : AhlAllContinuations G l => ahlGlobalInvWeight G X)
      (by
        intro X hX
        exact ahlGlobalWeight_nonneg G hdeg X)
      (by
        simpa using sum_ahlGlobalWeight_eq_one G hD hprob)
      (by
        intro X hX
        exact ahlContinuationInvWeight_nonneg G hdeg X.2)
  change (∏ X : AhlAllContinuations G l,
      ahlGlobalInvWeight G X ^ ahlGlobalWeight G X) ≤
    ∑ X : AhlAllContinuations G l,
      ahlGlobalWeight G X * ahlGlobalInvWeight G X at h
  rwa [sum_global_weight_mul_invWeight_eq_ahlN G hdeg] at h

theorem ahl_exp_logGeom_le_ahlN_of_probabilities {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {l : ℕ}
    [∀ d : G.Dart, Fintype (AhlDartContinuation G d l)]
    (hD : Fintype.card G.Dart ≠ 0)
    (hdeg : ∀ v : V, 2 ≤ G.degree v)
    (hprob : ∀ d : G.Dart, ∑ A : AhlDartContinuation G d l,
      ahlContinuationWeight G A = 1) :
    Real.exp (ahlLogGeom (l := l) G) ≤ ahlN G l := by
  have hJ :
      Real.exp
          (∑ X : AhlAllContinuations G l,
            ahlGlobalWeight G X * Real.log (ahlGlobalInvWeight G X)) ≤
        ∑ X : AhlAllContinuations G l,
          ahlGlobalWeight G X *
            Real.exp (Real.log (ahlGlobalInvWeight G X)) := by
    simpa [smul_eq_mul] using
      (convexOn_exp.map_sum_le
        (t := Finset.univ)
        (w := fun X : AhlAllContinuations G l => ahlGlobalWeight G X)
        (p := fun X : AhlAllContinuations G l =>
          Real.log (ahlGlobalInvWeight G X))
        (by
          intro X hX
          exact ahlGlobalWeight_nonneg G hdeg X)
        (by
          simpa using sum_ahlGlobalWeight_eq_one G hD hprob)
        (by
          intro X hX
          exact Set.mem_univ _))
  calc
    Real.exp (ahlLogGeom (l := l) G) ≤
        ∑ X : AhlAllContinuations G l,
          ahlGlobalWeight G X *
            Real.exp (Real.log (ahlGlobalInvWeight G X)) := by
      simpa [ahlLogGeom] using hJ
    _ = ∑ X : AhlAllContinuations G l,
          ahlGlobalWeight G X * ahlGlobalInvWeight G X := by
      apply Finset.sum_congr rfl
      intro X hX
      simp [ahlGlobalInvWeight,
        Real.exp_log (ahlContinuationInvWeight_pos G hdeg X.2)]
    _ = ahlN G l := sum_global_weight_mul_invWeight_eq_ahlN G hdeg

/-- Reversal of directed edges as a finite permutation. -/
def dartSymmEquiv {V : Type u} (G : SimpleGraph V) : G.Dart ≃ G.Dart where
  toFun d := d.symm
  invFun d := d.symm
  left_inv d := d.symm_symm
  right_inv d := d.symm_symm

@[simp]
theorem dartSymmEquiv_apply {V : Type u} (G : SimpleGraph V) (d : G.Dart) :
    dartSymmEquiv G d = d.symm :=
  rfl

theorem sum_dart_symm {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {M : Type*} [AddCommMonoid M]
    (f : G.Dart → M) :
    ∑ d : G.Dart, f d.symm = ∑ d : G.Dart, f d := by
  rw [← Fintype.sum_equiv (dartSymmEquiv G)
    (fun d : G.Dart => f d.symm)
    (fun d : G.Dart => f d)
    (by intro d; rfl)]

def dartNeighborEquiv {V : Type u} (G : SimpleGraph V) :
    (Σ v : V, G.neighborSet v) ≃ G.Dart where
  toFun s := G.dartOfNeighborSet s.1 s.2
  invFun d := ⟨d.fst, ⟨d.snd, d.adj⟩⟩
  left_inv s := by
    rcases s with ⟨v, w, hw⟩
    rfl
  right_inv d := by
    ext <;> rfl

theorem sum_dart_fst {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {M : Type*} [AddCommMonoid M]
    (f : V → M) :
    ∑ d : G.Dart, f d.fst = ∑ v : V, ∑ _w : G.neighborSet v, f v := by
  rw [← Fintype.sum_equiv (dartNeighborEquiv G)
    (fun s : Σ v : V, G.neighborSet v => f (dartNeighborEquiv G s).fst)
    (fun d : G.Dart => f d.fst)
    (by intro s; rfl)]
  rw [Fintype.sum_sigma]
  rfl

theorem sum_dart_fst_real {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (f : V → ℝ) :
    ∑ d : G.Dart, f d.fst = ∑ v : V, (G.degree v : ℝ) * f v := by
  rw [sum_dart_fst G f]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ]
  rw [SimpleGraph.card_neighborSet_eq_degree]

theorem sum_dart_snd_real {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (f : V → ℝ) :
    ∑ d : G.Dart, f d.snd = ∑ v : V, (G.degree v : ℝ) * f v := by
  calc
    ∑ d : G.Dart, f d.snd = ∑ d : G.Dart, f d.symm.fst := by
      rfl
    _ = ∑ d : G.Dart, f d.fst := sum_dart_symm G (fun d : G.Dart => f d.fst)
    _ = ∑ v : V, (G.degree v : ℝ) * f v := sum_dart_fst_real G f

abbrev DartTransitionChoice {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (d : G.Dart) :=
  (↑((G.neighborFinset d.snd).erase d.fst) : Type u)

abbrev DartTransitionStep {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :=
  Σ d : G.Dart, DartTransitionChoice G d

abbrev DartIncomingChoice {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (d : G.Dart) :=
  (↑((G.neighborFinset d.fst).erase d.snd) : Type u)

abbrev DartIncomingStep {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :=
  Σ d : G.Dart, DartIncomingChoice G d

def dartTransitionNext {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : DartTransitionStep G) : G.Dart :=
  ⟨(S.1.snd, S.2.1),
    (SimpleGraph.mem_neighborFinset G S.1.snd S.2.1).mp
      (Finset.mem_erase.mp S.2.2).2⟩

noncomputable def dartTransitionAverage {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (F : G.Dart → ℝ) (d : G.Dart) : ℝ :=
  ∑ y : DartTransitionChoice G d,
    (((G.degree d.snd : ℝ) - 1)⁻¹) *
      F (dartTransitionNext G ⟨d, y⟩)

def dartTransitionStepEquivIncoming {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    DartTransitionStep G ≃ DartIncomingStep G where
  toFun S :=
    let e := dartTransitionNext G S
    ⟨e, ⟨S.1.fst, by
      rw [Finset.mem_erase]
      constructor
      · exact (Finset.mem_erase.mp S.2.2).1.symm
      · rw [SimpleGraph.mem_neighborFinset]
        exact S.1.adj.symm⟩⟩
  invFun T :=
    let d : G.Dart :=
      ⟨(T.2.1, T.1.fst),
        by
          have hmem : T.2.1 ∈ G.neighborFinset T.1.fst :=
            (Finset.mem_erase.mp T.2.2).2
          exact ((SimpleGraph.mem_neighborFinset G T.1.fst T.2.1).mp hmem).symm⟩
    ⟨d, ⟨T.1.snd, by
      rw [Finset.mem_erase]
      constructor
      · exact (Finset.mem_erase.mp T.2.2).1.symm
      · rw [SimpleGraph.mem_neighborFinset]
        exact T.1.adj⟩⟩
  left_inv S := by
    rcases S with ⟨d, y, hy⟩
    ext <;> rfl
  right_inv T := by
    rcases T with ⟨d, y, hy⟩
    ext <;> rfl

theorem sum_dart_transition_stationary {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hdeg : ∀ v : V, 2 ≤ G.degree v) (F : G.Dart → ℝ) :
    (∑ d : G.Dart, dartTransitionAverage G F d) =
      ∑ d : G.Dart, F d := by
  have hstep :
      (∑ S : DartTransitionStep G,
        (((G.degree S.1.snd : ℝ) - 1)⁻¹) *
          F (dartTransitionNext G S)) =
        ∑ T : DartIncomingStep G,
          (((G.degree T.1.fst : ℝ) - 1)⁻¹) * F T.1 := by
    rw [Fintype.sum_equiv (dartTransitionStepEquivIncoming G)
      (fun S : DartTransitionStep G =>
        (((G.degree S.1.snd : ℝ) - 1)⁻¹) *
          F (dartTransitionNext G S))
      (fun T : DartIncomingStep G =>
        (((G.degree T.1.fst : ℝ) - 1)⁻¹) * F T.1)
      (by
        intro S
        rfl)]
  calc
    (∑ d : G.Dart, dartTransitionAverage G F d)
        =
        ∑ S : DartTransitionStep G,
          (((G.degree S.1.snd : ℝ) - 1)⁻¹) *
            F (dartTransitionNext G S) := by
      rw [Fintype.sum_sigma]
      rfl
    _ = ∑ T : DartIncomingStep G,
          (((G.degree T.1.fst : ℝ) - 1)⁻¹) * F T.1 := hstep
    _ = ∑ d : G.Dart, ∑ y : DartIncomingChoice G d,
          (((G.degree d.fst : ℝ) - 1)⁻¹) * F d := by
      rw [Fintype.sum_sigma]
    _ = ∑ d : G.Dart, F d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hmem : d.snd ∈ G.neighborFinset d.fst := by
        rw [SimpleGraph.mem_neighborFinset]
        exact d.adj
      have hcard :
          Fintype.card (DartIncomingChoice G d) = G.degree d.fst - 1 := by
        dsimp [DartIncomingChoice]
        rw [Fintype.card_coe]
        rw [Finset.card_erase_of_mem hmem]
        rw [SimpleGraph.card_neighborFinset_eq_degree]
      have hdeg_one : 1 ≤ G.degree d.fst := by
        have htwo := hdeg d.fst
        omega
      have hcast : ((G.degree d.fst - 1 : ℕ) : ℝ) =
          (G.degree d.fst : ℝ) - 1 := by
        rw [Nat.cast_sub hdeg_one]
        norm_num
      have hpos : 0 < (G.degree d.fst : ℝ) - 1 := by
        have h : (2 : ℝ) ≤ (G.degree d.fst : ℝ) := by
          exact_mod_cast hdeg d.fst
        linarith
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_univ, hcard, hcast]
      rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

theorem dart_card_mul_sum_ahlN_range_eq {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {k : ℕ}
    (hD : Fintype.card G.Dart ≠ 0) :
    (Fintype.card G.Dart : ℝ) * (∑ i ∈ Finset.range k, ahlN G i) =
      ∑ d : G.Dart, ∑ i ∈ Finset.range k,
        (Nat.card (AhlDartContinuation G d i) : ℝ) := by
  have hDreal : (Fintype.card G.Dart : ℝ) ≠ 0 := by exact_mod_cast hD
  rw [Finset.mul_sum]
  calc
    ∑ i ∈ Finset.range k, (Fintype.card G.Dart : ℝ) * ahlN G i =
        ∑ i ∈ Finset.range k,
          ∑ d : G.Dart, (Nat.card (AhlDartContinuation G d i) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [ahlN]
      field_simp [hDreal]
    _ = ∑ d : G.Dart, ∑ i ∈ Finset.range k,
          (Nat.card (AhlDartContinuation G d i) : ℝ) := by
      rw [Finset.sum_comm]

theorem sum_reverse_avoidingPathAtMost_eq {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (r : ℕ) :
    (∑ d : G.Dart,
        (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 r) : ℝ)) =
      ∑ d : G.Dart,
        (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) : ℝ) := by
  simpa using
    (sum_dart_symm G
      (fun d : G.Dart =>
        (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) : ℝ)))

theorem finite_ahlDartContinuation {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (d : G.Dart) (hsmall : l + l < g) :
    Finite (AhlDartContinuation G d l) :=
  finite_avoidingPathOfLength
    (avoiding_endpoint_injective (G := G) hg (z := d.toProd.2)
      (forbidden := d.toProd.1) hsmall)

@[reducible]
noncomputable def ahlDartContinuationFintype {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (d : G.Dart) (hsmall : l + l < g) :
    Fintype (AhlDartContinuation G d l) :=
  letI : Finite (AhlDartContinuation G d l) :=
    finite_ahlDartContinuation (G := G) hg d hsmall
  Fintype.ofFinite (AhlDartContinuation G d l)

theorem sum_ahlContinuationWeight_eq_one_of_girth {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {d : G.Dart}
    (hsmall : l + l < g)
    (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    letI : Fintype (AhlDartContinuation G d l) :=
      ahlDartContinuationFintype (G := G) hg d hsmall
    ∑ A : AhlDartContinuation G d l, ahlContinuationWeight G A = 1 := by
  induction l with
  | zero =>
      letI : Fintype (AhlDartContinuation G d 0) :=
        ahlDartContinuationFintype (G := G) hg d hsmall
      exact sum_ahlContinuationWeight_zero (d := d) G
  | succ m ih =>
      have hm : m + m < g := by omega
      letI : Fintype (AhlDartContinuation G d m) :=
        ahlDartContinuationFintype (G := G) hg d hm
      letI : Fintype (AhlDartContinuation G d (m + 1)) :=
        ahlDartContinuationFintype (G := G) hg d hsmall
      exact sum_ahlContinuationWeight_succ (d := d) G hg (by omega) hsmall hdeg
        (ih hm)

theorem ahl_amgm_lower_of_girth {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (hsmall : l + l < g)
    (hD : Fintype.card G.Dart ≠ 0)
    (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d l) :=
      fun d => ahlDartContinuationFintype (G := G) hg d hsmall
    (∏ X : AhlAllContinuations G l,
        ahlGlobalInvWeight G X ^ ahlGlobalWeight G X) ≤ ahlN G l := by
  letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d l) :=
    fun d => ahlDartContinuationFintype (G := G) hg d hsmall
  exact ahl_amgm_lower_of_probabilities G hD hdeg
    (fun d => sum_ahlContinuationWeight_eq_one_of_girth G hg hsmall hdeg)

theorem ahl_current_dart_stationary {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (hsmall : l + l < g)
    (hdeg : ∀ v : V, 2 ≤ G.degree v) (F : G.Dart → ℝ) :
    letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d l) :=
      fun d => ahlDartContinuationFintype (G := G) hg d hsmall
    ∑ X : AhlAllContinuations G l,
        ahlGlobalWeight G X * F (ahlContinuationCurrentDart G X.2) =
      (Fintype.card G.Dart : ℝ)⁻¹ * ∑ d : G.Dart, F d := by
  induction l generalizing F with
  | zero =>
      letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d 0) :=
        fun d => ahlDartContinuationFintype (G := G) hg d hsmall
      calc
        ∑ X : AhlAllContinuations G 0,
            ahlGlobalWeight G X * F (ahlContinuationCurrentDart G X.2)
            =
            ∑ d : G.Dart, ∑ A : AhlDartContinuation G d 0,
              ((Fintype.card G.Dart : ℝ)⁻¹ * ahlContinuationWeight G A) * F d := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro A hA
          rw [ahlContinuationCurrentDart_zero G A]
          rfl
        _ = ∑ d : G.Dart, (Fintype.card G.Dart : ℝ)⁻¹ * F d := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Fintype.sum_equiv (ahlDartContinuationZeroEquiv G d)
            (fun A : AhlDartContinuation G d 0 =>
              ((Fintype.card G.Dart : ℝ)⁻¹ * ahlContinuationWeight G A) * F d)
            (fun _ : Unit => (Fintype.card G.Dart : ℝ)⁻¹ * F d)
            (by
              intro A
              simpa [ahlContinuationWeight_zero G A, mul_assoc])]
          simp
        _ = (Fintype.card G.Dart : ℝ)⁻¹ * ∑ d : G.Dart, F d := by
          rw [Finset.mul_sum]
  | succ m ih =>
      have hm : m + m < g := by omega
      have hshort : m + 1 < g := by omega
      letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d m) :=
        fun d => ahlDartContinuationFintype (G := G) hg d hm
      letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d (m + 1)) :=
        fun d => ahlDartContinuationFintype (G := G) hg d hsmall
      have hih := ih hm (dartTransitionAverage G F)
      calc
        ∑ X : AhlAllContinuations G (m + 1),
            ahlGlobalWeight G X * F (ahlContinuationCurrentDart G X.2)
            =
            ∑ d : G.Dart, ∑ B : AhlDartContinuation G d (m + 1),
              ahlGlobalWeight G ⟨d, B⟩ * F (ahlContinuationCurrentDart G B) := by
          rw [Fintype.sum_sigma]
        _ =
            ∑ d : G.Dart,
              ∑ S : Σ A : AhlDartContinuation G d m,
                  AhlContinuationExtensionChoice G A,
                ahlGlobalWeight G
                    ⟨d, ahlContinuationExtend G hg hshort S.1 S.2⟩ *
                  F (ahlContinuationCurrentDart G
                    (ahlContinuationExtend G hg hshort S.1 S.2)) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [← Fintype.sum_equiv
            (ahlContinuationExtensionEquiv G hg hshort
              (by simpa [Nat.succ_eq_add_one] using hsmall) (d := d))
            (fun S : Σ A : AhlDartContinuation G d m,
                AhlContinuationExtensionChoice G A =>
              ahlGlobalWeight G
                  ⟨d, ahlContinuationExtend G hg hshort S.1 S.2⟩ *
                F (ahlContinuationCurrentDart G
                  (ahlContinuationExtend G hg hshort S.1 S.2)))
            (fun B : AhlDartContinuation G d (m + 1) =>
              ahlGlobalWeight G ⟨d, B⟩ * F (ahlContinuationCurrentDart G B))
            (by intro S; rfl)]
        _ =
            ∑ d : G.Dart, ∑ A : AhlDartContinuation G d m,
              ahlGlobalWeight G ⟨d, A⟩ *
                dartTransitionAverage G F (ahlContinuationCurrentDart G A) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro A hA
          calc
            ∑ Y : AhlContinuationExtensionChoice G A,
                ahlGlobalWeight G
                    ⟨d, ahlContinuationExtend G hg hshort A Y⟩ *
                  F (ahlContinuationCurrentDart G
                    (ahlContinuationExtend G hg hshort A Y))
                =
                ∑ Y : AhlContinuationExtensionChoice G A,
                  ahlGlobalWeight G ⟨d, A⟩ *
                    (((G.degree A.1 : ℝ) - 1)⁻¹ *
                      F (dartTransitionNext G ⟨ahlContinuationCurrentDart G A, Y⟩)) := by
              apply Finset.sum_congr rfl
              intro Y hY
              dsimp [ahlGlobalWeight]
              rw [ahlContinuationExtend_weight G hg hshort A Y]
              rw [ahlContinuationCurrentDart_extend G hg hshort A Y]
              dsimp [dartTransitionNext, ahlContinuationCurrentDart]
              ring
            _ =
                ahlGlobalWeight G ⟨d, A⟩ *
                  ∑ Y : AhlContinuationExtensionChoice G A,
                    (((G.degree A.1 : ℝ) - 1)⁻¹ *
                      F (dartTransitionNext G ⟨ahlContinuationCurrentDart G A, Y⟩)) := by
              rw [Finset.mul_sum]
            _ =
                ahlGlobalWeight G ⟨d, A⟩ *
                  dartTransitionAverage G F (ahlContinuationCurrentDart G A) := by
              rfl
        _ =
            ∑ X : AhlAllContinuations G m,
              ahlGlobalWeight G X *
                dartTransitionAverage G F (ahlContinuationCurrentDart G X.2) := by
          rw [Fintype.sum_sigma]
        _ = (Fintype.card G.Dart : ℝ)⁻¹ *
            ∑ d : G.Dart, dartTransitionAverage G F d := hih
        _ = (Fintype.card G.Dart : ℝ)⁻¹ * ∑ d : G.Dart, F d := by
          rw [sum_dart_transition_stationary G hdeg F]

theorem dart_average_log_degree_sub_one_eq_ahlLogLambda {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    (Fintype.card G.Dart : ℝ)⁻¹ *
        ∑ d : G.Dart, Real.log ((G.degree d.snd : ℝ) - 1) =
      ahlLogLambda G := by
  let S : ℝ := ∑ v : V, (G.degree v : ℝ)
  have hDsum : (Fintype.card G.Dart : ℝ) = S := by
    dsimp [S]
    exact_mod_cast SimpleGraph.dart_card_eq_sum_degrees G
  have hcard_pos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hS_pos : 0 < S := by
    dsimp [S]
    rcases ‹Nonempty V› with ⟨v⟩
    exact Finset.sum_pos'
      (fun w hw => by
        exact Nat.cast_nonneg (G.degree w))
      ⟨v, Finset.mem_univ v, by
      have hv : (2 : ℝ) ≤ (G.degree v : ℝ) := by
        exact_mod_cast hdeg v
      linarith⟩
  have hcoeff :
      S⁻¹ = (((average_degree G : ℚ) : ℝ))⁻¹ * (Fintype.card V : ℝ)⁻¹ := by
    rw [average_degree_real_eq_inv_card_mul_sum_degrees G]
    change S⁻¹ = (((Fintype.card V : ℝ)⁻¹ * S))⁻¹ *
      (Fintype.card V : ℝ)⁻¹
    field_simp [hcard_pos.ne', hS_pos.ne']
  calc
    (Fintype.card G.Dart : ℝ)⁻¹ *
        ∑ d : G.Dart, Real.log ((G.degree d.snd : ℝ) - 1)
        =
        S⁻¹ *
          ∑ v : V, (G.degree v : ℝ) *
            Real.log ((G.degree v : ℝ) - 1) := by
      rw [hDsum]
      rw [sum_dart_snd_real G (fun v : V =>
        Real.log ((G.degree v : ℝ) - 1))]
    _ = ahlLogLambda G := by
      dsimp [ahlLogLambda, ahlPhi]
      rw [hcoeff]
      ring

theorem ahlLogGeom_succ_eq {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    {g m : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (hsmall : (m + 1) + (m + 1) < g)
    (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d m) :=
      fun d => ahlDartContinuationFintype (G := G) hg d (by omega)
    letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d (m + 1)) :=
      fun d => ahlDartContinuationFintype (G := G) hg d hsmall
    ahlLogGeom (l := m + 1) G =
      ahlLogGeom (l := m) G + ahlLogLambda G := by
  have hm : m + m < g := by omega
  have hshort : m + 1 < g := by omega
  letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d m) :=
    fun d => ahlDartContinuationFintype (G := G) hg d hm
  letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d (m + 1)) :=
    fun d => ahlDartContinuationFintype (G := G) hg d hsmall
  have hstationary :
      ∑ X : AhlAllContinuations G m,
          ahlGlobalWeight G X *
            Real.log ((G.degree (ahlContinuationCurrentDart G X.2).snd : ℝ) - 1) =
        ahlLogLambda G := by
    calc
      ∑ X : AhlAllContinuations G m,
          ahlGlobalWeight G X *
            Real.log ((G.degree (ahlContinuationCurrentDart G X.2).snd : ℝ) - 1)
          =
          (Fintype.card G.Dart : ℝ)⁻¹ *
            ∑ d : G.Dart, Real.log ((G.degree d.snd : ℝ) - 1) := by
        simpa using
          ahl_current_dart_stationary G hg hm hdeg
            (fun d : G.Dart => Real.log ((G.degree d.snd : ℝ) - 1))
      _ = ahlLogLambda G :=
        dart_average_log_degree_sub_one_eq_ahlLogLambda G hdeg
  calc
    ahlLogGeom (l := m + 1) G
        =
        ∑ d : G.Dart, ∑ B : AhlDartContinuation G d (m + 1),
          ahlGlobalWeight G ⟨d, B⟩ *
            Real.log (ahlGlobalInvWeight G ⟨d, B⟩) := by
      dsimp [ahlLogGeom]
      rw [Fintype.sum_sigma]
    _ =
        ∑ d : G.Dart,
          ∑ S : Σ A : AhlDartContinuation G d m,
              AhlContinuationExtensionChoice G A,
            ahlGlobalWeight G
                ⟨d, ahlContinuationExtend G hg hshort S.1 S.2⟩ *
              Real.log (ahlGlobalInvWeight G
                ⟨d, ahlContinuationExtend G hg hshort S.1 S.2⟩) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Fintype.sum_equiv
        (ahlContinuationExtensionEquiv G hg hshort hsmall (d := d))
        (fun S : Σ A : AhlDartContinuation G d m,
            AhlContinuationExtensionChoice G A =>
          ahlGlobalWeight G
              ⟨d, ahlContinuationExtend G hg hshort S.1 S.2⟩ *
            Real.log (ahlGlobalInvWeight G
              ⟨d, ahlContinuationExtend G hg hshort S.1 S.2⟩))
        (fun B : AhlDartContinuation G d (m + 1) =>
          ahlGlobalWeight G ⟨d, B⟩ *
            Real.log (ahlGlobalInvWeight G ⟨d, B⟩))
        (by intro S; rfl)]
    _ =
        ∑ d : G.Dart, ∑ A : AhlDartContinuation G d m,
          (ahlGlobalWeight G ⟨d, A⟩ *
              Real.log (ahlGlobalInvWeight G ⟨d, A⟩) +
            ahlGlobalWeight G ⟨d, A⟩ *
              Real.log ((G.degree (ahlContinuationCurrentDart G A).snd : ℝ) - 1)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro A hA
      simpa [ahlContinuationCurrentDart] using
        sum_extension_globalWeight_logInvWeight G hg hshort hdeg A
    _ =
        (∑ d : G.Dart, ∑ A : AhlDartContinuation G d m,
          ahlGlobalWeight G ⟨d, A⟩ *
            Real.log (ahlGlobalInvWeight G ⟨d, A⟩)) +
        (∑ d : G.Dart, ∑ A : AhlDartContinuation G d m,
          ahlGlobalWeight G ⟨d, A⟩ *
            Real.log ((G.degree (ahlContinuationCurrentDart G A).snd : ℝ) - 1)) := by
      calc
        ∑ d : G.Dart, ∑ A : AhlDartContinuation G d m,
          (ahlGlobalWeight G ⟨d, A⟩ *
              Real.log (ahlGlobalInvWeight G ⟨d, A⟩) +
            ahlGlobalWeight G ⟨d, A⟩ *
              Real.log ((G.degree (ahlContinuationCurrentDart G A).snd : ℝ) - 1))
            =
            ∑ d : G.Dart,
              ((∑ A : AhlDartContinuation G d m,
                ahlGlobalWeight G ⟨d, A⟩ *
                  Real.log (ahlGlobalInvWeight G ⟨d, A⟩)) +
              ∑ A : AhlDartContinuation G d m,
                ahlGlobalWeight G ⟨d, A⟩ *
                  Real.log ((G.degree (ahlContinuationCurrentDart G A).snd : ℝ) - 1)) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_add_distrib]
        _ =
            (∑ d : G.Dart, ∑ A : AhlDartContinuation G d m,
              ahlGlobalWeight G ⟨d, A⟩ *
                Real.log (ahlGlobalInvWeight G ⟨d, A⟩)) +
            (∑ d : G.Dart, ∑ A : AhlDartContinuation G d m,
              ahlGlobalWeight G ⟨d, A⟩ *
                Real.log ((G.degree (ahlContinuationCurrentDart G A).snd : ℝ) - 1)) := by
          rw [Finset.sum_add_distrib]
    _ = ahlLogGeom (l := m) G + ahlLogLambda G := by
      rw [← hstationary]
      congr 1
      dsimp [ahlLogGeom]
      rw [Fintype.sum_sigma]
      rw [Fintype.sum_sigma]

theorem ahlLogGeom_eq_nat_mul_ahlLogLambda {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (hsmall : l + l < g)
    (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d l) :=
      fun d => ahlDartContinuationFintype (G := G) hg d hsmall
    ahlLogGeom (l := l) G = (l : ℝ) * ahlLogLambda G := by
  induction l with
  | zero =>
      letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d 0) :=
        fun d => ahlDartContinuationFintype (G := G) hg d hsmall
      calc
        ahlLogGeom (l := 0) G = 0 := by
          dsimp [ahlLogGeom]
          rw [Fintype.sum_sigma]
          apply Finset.sum_eq_zero
          intro d hd
          apply Finset.sum_eq_zero
          intro A hA
          simp [ahlGlobalInvWeight, ahlContinuationInvWeight_zero G A]
        _ = ((0 : ℕ) : ℝ) * ahlLogLambda G := by
          rw [Nat.cast_zero]
          simp
  | succ m ih =>
      have hm : m + m < g := by omega
      letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d m) :=
        fun d => ahlDartContinuationFintype (G := G) hg d hm
      letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d (m + 1)) :=
        fun d => ahlDartContinuationFintype (G := G) hg d hsmall
      calc
        ahlLogGeom (l := m + 1) G =
            ahlLogGeom (l := m) G + ahlLogLambda G := by
          exact ahlLogGeom_succ_eq G hg hsmall hdeg
        _ = (m : ℝ) * ahlLogLambda G + ahlLogLambda G := by
          rw [ih hm]
        _ = ((m + 1 : ℕ) : ℝ) * ahlLogLambda G := by
          rw [Nat.cast_add, Nat.cast_one]
          ring

theorem ahlLambda_pow_le_ahlN {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    {g l : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (hsmall : l + l < g)
    (hD : Fintype.card G.Dart ≠ 0)
    (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d l) :=
      fun d => ahlDartContinuationFintype (G := G) hg d hsmall
    ahlLambda G ^ l ≤ ahlN G l := by
  letI : ∀ d : G.Dart, Fintype (AhlDartContinuation G d l) :=
    fun d => ahlDartContinuationFintype (G := G) hg d hsmall
  have hgeom := ahlLogGeom_eq_nat_mul_ahlLogLambda G hg hsmall hdeg
  have hAMGM :
      Real.exp (ahlLogGeom (l := l) G) ≤ ahlN G l := by
    exact ahl_exp_logGeom_le_ahlN_of_probabilities G hD hdeg
      (fun d => sum_ahlContinuationWeight_eq_one_of_girth G hg hsmall hdeg)
  calc
    ahlLambda G ^ l = Real.exp ((l : ℝ) * ahlLogLambda G) := by
      dsimp [ahlLambda]
      exact (Real.exp_nat_mul (ahlLogLambda G) l).symm
    _ = Real.exp (ahlLogGeom (l := l) G) := by
      rw [hgeom]
    _ ≤ ahlN G l := hAMGM

theorem one_add_mul_geom_sum_eq_sum_succ (x : ℝ) (r : ℕ) :
    1 + x * (∑ i ∈ Finset.range r, x ^ i) =
      ∑ i ∈ Finset.range (r + 1), x ^ i := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [← ih]
      rw [mul_add]
      rw [pow_succ']
      ring

theorem n0_odd_eq_ahl_sum (x : ℝ) (r : ℕ) :
    n0 (x + 1) (2 * r + 1) =
      (∑ i ∈ Finset.range (r + 1), x ^ i) +
        ∑ i ∈ Finset.range r, x ^ i := by
  have hodd : Odd (2 * r + 1) := by
    exact ⟨r, by ring⟩
  have hdiv : (2 * r + 1) / 2 = r := by omega
  dsimp [n0]
  rw [if_pos hodd]
  rw [hdiv]
  have hsub : x + 1 - 1 = x := by ring
  rw [hsub]
  calc
    1 + (x + 1) * (∑ i ∈ Finset.range r, x ^ i)
        =
        (1 + x * (∑ i ∈ Finset.range r, x ^ i)) +
          ∑ i ∈ Finset.range r, x ^ i := by
      ring
    _ =
        (∑ i ∈ Finset.range (r + 1), x ^ i) +
          ∑ i ∈ Finset.range r, x ^ i := by
      rw [one_add_mul_geom_sum_eq_sum_succ]

theorem n0_even_eq_ahl_sum (x : ℝ) (r : ℕ) :
    n0 (x + 1) (2 * r) =
      2 * (∑ i ∈ Finset.range r, x ^ i) := by
  have heven_not_odd : ¬ Odd (2 * r) := by
    exact Nat.not_odd_iff_even.mpr ⟨r, by ring⟩
  have hdiv : (2 * r) / 2 = r := by omega
  dsimp [n0]
  rw [if_neg heven_not_odd]
  rw [hdiv]
  have hsub : x + 1 - 1 = x := by ring
  rw [hsub]

theorem dart_card_ne_zero_of_minDegree_two {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    Fintype.card G.Dart ≠ 0 := by
  rw [SimpleGraph.dart_card_eq_sum_degrees G]
  apply ne_of_gt
  rcases ‹Nonempty V› with ⟨v⟩
  exact Finset.sum_pos'
    (fun w hw => Nat.zero_le (G.degree w))
    ⟨v, Finset.mem_univ v, by
      have hv := hdeg v
      omega⟩

theorem sum_ahlLambda_pow_le_sum_ahlN_range {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    {g k : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (hD : Fintype.card G.Dart ≠ 0)
    (hdeg : ∀ v : V, 2 ≤ G.degree v)
    (hsmall : ∀ i ∈ Finset.range k, i + i < g) :
    (∑ i ∈ Finset.range k, ahlLambda G ^ i) ≤
      ∑ i ∈ Finset.range k, ahlN G i := by
  apply Finset.sum_le_sum
  intro i hi
  exact ahlLambda_pow_le_ahlN G hg (hsmall i hi) hD hdeg

theorem finite_avoidingPathOfLengthAtMost_of_girth {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {z forbidden : V} (hsmall : r + r < g) :
    Finite (AvoidingPathOfLengthAtMost G z forbidden r) := by
  exact @Finite.instSigma {n : ℕ // n ≤ r}
    (fun n => AvoidingPathOfLength G z forbidden n.1)
    inferInstance
    (fun n =>
      finite_avoidingPathOfLength
        (avoiding_endpoint_injective (G := G) hg (z := z)
          (forbidden := forbidden) (by omega)))

theorem ahlDartContinuationAtMost_card_eq_sum {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (d : G.Dart) (hsmall : r + r < g) :
    Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) =
      ∑ n : {n : ℕ // n ≤ r}, Nat.card (AhlDartContinuation G d n.1) := by
  letI : ∀ n : {n : ℕ // n ≤ r}, Finite (AhlDartContinuation G d n.1) := fun n =>
    finite_ahlDartContinuation (G := G) hg d (by omega)
  exact Nat.card_sigma

theorem ahlDartContinuationAtMost_card_eq_range_sum {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (d : G.Dart) (hsmall : r + r < g) :
    Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) =
      ∑ n ∈ Finset.range (r + 1), Nat.card (AhlDartContinuation G d n) := by
  rw [ahlDartContinuationAtMost_card_eq_sum (G := G) hg d hsmall]
  rw [Fintype.sum_equiv (leNatSubtypeEquivFin r)
    (fun n : {n : ℕ // n ≤ r} => Nat.card (AhlDartContinuation G d n.1))
    (fun n : Fin (r + 1) => Nat.card (AhlDartContinuation G d (n : ℕ)))
    (by intro n; rfl)]
  exact Fin.sum_univ_eq_sum_range
    (fun n => Nat.card (AhlDartContinuation G d n)) (r + 1)

theorem ahl_odd_fixed_dart_row_sum_le_card {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (d : G.Dart) (hrpos : 0 < r) (hsmall : r + r < g) :
    (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) +
        Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 (r - 1)) : ℕ) ≤
      Nat.card V := by
  have hroot := dartRootAvoidingOddAtMost_card_le_vertices (G := G) hg d hrpos hsmall
  have hcard :
      Nat.card (DartRootAvoidingOddAtMost G d r) =
        Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) +
          Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 (r - 1)) := by
    letI : Finite (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) :=
      finite_avoidingPathOfLengthAtMost_of_girth (G := G) hg hsmall
    letI : Finite (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 (r - 1)) :=
      finite_avoidingPathOfLengthAtMost_of_girth (G := G) hg (by omega)
    exact Nat.card_sum
  rwa [DartRootAvoidingOddAtMost, EdgeRootAtMostAsym, hcard] at hroot

theorem ahl_odd_scaled_upper {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (hD : Fintype.card G.Dart ≠ 0) (hrpos : 0 < r) (hsmall : r + r < g) :
    (Fintype.card G.Dart : ℝ) *
        ((∑ i ∈ Finset.range (r + 1), ahlN G i) +
          ∑ i ∈ Finset.range r, ahlN G i) ≤
      (Fintype.card G.Dart : ℝ) * (Fintype.card V : ℝ) := by
  have hfirst :
      (∑ d : G.Dart, ∑ i ∈ Finset.range (r + 1),
          (Nat.card (AhlDartContinuation G d i) : ℝ)) =
        ∑ d : G.Dart,
          (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hnat := ahlDartContinuationAtMost_card_eq_range_sum (G := G) hg d hsmall
    exact_mod_cast hnat.symm
  have hsecond_forward :
      (∑ d : G.Dart, ∑ i ∈ Finset.range r,
          (Nat.card (AhlDartContinuation G d i) : ℝ)) =
        ∑ d : G.Dart,
          (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 (r - 1)) : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hnat :
        Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 (r - 1)) =
          ∑ i ∈ Finset.range r, Nat.card (AhlDartContinuation G d i) := by
      simpa [Nat.sub_add_cancel hrpos] using
        ahlDartContinuationAtMost_card_eq_range_sum (G := G) hg d (by omega : (r - 1) + (r - 1) < g)
    exact_mod_cast hnat.symm
  have hsecond :
      (∑ d : G.Dart, ∑ i ∈ Finset.range r,
          (Nat.card (AhlDartContinuation G d i) : ℝ)) =
        ∑ d : G.Dart,
          (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 (r - 1)) : ℝ) := by
    rw [hsecond_forward]
    exact (sum_reverse_avoidingPathAtMost_eq G (r - 1)).symm
  have hrows :
      (∑ d : G.Dart,
          ((Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) +
            Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 (r - 1))) : ℝ)) ≤
        ∑ d : G.Dart, (Fintype.card V : ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    have hnat :
        (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) +
            Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 (r - 1)) : ℕ) ≤
          Fintype.card V := by
      simpa [Nat.card_eq_fintype_card] using
        ahl_odd_fixed_dart_row_sum_le_card (G := G) hg d hrpos hsmall
    exact_mod_cast hnat
  calc
    (Fintype.card G.Dart : ℝ) *
        ((∑ i ∈ Finset.range (r + 1), ahlN G i) +
          ∑ i ∈ Finset.range r, ahlN G i)
        =
        (∑ d : G.Dart,
          ∑ i ∈ Finset.range (r + 1),
            (Nat.card (AhlDartContinuation G d i) : ℝ)) +
          ∑ d : G.Dart,
            ∑ i ∈ Finset.range r,
              (Nat.card (AhlDartContinuation G d i) : ℝ) := by
      rw [mul_add]
      rw [dart_card_mul_sum_ahlN_range_eq G hD]
      rw [dart_card_mul_sum_ahlN_range_eq G hD]
    _ =
        (∑ d : G.Dart,
          (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) : ℝ)) +
          ∑ d : G.Dart,
            (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 (r - 1)) : ℝ) := by
      rw [hfirst, hsecond]
    _ =
        ∑ d : G.Dart,
          ((Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) +
            Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 (r - 1))) : ℝ) := by
      rw [Finset.sum_add_distrib]
    _ ≤ ∑ d : G.Dart, (Fintype.card V : ℝ) := hrows
    _ = (Fintype.card G.Dart : ℝ) * (Fintype.card V : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]

theorem ahl_even_fixed_dart_row_sum_le_card {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (d : G.Dart) (hsmall : r + r < g) (hcross : r + (r + 1) < g) :
    (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) +
        Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 r) : ℕ) ≤
      Nat.card V := by
  have hroot := dartRootAvoidingAtMost_card_le_vertices (G := G) hg d hsmall hcross
  have hcard :
      Nat.card (DartRootAvoidingAtMost G d r) =
        Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) +
          Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 r) := by
    letI : Finite (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) :=
      finite_avoidingPathOfLengthAtMost_of_girth (G := G) hg hsmall
    letI : Finite (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 r) :=
      finite_avoidingPathOfLengthAtMost_of_girth (G := G) hg hsmall
    exact Nat.card_sum
  rwa [DartRootAvoidingAtMost, hcard] at hroot

theorem ahl_even_scaled_upper {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (hD : Fintype.card G.Dart ≠ 0) (hsmall : r + r < g)
    (hcross : r + (r + 1) < g) :
    (Fintype.card G.Dart : ℝ) *
        ((∑ i ∈ Finset.range (r + 1), ahlN G i) +
          ∑ i ∈ Finset.range (r + 1), ahlN G i) ≤
      (Fintype.card G.Dart : ℝ) * (Fintype.card V : ℝ) := by
  have hfirst :
      (∑ d : G.Dart, ∑ i ∈ Finset.range (r + 1),
          (Nat.card (AhlDartContinuation G d i) : ℝ)) =
        ∑ d : G.Dart,
          (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hnat := ahlDartContinuationAtMost_card_eq_range_sum (G := G) hg d hsmall
    exact_mod_cast hnat.symm
  have hsecond :
      (∑ d : G.Dart, ∑ i ∈ Finset.range (r + 1),
          (Nat.card (AhlDartContinuation G d i) : ℝ)) =
        ∑ d : G.Dart,
          (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 r) : ℝ) := by
    rw [hfirst]
    exact (sum_reverse_avoidingPathAtMost_eq G r).symm
  have hrows :
      (∑ d : G.Dart,
          ((Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) +
            Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 r)) : ℝ)) ≤
        ∑ d : G.Dart, (Fintype.card V : ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    have hnat :
        (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) +
            Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 r) : ℕ) ≤
          Fintype.card V := by
      simpa [Nat.card_eq_fintype_card] using
        ahl_even_fixed_dart_row_sum_le_card (G := G) hg d hsmall hcross
    exact_mod_cast hnat
  calc
    (Fintype.card G.Dart : ℝ) *
        ((∑ i ∈ Finset.range (r + 1), ahlN G i) +
          ∑ i ∈ Finset.range (r + 1), ahlN G i)
        =
        (∑ d : G.Dart,
          ∑ i ∈ Finset.range (r + 1),
            (Nat.card (AhlDartContinuation G d i) : ℝ)) +
          ∑ d : G.Dart,
            ∑ i ∈ Finset.range (r + 1),
              (Nat.card (AhlDartContinuation G d i) : ℝ) := by
      rw [mul_add]
      rw [dart_card_mul_sum_ahlN_range_eq G hD]
    _ =
        (∑ d : G.Dart,
          (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) : ℝ)) +
          ∑ d : G.Dart,
            (Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 r) : ℝ) := by
      conv_lhs =>
        congr
        · rw [hfirst]
        · rw [hsecond]
    _ =
        ∑ d : G.Dart,
          ((Nat.card (AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r) +
            Nat.card (AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 r)) : ℝ) := by
      rw [Finset.sum_add_distrib]
    _ ≤ ∑ d : G.Dart, (Fintype.card V : ℝ) := hrows
    _ = (Fintype.card G.Dart : ℝ) * (Fintype.card V : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]

theorem ahl_moore_bound_minDegree_two {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    n0 (ahlLambda G + 1) g ≤ (Fintype.card V : ℝ) := by
  let D : ℝ := Fintype.card G.Dart
  have hD : Fintype.card G.Dart ≠ 0 :=
    dart_card_ne_zero_of_minDegree_two G hdeg
  have hDpos : 0 < D := by
    dsimp [D]
    exact_mod_cast Nat.pos_of_ne_zero hD
  by_cases hodd : Odd g
  · let r := g / 2
    have hg_eq : g = 2 * r + 1 := by
      rcases hodd with ⟨k, hk⟩
      dsimp [r]
      rw [hk]
      omega
    by_cases hr0 : r = 0
    · have hn0 : n0 (ahlLambda G + 1) g = 1 := by
        rw [hg_eq, hr0]
        rw [n0_odd_eq_ahl_sum]
        simp
      rw [hn0]
      exact_mod_cast Fintype.card_pos
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      have hsmall : r + r < g := by
        rw [hg_eq]
        omega
      have hupper :=
        ahl_odd_scaled_upper G hg hD hrpos hsmall
      have hlow₁ :
          (∑ i ∈ Finset.range (r + 1), ahlLambda G ^ i) ≤
            ∑ i ∈ Finset.range (r + 1), ahlN G i := by
        apply sum_ahlLambda_pow_le_sum_ahlN_range G hg hD hdeg
        intro i hi
        have hi_lt : i < r + 1 := Finset.mem_range.mp hi
        rw [hg_eq]
        omega
      have hlow₂ :
          (∑ i ∈ Finset.range r, ahlLambda G ^ i) ≤
            ∑ i ∈ Finset.range r, ahlN G i := by
        apply sum_ahlLambda_pow_le_sum_ahlN_range G hg hD hdeg
        intro i hi
        have hi_lt : i < r := Finset.mem_range.mp hi
        rw [hg_eq]
        omega
      have hlow :
          n0 (ahlLambda G + 1) g ≤
            (∑ i ∈ Finset.range (r + 1), ahlN G i) +
              ∑ i ∈ Finset.range r, ahlN G i := by
        rw [hg_eq]
        rw [n0_odd_eq_ahl_sum]
        exact add_le_add hlow₁ hlow₂
      have hmul_low :
          D * n0 (ahlLambda G + 1) g ≤
            D * ((∑ i ∈ Finset.range (r + 1), ahlN G i) +
              ∑ i ∈ Finset.range r, ahlN G i) :=
        mul_le_mul_of_nonneg_left hlow (le_of_lt hDpos)
      have hchain :
          D * n0 (ahlLambda G + 1) g ≤ D * (Fintype.card V : ℝ) :=
        hmul_low.trans (by simpa [D] using hupper)
      exact (mul_le_mul_iff_of_pos_left hDpos).mp hchain
  · have heven : Even g := Nat.not_odd_iff_even.mp hodd
    let r := g / 2
    have hg_eq : g = 2 * r := by
      rcases heven with ⟨k, hk⟩
      dsimp [r]
      rw [hk]
      omega
    by_cases hr0 : r = 0
    · have hn0 : n0 (ahlLambda G + 1) g = 0 := by
        rw [hg_eq, hr0]
        rw [n0_even_eq_ahl_sum]
        simp
      rw [hn0]
      exact_mod_cast Nat.zero_le (Fintype.card V)
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      let s := r - 1
      have hs_succ : s + 1 = r := by
        dsimp [s]
        omega
      have hsmall : s + s < g := by
        rw [hg_eq]
        dsimp [s]
        omega
      have hcross : s + (s + 1) < g := by
        rw [hg_eq]
        dsimp [s]
        omega
      have hupper :=
        ahl_even_scaled_upper G hg hD hsmall hcross
      have hupper' :
          D * ((∑ i ∈ Finset.range r, ahlN G i) +
              ∑ i ∈ Finset.range r, ahlN G i) ≤
            D * (Fintype.card V : ℝ) := by
        simpa [D, hs_succ] using hupper
      have hlow :
          (∑ i ∈ Finset.range r, ahlLambda G ^ i) ≤
            ∑ i ∈ Finset.range r, ahlN G i := by
        apply sum_ahlLambda_pow_le_sum_ahlN_range G hg hD hdeg
        intro i hi
        have hi_lt : i < r := Finset.mem_range.mp hi
        rw [hg_eq]
        omega
      have hlow_n0 :
          n0 (ahlLambda G + 1) g ≤
            (∑ i ∈ Finset.range r, ahlN G i) +
              ∑ i ∈ Finset.range r, ahlN G i := by
        rw [hg_eq]
        rw [n0_even_eq_ahl_sum]
        have htwice := add_le_add hlow hlow
        have htwo :
            2 * (∑ i ∈ Finset.range r, ahlLambda G ^ i) =
              (∑ i ∈ Finset.range r, ahlLambda G ^ i) +
                ∑ i ∈ Finset.range r, ahlLambda G ^ i := by
          ring
        rwa [htwo]
      have hmul_low :
          D * n0 (ahlLambda G + 1) g ≤
            D * ((∑ i ∈ Finset.range r, ahlN G i) +
              ∑ i ∈ Finset.range r, ahlN G i) :=
        mul_le_mul_of_nonneg_left hlow_n0 (le_of_lt hDpos)
      have hchain :
          D * n0 (ahlLambda G + 1) g ≤ D * (Fintype.card V : ℝ) :=
        hmul_low.trans hupper'
      exact (mul_le_mul_iff_of_pos_left hDpos).mp hchain

end Chapter01
end Diestel
