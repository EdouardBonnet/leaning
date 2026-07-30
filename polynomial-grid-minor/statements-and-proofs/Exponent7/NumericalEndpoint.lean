import «statements-and-proofs».Exponent7.NumericalBounds

/-!
# Conditional exponent-seven numerical endpoint

This file chooses every arithmetic parameter in the global theorem.  The
resulting endpoint has the exact natural-number threshold

`K * target^7 * (log_2 target)^b`.

The theorem remains conditional on one ordinary proof argument,
`CleanMatchingDichotomyStatement reserve`.  No axiom is introduced.
-/

namespace SimpleGraph
namespace Exponent7

universe u

/-- Exact exponent-seven treewidth threshold. -/
def polynomialGridMinorTreewidthBound7
    (K b target : ℕ) : ℕ :=
  K * target ^ 7 * (Nat.log 2 target) ^ b

/-- Constant in the normalized hairy-system size estimate. -/
def exponentSevenHairyConstant (cHair cGrid : ℕ) : ℕ :=
  cHair * (2 ^ 38) * (max 2 cGrid) ^ 50

/-- The binary logarithm of a log-product scale, with the additive one needed
by the local threshold, is still bounded by a constant times the target
logarithm. -/
theorem log_logProductScale_add_one_le7
    (C p : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2 (PolynomialGridMinor.logProductScale C p target) + 1 ≤
      (Nat.clog 2 C + p + 3) * Nat.log 2 target := by
  let L := Nat.log 2 target
  have hL : 1 ≤ L := by
    exact Nat.succ_le_of_lt
      (by
        simpa [L] using
          Nat.log_pos (by decide : 1 < 2) htarget)
  calc
    Nat.log 2 (PolynomialGridMinor.logProductScale C p target) + 1
        ≤ (Nat.clog 2 C + p + 2) * L + 1 :=
      Nat.add_le_add_right
        (by
          simpa [L] using
            PolynomialGridMinor.log_logProductScale_le_clog_const_mul_log
              C p htarget)
        1
    _ ≤ (Nat.clog 2 C + p + 2) * L + L := by
      gcongr
    _ = (Nat.clog 2 C + p + 3) * L := by ring
    _ = (Nat.clog 2 C + p + 3) *
          Nat.log 2 target := rfl

/-- The normalized local width together with the standard hairy-system
length has the expected `n^6 * target` polynomial part. -/
theorem hairy_size7_le_normalized
    (cHair cHairLog cGrid k n target : ℕ)
    (hn : 2 ≤ n) :
    cHair * exponentSevenNormalizedLocalThreshold n target *
        (PolynomialGridMinor.lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog ≤
      exponentSevenHairyConstant cHair cGrid *
        n ^ 6 * target * (Nat.log 2 n + 1) ^ 53 *
        (Nat.log 2 k) ^ cHairLog := by
  have hell :
      PolynomialGridMinor.lengthScale cGrid n ≤
        max 2 cGrid * (Nat.log 2 n + 1) := by
    calc
      PolynomialGridMinor.lengthScale cGrid n
          ≤ PolynomialGridMinor.coarseLengthScale cGrid n :=
        PolynomialGridMinor.lengthScale_le_unrounded cGrid n hn
      _ ≤ max 2 cGrid * Nat.log 2 n :=
        PolynomialGridMinor.coarseLengthScale_le_logarithmic cGrid hn
      _ ≤ max 2 cGrid * (Nat.log 2 n + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  calc
    cHair * exponentSevenNormalizedLocalThreshold n target *
        (PolynomialGridMinor.lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog
        ≤
      cHair *
          ((2 ^ 38) * n ^ 6 * target *
            (Nat.log 2 n + 1) ^ 3) *
        (max 2 cGrid * (Nat.log 2 n + 1)) ^ 50 *
        (Nat.log 2 k) ^ cHairLog := by
          simp only [exponentSevenNormalizedLocalThreshold]
          gcongr
    _ =
      exponentSevenHairyConstant cHair cGrid *
        n ^ 6 * target * (Nat.log 2 n + 1) ^ 53 *
        (Nat.log 2 k) ^ cHairLog := by
      rw [mul_pow]
      have hpow :
          (Nat.log 2 n + 1) ^ 3 *
              (Nat.log 2 n + 1) ^ 50 =
            (Nat.log 2 n + 1) ^ 53 := by
        rw [← pow_add]
      simp only [exponentSevenHairyConstant]
      calc
        cHair *
              ((2 ^ 38) * n ^ 6 * target *
                (Nat.log 2 n + 1) ^ 3) *
            ((max 2 cGrid) ^ 50 *
              (Nat.log 2 n + 1) ^ 50) *
            (Nat.log 2 k) ^ cHairLog
            =
          (cHair * (2 ^ 38) * (max 2 cGrid) ^ 50) *
            n ^ 6 * target *
            ((Nat.log 2 n + 1) ^ 3 *
              (Nat.log 2 n + 1) ^ 50) *
            (Nat.log 2 k) ^ cHairLog := by ring
        _ =
          (cHair * (2 ^ 38) * (max 2 cGrid) ^ 50) *
            n ^ 6 * target *
            (Nat.log 2 n + 1) ^ 53 *
            (Nat.log 2 k) ^ cHairLog := by rw [hpow]

/-- The logarithm of the exponent-seven threshold is linear in the target
logarithm. -/
theorem log_polynomialGridMinorTreewidthBound7_le
    (K b : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2 (polynomialGridMinorTreewidthBound7 K b target) ≤
      (Nat.clog 2 K + 2 * 7 + b) * Nat.log 2 target := by
  have heq :
      polynomialGridMinorTreewidthBound7 K b target =
        PolynomialGridMinor.monomialLogScale K 7 b target := by
    rfl
  rw [heq]
  exact
    PolynomialGridMinor.log_monomialLogScale_le_clog_const_mul_log
      K 7 b htarget

/-- The exponent-seven threshold is nontrivial. -/
theorem polynomialGridMinorTreewidthBound7_gt_one
    {K b target : ℕ} (hK : 1 ≤ K) (htarget : 2 ≤ target) :
    1 < polynomialGridMinorTreewidthBound7 K b target := by
  have hlogPos : 0 < Nat.log 2 target :=
    Nat.log_pos (by decide : 1 < 2) htarget
  have hlog : 1 ≤ (Nat.log 2 target) ^ b :=
    Nat.succ_le_of_lt (Nat.pow_pos hlogPos)
  have ht7 : 2 ≤ target ^ 7 := by
    calc
      2 ≤ 2 ^ 7 := by decide
      _ ≤ target ^ 7 := Nat.pow_le_pow_left htarget 7
  have :
      2 ≤ K * target ^ 7 * (Nat.log 2 target) ^ b := by
    calc
      2 = 1 * 2 * 1 := by norm_num
      _ ≤ K * target ^ 7 * (Nat.log 2 target) ^ b := by
        gcongr
  simpa [polynomialGridMinorTreewidthBound7] using this

/-- The log-product scale pays for the clean-matching reserve after
power-of-two rounding. -/
theorem clean_scale_logProduct_sq_of_coeff
    {reserve C p target : ℕ}
    (htarget : 2 ≤ target)
    (hcoeff : 4 * (20000 * reserve) ≤ C ^ 2) :
    4 * (20000 * (reserve * target ^ 2)) ≤
      (PolynomialGridMinor.logProductScale C p target) ^ 2 := by
  let L := Nat.log 2 target
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have hLP : 1 ≤ (L ^ p) ^ 2 := by
    exact Nat.one_le_pow 2 _ (Nat.one_le_pow p _ (by omega))
  calc
    4 * (20000 * (reserve * target ^ 2))
        = (4 * (20000 * reserve)) * target ^ 2 := by ring
    _ ≤ C ^ 2 * target ^ 2 :=
      Nat.mul_le_mul_right _ hcoeff
    _ ≤ C ^ 2 * target ^ 2 * (L ^ p) ^ 2 :=
      Nat.le_mul_of_pos_right _ hLP
    _ =
      (PolynomialGridMinor.logProductScale C p target) ^ 2 := by
      simp [PolynomialGridMinor.logProductScale, L]
      ring

/-- Coefficient and exponent budgets imply the hairy-system inequality at
the exponent-seven threshold. -/
theorem hairy_large_threshold7_of_coeff
    {cHair cHairLog cGrid C p Dn Dk K b target : ℕ}
    (htarget : 2 ≤ target)
    (hexponent : p * 6 + 53 + cHairLog ≤ b)
    (hcoeff :
      exponentSevenHairyConstant cHair cGrid * C ^ 6 *
        Dn ^ 53 * Dk ^ cHairLog < K) :
    exponentSevenHairyConstant cHair cGrid *
        (PolynomialGridMinor.logProductScale C p target) ^ 6 *
        target *
        (Dn * Nat.log 2 target) ^ 53 *
        (Dk * Nat.log 2 target) ^ cHairLog <
      polynomialGridMinorTreewidthBound7 K b target := by
  let L := Nat.log 2 target
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have htpos : 0 < target := by omega
  have hmultPos : 0 < target ^ 7 * L ^ b :=
    Nat.mul_pos (Nat.pow_pos htpos) (Nat.pow_pos hLpos)
  have hLp6 : (L ^ p) ^ 6 = L ^ (p * 6) := by
    simpa using (Nat.pow_mul L p 6).symm
  have hLcombine :
      L ^ (p * 6) * L ^ 53 * L ^ cHairLog =
        L ^ (p * 6 + 53 + cHairLog) := by
    rw [← pow_add, ← pow_add]
  have hleft :
      exponentSevenHairyConstant cHair cGrid *
          (PolynomialGridMinor.logProductScale C p target) ^ 6 *
          target * (Dn * L) ^ 53 * (Dk * L) ^ cHairLog =
        (exponentSevenHairyConstant cHair cGrid * C ^ 6 *
            Dn ^ 53 * Dk ^ cHairLog) *
          target ^ 7 * L ^ (p * 6 + 53 + cHairLog) := by
    rw [PolynomialGridMinor.logProductScale]
    repeat rw [mul_pow]
    rw [hLp6]
    calc
      exponentSevenHairyConstant cHair cGrid *
            (C ^ 6 * target ^ 6 * L ^ (p * 6)) *
            target * (Dn ^ 53 * L ^ 53) *
            (Dk ^ cHairLog * L ^ cHairLog)
          =
        (exponentSevenHairyConstant cHair cGrid * C ^ 6 *
            Dn ^ 53 * Dk ^ cHairLog) *
          target ^ 7 *
          (L ^ (p * 6) * L ^ 53 * L ^ cHairLog) := by
            ring
      _ =
        (exponentSevenHairyConstant cHair cGrid * C ^ 6 *
            Dn ^ 53 * Dk ^ cHairLog) *
          target ^ 7 * L ^ (p * 6 + 53 + cHairLog) := by
            rw [hLcombine]
  have hpow :
      L ^ (p * 6 + 53 + cHairLog) ≤ L ^ b :=
    Nat.pow_le_pow_right hLpos hexponent
  calc
    exponentSevenHairyConstant cHair cGrid *
        (PolynomialGridMinor.logProductScale C p target) ^ 6 *
        target *
        (Dn * Nat.log 2 target) ^ 53 *
        (Dk * Nat.log 2 target) ^ cHairLog
        =
      (exponentSevenHairyConstant cHair cGrid * C ^ 6 *
          Dn ^ 53 * Dk ^ cHairLog) *
        target ^ 7 * L ^ (p * 6 + 53 + cHairLog) := by
          simpa [L] using hleft
    _ ≤
      (exponentSevenHairyConstant cHair cGrid * C ^ 6 *
          Dn ^ 53 * Dk ^ cHairLog) *
        target ^ 7 * L ^ b := by
          gcongr
    _ < K * target ^ 7 * L ^ b := by
      calc
        (exponentSevenHairyConstant cHair cGrid * C ^ 6 *
            Dn ^ 53 * Dk ^ cHairLog) *
            target ^ 7 * L ^ b
            =
          (exponentSevenHairyConstant cHair cGrid * C ^ 6 *
            Dn ^ 53 * Dk ^ cHairLog) *
            (target ^ 7 * L ^ b) := by ring
        _ < K * (target ^ 7 * L ^ b) :=
          Nat.mul_lt_mul_of_pos_right hcoeff hmultPos
        _ = K * target ^ 7 * L ^ b := by ring
    _ = polynomialGridMinorTreewidthBound7 K b target := by
      simp [polynomialGridMinorTreewidthBound7, L]

/-- Fully explicit numerical parameters consumed by the global graph
theorem. -/
structure ParameterChoice7
    (cHair cHairLog cGrid reserve target tw : ℕ) where
  ell : ℕ
  w : ℕ
  k : ℕ
  q : ℕ
  ell_gt_one : 1 < ell
  w_gt_one : 1 < w
  k_gt_one : 1 < k
  k_le_treewidth : k ≤ tw
  hairy_large :
    cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k
  q_ge_two : 2 ≤ q
  q_powerOfTwo : CrossbarContract.IsPowerOfTwo q
  target_ge_two : 2 ≤ target
  reserve_pos : 0 < reserve
  grid_length : cGrid * Nat.log 2 q ≤ ell
  grid_width : q ^ 2 ≤ w
  local_width : exponentSevenLocalThreshold q (2 * target) ≤ w
  matching_width : 20000 * (reserve * target ^ 2) ≤ q ^ 2
  target_direct : cGrid * target * (Nat.log 2 q) ^ 2 ≤ q

/-- Target-independent coefficient package. -/
structure PolynomialThresholdTemplate7
    (cHair cHairLog cGrid reserve : ℕ) where
  K : ℕ
  b : ℕ
  C : ℕ
  p : ℕ
  K_pos : 0 < K
  b_pos : 0 < b
  C_pos : 1 ≤ C
  p_ge_two : 2 ≤ p
  matching_coeff : 4 * (20000 * reserve) ≤ C ^ 2
  direct_coeff :
    2 * cGrid * (Nat.clog 2 C + p + 2) ^ 2 ≤ C
  hairy_exponent : p * 6 + 53 + cHairLog ≤ b
  hairy_coeff :
    exponentSevenHairyConstant cHair cGrid * C ^ 6 *
      (Nat.clog 2 C + p + 3) ^ 53 *
      (Nat.clog 2 K + 2 * 7 + b) ^ cHairLog < K

namespace PolynomialThresholdTemplate7

/-- A coefficient template gives all graph-theoretic parameters at every
target order. -/
def toParameterChoice
    {cHair cHairLog cGrid reserve : ℕ}
    (T : PolynomialThresholdTemplate7
      cHair cHairLog cGrid reserve)
    (target : ℕ) (htarget : 2 ≤ target)
    (hreserve : 0 < reserve) :
    ParameterChoice7 cHair cHairLog cGrid reserve target
      (polynomialGridMinorTreewidthBound7 T.K T.b target) := by
  let n := PolynomialGridMinor.logProductScale T.C T.p target
  let k := polynomialGridMinorTreewidthBound7 T.K T.b target
  let Dn := Nat.clog 2 T.C + T.p + 3
  let Dk := Nat.clog 2 T.K + 2 * 7 + T.b
  refine
    { ell := PolynomialGridMinor.lengthScale cGrid n
      w := exponentSevenNormalizedLocalThreshold n target
      k := k
      q := GridMinorArithmetic.powTwoFloor n
      ell_gt_one := PolynomialGridMinor.lengthScale_gt_one cGrid n
      w_gt_one := ?_
      k_gt_one := ?_
      k_le_treewidth := le_rfl
      hairy_large := ?_
      q_ge_two := ?_
      q_powerOfTwo := GridMinorArithmetic.isPowerOfTwo_powTwoFloor n
      target_ge_two := htarget
      reserve_pos := hreserve
      grid_length := PolynomialGridMinor.lengthScale_grid_length cGrid n
      grid_width := ?_
      local_width := ?_
      matching_width := ?_
      target_direct := ?_ }
  · exact exponentSevenNormalizedLocalThreshold_gt_one
      (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
      htarget
  · exact polynomialGridMinorTreewidthBound7_gt_one
      (Nat.succ_le_of_lt T.K_pos) htarget
  · have hn : 2 ≤ n :=
      PolynomialGridMinor.two_le_logProductScale T.C_pos htarget
    apply lt_of_le_of_lt
      (hairy_size7_le_normalized cHair cHairLog cGrid k n target hn)
    have hlogn :
        Nat.log 2 n + 1 ≤ Dn * Nat.log 2 target := by
      simpa [n, Dn, Nat.add_assoc] using
        log_logProductScale_add_one_le7 T.C T.p htarget
    have hlogk :
        Nat.log 2 k ≤ Dk * Nat.log 2 target := by
      simpa [k, Dk] using
        log_polynomialGridMinorTreewidthBound7_le
          T.K T.b htarget
    have hthreshold :
        exponentSevenHairyConstant cHair cGrid *
            n ^ 6 * target *
            (Dn * Nat.log 2 target) ^ 53 *
            (Dk * Nat.log 2 target) ^ cHairLog <
          k := by
      simpa [n, k, Dn, Dk, Nat.add_assoc] using
        hairy_large_threshold7_of_coeff
          htarget T.hairy_exponent T.hairy_coeff
    exact lt_of_le_of_lt (by gcongr) hthreshold
  · exact GridMinorArithmetic.two_le_powTwoFloor
      (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
  · exact powTwoFloor_sq_le_normalizedLocalThreshold
      (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
      htarget
  · exact rounded_exponentSevenLocalThreshold_le
      (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
      (by omega)
  · apply GridMinorArithmetic.le_powTwoFloor_sq_of_four_mul_le_sq
    simpa [n] using
      clean_scale_logProduct_sq_of_coeff htarget T.matching_coeff
  · have hlogn :
        Nat.log 2 n ≤
          (Nat.clog 2 T.C + T.p + 2) *
            Nat.log 2 target := by
      have h :=
        PolynomialGridMinor.log_logProductScale_le_clog_const_mul_log
          T.C T.p htarget
      simpa [n] using h
    have hlogSq :
        (Nat.log 2 n) ^ 2 ≤
          ((Nat.clog 2 T.C + T.p + 2) *
            Nat.log 2 target) ^ 2 :=
      Nat.pow_le_pow_left hlogn 2
    apply GridMinorArithmetic.direct_bound_powTwoFloor_of_two_mul_le
      (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
    calc
      2 * (cGrid * target * (Nat.log 2 n) ^ 2)
          ≤ 2 * (cGrid * target *
            ((Nat.clog 2 T.C + T.p + 2) *
              Nat.log 2 target) ^ 2) := by
              gcongr
      _ ≤ n := by
        simpa [n] using
          (PolynomialGridMinor.target_direct_logProduct_of_coeff
            htarget T.p_ge_two T.direct_coeff)

/-- Canonical constants satisfying every coefficient budget. -/
def canonical
    (cHair cHairLog cGrid reserve : ℕ) :
    PolynomialThresholdTemplate7 cHair cHairLog cGrid reserve := by
  let C :=
    PolynomialGridMinor.crossbarCoefficient
      (20000 * reserve) cGrid 1
  let b := 2 * 6 + 53 + cHairLog
  let A :=
    exponentSevenHairyConstant cHair cGrid * C ^ 6 *
      (Nat.clog 2 C + 2 + 3) ^ 53
  let E := 2 * 7 + b
  refine
    { K := PolynomialGridMinor.thresholdCoefficient A cHairLog E
      b := b
      C := C
      p := 2
      K_pos := by
        dsimp [PolynomialGridMinor.thresholdCoefficient]
        positivity
      b_pos := by omega
      C_pos := by
        dsimp [C, PolynomialGridMinor.crossbarCoefficient]
        exact Nat.succ_le_of_lt (Nat.pow_pos (by norm_num))
      p_ge_two := le_rfl
      matching_coeff := ?_
      direct_coeff := ?_
      hairy_exponent := by omega
      hairy_coeff := ?_ }
  · have hstrong :=
      PolynomialGridMinor.strong_coeff_crossbarCoefficient
        (20000 * reserve) cGrid 1
    exact le_trans
      (by
        calc
          4 * (20000 * reserve) =
              4 * (20000 * reserve) * 1 := by ring
          _ ≤ 4 * (20000 * reserve) * (max 2 1) ^ 2 :=
            Nat.mul_le_mul_left _ (by norm_num))
      (by simpa [C] using hstrong)
  · simpa [C] using
      PolynomialGridMinor.direct_coeff_crossbarCoefficient
        (20000 * reserve) cGrid 1
  · simpa [A, E, Nat.add_assoc] using
      PolynomialGridMinor.coeff_mul_clog_thresholdCoefficient_add_pow_lt
        A cHairLog E

end PolynomialThresholdTemplate7

/-- Consume a bundled numerical choice with the graph-theoretic theorem. -/
theorem containsGridMinor_of_parameterChoice7
    {reserve : ℕ}
    (hDichotomy : CleanMatchingDichotomyStatement.{u} reserve) :
    ∃ cHair cHairLog cGrid : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cGrid ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) (target : ℕ),
            ParameterChoice7 cHair cHairLog cGrid reserve
              target (treewidth G) →
              ContainsGridMinor G target := by
  rcases containsGridMinor_of_treewidth_parameters hDichotomy with
    ⟨cHair, cHairLog, cGrid,
      hcHair, hcHairLog, hcGrid, hmain⟩
  refine ⟨cHair, cHairLog, cGrid,
    hcHair, hcHairLog, hcGrid, ?_⟩
  intro V _ _ G target P
  exact hmain G P.ell_gt_one P.w_gt_one P.k_gt_one
    P.k_le_treewidth P.hairy_large P.q_ge_two P.q_powerOfTwo
    P.target_ge_two P.reserve_pos P.grid_length P.grid_width
    P.local_width P.matching_width P.target_direct

/-- Conditional excluded-grid theorem with exact exponent seven. -/
theorem polynomial_grid_minor_theorem7
    {reserve : ℕ}
    (hDichotomy : CleanMatchingDichotomyStatement.{u} reserve)
    (hreserve : 0 < reserve) :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound7 K b target ≤ treewidth G →
              ContainsGridMinor G target := by
  rcases containsGridMinor_of_parameterChoice7 hDichotomy with
    ⟨cHair, cHairLog, cGrid,
      hcHair, hcHairLog, hcGrid, hmain⟩
  let T :=
    PolynomialThresholdTemplate7.canonical
      cHair cHairLog cGrid reserve
  refine ⟨T.K, T.b, T.K_pos, T.b_pos, ?_⟩
  intro V _ _ G target htarget htw
  let P := T.toParameterChoice target htarget hreserve
  exact hmain G target
    { P with
      k_le_treewidth := le_trans P.k_le_treewidth htw }

end Exponent7
end SimpleGraph
