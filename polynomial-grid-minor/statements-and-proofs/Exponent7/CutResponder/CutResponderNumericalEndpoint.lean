import «statements-and-proofs».Exponent7.CutResponder.CutResponderNumericalBounds

/-!
# Numerical endpoint for the clean active cut responder

The cut-matching coordinate order and the pseudo-grid scale are separate
rounded powers of two.  This file chooses both scales and discharges every
finite inequality in the global graph theorem.

The resulting polynomial power is six.  This is stronger than the original
exponent-seven milestone because the application-specific consumer needs only
quadratically logarithmic strong-system length.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

/-- Exact treewidth threshold produced by the clean active responder route. -/
def polynomialGridMinorTreewidthBoundCleanResponder
    (K b target : ℕ) : ℕ :=
  K * target ^ 6 * (Nat.log 2 target) ^ b

/-- The logarithm of the clean-responder threshold is linear in the target
logarithm. -/
theorem log_polynomialGridMinorTreewidthBoundCleanResponder_le
    (K b : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2
        (polynomialGridMinorTreewidthBoundCleanResponder
          K b target) ≤
      (Nat.clog 2 K + 2 * 6 + b) *
        Nat.log 2 target := by
  have heq :
      polynomialGridMinorTreewidthBoundCleanResponder K b target =
        PolynomialGridMinor.monomialLogScale
          K 6 b target := rfl
  rw [heq]
  exact
    PolynomialGridMinor.log_monomialLogScale_le_clog_const_mul_log
      K 6 b htarget

/-- The clean-responder threshold is nontrivial. -/
theorem polynomialGridMinorTreewidthBoundCleanResponder_gt_one
    {K b target : ℕ}
    (hK : 1 ≤ K) (htarget : 2 ≤ target) :
    1 <
      polynomialGridMinorTreewidthBoundCleanResponder
        K b target := by
  have hlogPos : 0 < Nat.log 2 target :=
    Nat.log_pos (by decide : 1 < 2) htarget
  have hlog :
      1 ≤ (Nat.log 2 target) ^ b :=
    Nat.succ_le_of_lt (Nat.pow_pos hlogPos)
  have ht6 : 2 ≤ target ^ 6 := by
    calc
      2 ≤ 2 ^ 6 := by decide
      _ ≤ target ^ 6 :=
        Nat.pow_le_pow_left htarget 6
  have :
      2 ≤ K * target ^ 6 *
        (Nat.log 2 target) ^ b := by
    calc
      2 = 1 * 2 * 1 := by norm_num
      _ ≤ K * target ^ 6 *
          (Nat.log 2 target) ^ b := by
        gcongr
  simpa [polynomialGridMinorTreewidthBoundCleanResponder]
    using this

/-- The logarithm of a log-product scale, including the additive one used by
the local threshold, is controlled by the target logarithm. -/
theorem cleanResponder_log_logProductScale_add_one_le
    (C p : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2
          (PolynomialGridMinor.logProductScale C p target) + 1 ≤
      (Nat.clog 2 C + p + 3) * Nat.log 2 target := by
  let L := Nat.log 2 target
  have hL : 1 ≤ L := by
    exact Nat.succ_le_of_lt
      (by
        simpa [L] using
          Nat.log_pos (by decide : 1 < 2) htarget)
  calc
    Nat.log 2
          (PolynomialGridMinor.logProductScale C p target) + 1
        ≤
      (Nat.clog 2 C + p + 2) * L + 1 :=
      Nat.add_le_add_right
        (by
          simpa [L] using
            PolynomialGridMinor.log_logProductScale_le_clog_const_mul_log
              C p htarget)
        1
    _ ≤ (Nat.clog 2 C + p + 2) * L + L := by
      gcongr
    _ = (Nat.clog 2 C + p + 3) * L := by ring
    _ =
      (Nat.clog 2 C + p + 3) *
        Nat.log 2 target := rfl

/-- A coefficient comparison lifts the coordinate scale into the larger
pseudo-grid scale before power-of-two rounding. -/
theorem cleanResponder_scale_separation
    {reserve coordinateCoeff pseudoCoeff p target : ℕ}
    (hcoeff :
      4 * (20000 * reserve * coordinateCoeff ^ 2) ≤
        pseudoCoeff ^ 2) :
    4 *
        (20000 * reserve *
          (PolynomialGridMinor.logProductScale
            coordinateCoeff p target) ^ 2) ≤
      (PolynomialGridMinor.logProductScale
        pseudoCoeff p target) ^ 2 := by
  simp only [PolynomialGridMinor.logProductScale]
  calc
    4 * (20000 * reserve *
          (coordinateCoeff * target *
            Nat.log 2 target ^ p) ^ 2)
        =
      (4 * (20000 * reserve * coordinateCoeff ^ 2)) *
        (target * Nat.log 2 target ^ p) ^ 2 := by ring
    _ ≤
      pseudoCoeff ^ 2 *
        (target * Nat.log 2 target ^ p) ^ 2 :=
      Nat.mul_le_mul_right _ hcoeff
    _ =
      (pseudoCoeff * target *
        Nat.log 2 target ^ p) ^ 2 := by ring

/-- Coefficient and logarithmic-exponent budgets imply the global
hairy-system inequality at polynomial power six. -/
theorem cleanResponder_hairy_large_of_coeff
    {cHair cHairLog cGrid cRound responseConstant
      pseudoCoeff p Dcoordinate Dpseudo Dk K b target : ℕ}
    (htarget : 2 ≤ target)
    (hexponent :
      p * 6 + 2 + 53 + cHairLog ≤ b)
    (hcoeff :
      cleanResponderHairyConstant
          cHair cGrid cRound responseConstant *
        pseudoCoeff ^ 6 *
        Dcoordinate ^ 2 *
        Dpseudo ^ 53 *
        Dk ^ cHairLog < K) :
    cleanResponderHairyConstant
          cHair cGrid cRound responseConstant *
        (PolynomialGridMinor.logProductScale
          pseudoCoeff p target) ^ 6 *
        (Dcoordinate * Nat.log 2 target) ^ 2 *
        (Dpseudo * Nat.log 2 target) ^ 53 *
        (Dk * Nat.log 2 target) ^ cHairLog <
      polynomialGridMinorTreewidthBoundCleanResponder
        K b target := by
  let L := Nat.log 2 target
  have hLpos : 0 < L := by
    simpa [L] using
      Nat.log_pos (by decide : 1 < 2) htarget
  have htpos : 0 < target := by omega
  have hmultPos :
      0 < target ^ 6 * L ^ b :=
    Nat.mul_pos (Nat.pow_pos htpos)
      (Nat.pow_pos hLpos)
  have hLp6 :
      (L ^ p) ^ 6 = L ^ (p * 6) := by
    simpa using (Nat.pow_mul L p 6).symm
  have hLcombine :
      L ^ (p * 6) * L ^ 2 * L ^ 53 *
          L ^ cHairLog =
        L ^ (p * 6 + 2 + 53 + cHairLog) := by
    repeat rw [← pow_add]
  have hleft :
      cleanResponderHairyConstant
            cHair cGrid cRound responseConstant *
          (PolynomialGridMinor.logProductScale
            pseudoCoeff p target) ^ 6 *
          (Dcoordinate * L) ^ 2 *
          (Dpseudo * L) ^ 53 *
          (Dk * L) ^ cHairLog =
        (cleanResponderHairyConstant
            cHair cGrid cRound responseConstant *
          pseudoCoeff ^ 6 *
          Dcoordinate ^ 2 *
          Dpseudo ^ 53 *
          Dk ^ cHairLog) *
          target ^ 6 *
          L ^ (p * 6 + 2 + 53 + cHairLog) := by
    rw [PolynomialGridMinor.logProductScale]
    repeat rw [mul_pow]
    rw [hLp6]
    calc
      cleanResponderHairyConstant
            cHair cGrid cRound responseConstant *
          (pseudoCoeff ^ 6 * target ^ 6 *
            L ^ (p * 6)) *
          (Dcoordinate ^ 2 * L ^ 2) *
          (Dpseudo ^ 53 * L ^ 53) *
          (Dk ^ cHairLog * L ^ cHairLog)
          =
        (cleanResponderHairyConstant
            cHair cGrid cRound responseConstant *
          pseudoCoeff ^ 6 *
          Dcoordinate ^ 2 *
          Dpseudo ^ 53 *
          Dk ^ cHairLog) *
          target ^ 6 *
          (L ^ (p * 6) * L ^ 2 * L ^ 53 *
            L ^ cHairLog) := by ring
      _ =
        (cleanResponderHairyConstant
            cHair cGrid cRound responseConstant *
          pseudoCoeff ^ 6 *
          Dcoordinate ^ 2 *
          Dpseudo ^ 53 *
          Dk ^ cHairLog) *
          target ^ 6 *
          L ^ (p * 6 + 2 + 53 + cHairLog) := by
        rw [hLcombine]
  have hpow :
      L ^ (p * 6 + 2 + 53 + cHairLog) ≤
        L ^ b :=
    Nat.pow_le_pow_right hLpos hexponent
  calc
    cleanResponderHairyConstant
          cHair cGrid cRound responseConstant *
        (PolynomialGridMinor.logProductScale
          pseudoCoeff p target) ^ 6 *
        (Dcoordinate * Nat.log 2 target) ^ 2 *
        (Dpseudo * Nat.log 2 target) ^ 53 *
        (Dk * Nat.log 2 target) ^ cHairLog
        =
      (cleanResponderHairyConstant
          cHair cGrid cRound responseConstant *
        pseudoCoeff ^ 6 *
        Dcoordinate ^ 2 *
        Dpseudo ^ 53 *
        Dk ^ cHairLog) *
        target ^ 6 *
        L ^ (p * 6 + 2 + 53 + cHairLog) := by
      simpa [L] using hleft
    _ ≤
      (cleanResponderHairyConstant
          cHair cGrid cRound responseConstant *
        pseudoCoeff ^ 6 *
        Dcoordinate ^ 2 *
        Dpseudo ^ 53 *
        Dk ^ cHairLog) *
        target ^ 6 * L ^ b := by
      gcongr
    _ < K * target ^ 6 * L ^ b := by
      calc
        (cleanResponderHairyConstant
            cHair cGrid cRound responseConstant *
          pseudoCoeff ^ 6 *
          Dcoordinate ^ 2 *
          Dpseudo ^ 53 *
          Dk ^ cHairLog) *
            target ^ 6 * L ^ b
            =
          (cleanResponderHairyConstant
              cHair cGrid cRound responseConstant *
            pseudoCoeff ^ 6 *
            Dcoordinate ^ 2 *
            Dpseudo ^ 53 *
            Dk ^ cHairLog) *
            (target ^ 6 * L ^ b) := by ring
        _ < K * (target ^ 6 * L ^ b) :=
          Nat.mul_lt_mul_of_pos_right hcoeff hmultPos
        _ = K * target ^ 6 * L ^ b := by ring
    _ =
      polynomialGridMinorTreewidthBoundCleanResponder
        K b target := by
      simp [polynomialGridMinorTreewidthBoundCleanResponder, L]

/-- Fully explicit parameters consumed by the global cut-responder theorem. -/
structure CleanResponderParameterChoice
    (cHair cHairLog cGrid cRound responseConstant reserve
      target tw : ℕ) where
  ell : ℕ
  w : ℕ
  k : ℕ
  pseudoScale : ℕ
  coordinateOrder : ℕ
  systemLength : ℕ
  ell_gt_one : 1 < ell
  w_gt_one : 1 < w
  k_gt_one : 1 < k
  k_le_treewidth : k ≤ tw
  hairy_large :
    cHair * w * ell ^ 50 *
        (Nat.log 2 k) ^ cHairLog < k
  cRound_pos : 0 < cRound
  responseConstant_pos : 0 < responseConstant
  reserve_pos : 0 < reserve
  pseudo_ge_two : 2 ≤ pseudoScale
  pseudo_powerOfTwo :
    CrossbarContract.IsPowerOfTwo pseudoScale
  coordinate_ge_two : 2 ≤ coordinateOrder
  coordinate_powerOfTwo :
    CrossbarContract.IsPowerOfTwo coordinateOrder
  target_ge_two : 2 ≤ target
  target_le_coordinate : target ≤ coordinateOrder
  systemLength_pos : 0 < systemLength
  cut_length :
    cutResponderStrongLength
        cRound responseConstant coordinateOrder ≤
      systemLength
  matching_width :
    20000 * (reserve * coordinateOrder ^ 2) ≤
      pseudoScale ^ 2
  target_budget :
    CutResponderTargetBudget
      cRound coordinateOrder target
  grid_length :
    cGrid * Nat.log 2 pseudoScale ≤ ell
  grid_width : pseudoScale ^ 2 ≤ w
  local_width :
    exponentSevenLocalThreshold
        pseudoScale systemLength ≤ w
  target_outer :
    cGrid * target *
        (Nat.log 2 pseudoScale) ^ 2 ≤ pseudoScale

/-- Target-independent coefficient package for the two rounded scales. -/
structure CleanResponderPolynomialTemplate
    (cHair cHairLog cGrid cRound responseConstant reserve : ℕ) where
  K : ℕ
  b : ℕ
  coordinateCoeff : ℕ
  pseudoCoeff : ℕ
  p : ℕ
  K_pos : 0 < K
  b_pos : 0 < b
  coordinateCoeff_pos : 1 ≤ coordinateCoeff
  pseudoCoeff_pos : 1 ≤ pseudoCoeff
  p_ge_two : 2 ≤ p
  coordinate_direct_coeff :
    2 *
        HairyCrossbarGrid.fixedRoundExpanderTargetScale cRound *
        (Nat.clog 2 coordinateCoeff + p + 2) ^ 2 ≤
      coordinateCoeff
  pseudo_direct_coeff :
    2 * cGrid *
        (Nat.clog 2 pseudoCoeff + p + 2) ^ 2 ≤
      pseudoCoeff
  separation_coeff :
    4 * (20000 * reserve * coordinateCoeff ^ 2) ≤
      pseudoCoeff ^ 2
  hairy_exponent :
    p * 6 + 2 + 53 + cHairLog ≤ b
  hairy_coeff :
    cleanResponderHairyConstant
        cHair cGrid cRound responseConstant *
      pseudoCoeff ^ 6 *
      (Nat.clog 2 coordinateCoeff + p + 3) ^ 2 *
      (Nat.clog 2 pseudoCoeff + p + 3) ^ 53 *
      (Nat.clog 2 K + 2 * 6 + b) ^ cHairLog < K

namespace CleanResponderPolynomialTemplate

/-- A coefficient template gives every graph-theoretic parameter. -/
def toParameterChoice
    {cHair cHairLog cGrid cRound responseConstant reserve : ℕ}
    (T : CleanResponderPolynomialTemplate
      cHair cHairLog cGrid cRound responseConstant reserve)
    (target : ℕ)
    (htarget : 2 ≤ target)
    (hcRound : 0 < cRound)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve) :
    CleanResponderParameterChoice
      cHair cHairLog cGrid cRound responseConstant reserve
      target
      (polynomialGridMinorTreewidthBoundCleanResponder
        T.K T.b target) := by
  let coordinateBase :=
    PolynomialGridMinor.logProductScale
      T.coordinateCoeff T.p target
  let pseudoBase :=
    PolynomialGridMinor.logProductScale
      T.pseudoCoeff T.p target
  let coordinateOrder :=
    GridMinorArithmetic.powTwoFloor coordinateBase
  let pseudoScale :=
    GridMinorArithmetic.powTwoFloor pseudoBase
  let systemLength :=
    cutResponderStrongLength
      cRound responseConstant coordinateOrder
  let k :=
    polynomialGridMinorTreewidthBoundCleanResponder
      T.K T.b target
  let Dcoordinate :=
    Nat.clog 2 T.coordinateCoeff + T.p + 3
  let Dpseudo :=
    Nat.clog 2 T.pseudoCoeff + T.p + 3
  let Dk := Nat.clog 2 T.K + 2 * 6 + T.b
  have hcoordinateBase :
      2 ≤ coordinateBase :=
    PolynomialGridMinor.two_le_logProductScale
      T.coordinateCoeff_pos htarget
  have hpseudoBase :
      2 ≤ pseudoBase :=
    PolynomialGridMinor.two_le_logProductScale
      T.pseudoCoeff_pos htarget
  have hcoordinate :
      2 ≤ coordinateOrder :=
    GridMinorArithmetic.two_le_powTwoFloor hcoordinateBase
  have hpseudo :
      2 ≤ pseudoScale :=
    GridMinorArithmetic.two_le_powTwoFloor hpseudoBase
  have hcoordinatePow :
      CrossbarContract.IsPowerOfTwo coordinateOrder :=
    GridMinorArithmetic.isPowerOfTwo_powTwoFloor coordinateBase
  have hpseudoPow :
      CrossbarContract.IsPowerOfTwo pseudoScale :=
    GridMinorArithmetic.isPowerOfTwo_powTwoFloor pseudoBase
  have hcoordinateLog :
      Nat.log 2 coordinateBase ≤
        (Nat.clog 2 T.coordinateCoeff + T.p + 2) *
          Nat.log 2 target := by
    simpa [coordinateBase] using
      PolynomialGridMinor.log_logProductScale_le_clog_const_mul_log
        T.coordinateCoeff T.p htarget
  have hpseudoLog :
      Nat.log 2 pseudoBase ≤
        (Nat.clog 2 T.pseudoCoeff + T.p + 2) *
          Nat.log 2 target := by
    simpa [pseudoBase] using
      PolynomialGridMinor.log_logProductScale_le_clog_const_mul_log
        T.pseudoCoeff T.p htarget
  have hcoordinateScaled :
      cutResponderTargetDenominator cRound coordinateOrder *
          target ≤ coordinateOrder := by
    have hdirect :
        HairyCrossbarGrid.fixedRoundExpanderTargetScale cRound *
              target *
              (Nat.log 2 coordinateOrder) ^ 2 ≤
            coordinateOrder := by
      apply
        GridMinorArithmetic.direct_bound_powTwoFloor_of_two_mul_le
          hcoordinateBase
      calc
        2 *
            (HairyCrossbarGrid.fixedRoundExpanderTargetScale
                cRound *
              target *
              (Nat.log 2 coordinateBase) ^ 2)
            ≤
          2 *
            (HairyCrossbarGrid.fixedRoundExpanderTargetScale
                cRound *
              target *
              ((Nat.clog 2 T.coordinateCoeff + T.p + 2) *
                Nat.log 2 target) ^ 2) := by
          gcongr
        _ ≤ coordinateBase := by
          simpa [coordinateBase] using
            PolynomialGridMinor.target_direct_logProduct_of_coeff
              htarget T.p_ge_two
              T.coordinate_direct_coeff
    simpa [cutResponderTargetDenominator, mul_assoc,
      mul_left_comm, mul_comm] using hdirect
  have htargetLe : target ≤ coordinateOrder := by
    have hlogPos :
        0 < Nat.log 2 coordinateOrder :=
      Nat.log_pos (by decide : 1 < 2) hcoordinate
    have hdenomPos :
        0 <
          cutResponderTargetDenominator
            cRound coordinateOrder := by
      exact Nat.mul_pos
        (HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos cRound)
        (Nat.pow_pos hlogPos)
    calc
      target = 1 * target := by simp
      _ ≤
        cutResponderTargetDenominator cRound coordinateOrder *
          target := by
        gcongr
        omega
      _ ≤ coordinateOrder := hcoordinateScaled
  have hmatching :
      20000 * (reserve * coordinateOrder ^ 2) ≤
        pseudoScale ^ 2 := by
    apply
      GridMinorArithmetic.le_powTwoFloor_sq_of_four_mul_le_sq
    have hcoordFloor :
        coordinateOrder ^ 2 ≤ coordinateBase ^ 2 :=
      GridMinorArithmetic.pow_powTwoFloor_le_pow
        hcoordinateBase
    calc
      4 *
          (20000 *
            (reserve * coordinateOrder ^ 2))
          ≤
        4 *
          (20000 *
            (reserve * coordinateBase ^ 2)) := by
        gcongr
      _ =
        4 *
          (20000 * reserve * coordinateBase ^ 2) := by
        ring
      _ ≤ pseudoBase ^ 2 := by
        simpa [coordinateBase, pseudoBase] using
          cleanResponder_scale_separation
            (p := T.p) (target := target)
            T.separation_coeff
  have hpseudoOuter :
      cGrid * target *
          (Nat.log 2 pseudoScale) ^ 2 ≤
        pseudoScale := by
    apply
      GridMinorArithmetic.direct_bound_powTwoFloor_of_two_mul_le
        hpseudoBase
    calc
      2 *
          (cGrid * target *
            (Nat.log 2 pseudoBase) ^ 2)
          ≤
        2 *
          (cGrid * target *
            ((Nat.clog 2 T.pseudoCoeff + T.p + 2) *
              Nat.log 2 target) ^ 2) := by
        gcongr
      _ ≤ pseudoBase := by
        simpa [pseudoBase] using
          PolynomialGridMinor.target_direct_logProduct_of_coeff
            htarget T.p_ge_two
            T.pseudo_direct_coeff
  refine
    { ell :=
        PolynomialGridMinor.lengthScale
          cGrid pseudoBase
      w :=
        cleanResponderNormalizedLocalThreshold
          pseudoBase coordinateBase cRound responseConstant
      k := k
      pseudoScale := pseudoScale
      coordinateOrder := coordinateOrder
      systemLength := systemLength
      ell_gt_one :=
        PolynomialGridMinor.lengthScale_gt_one
          cGrid pseudoBase
      w_gt_one :=
        cleanResponderNormalizedLocalThreshold_gt_one
          hpseudoBase hcoordinateBase hcRound hc
      k_gt_one :=
        polynomialGridMinorTreewidthBoundCleanResponder_gt_one
          (Nat.succ_le_of_lt T.K_pos) htarget
      k_le_treewidth := le_rfl
      hairy_large := ?_
      cRound_pos := hcRound
      responseConstant_pos := hc
      reserve_pos := hreserve
      pseudo_ge_two := hpseudo
      pseudo_powerOfTwo := hpseudoPow
      coordinate_ge_two := hcoordinate
      coordinate_powerOfTwo := hcoordinatePow
      target_ge_two := htarget
      target_le_coordinate := htargetLe
      systemLength_pos :=
        cutResponderStrongLength_pos
          hcRound hc hcoordinate
      cut_length := le_rfl
      matching_width := hmatching
      target_budget :=
        cutResponderTargetBudget_of_mul_le
          hcoordinate hcoordinatePow htarget
          hcoordinateScaled
      grid_length :=
        PolynomialGridMinor.lengthScale_grid_length
          cGrid pseudoBase
      grid_width :=
        powTwoFloor_pseudo_sq_le_cleanResponderNormalized
          hpseudoBase hcoordinateBase hcRound hc
      local_width := ?_
      target_outer := hpseudoOuter }
  · apply lt_of_le_of_lt
      (cleanResponder_hairy_size_le_normalized
        cHair cHairLog cGrid cRound responseConstant
        k pseudoBase coordinateBase hpseudoBase)
    have hlogCoordinate :
        Nat.log 2 coordinateBase + 1 ≤
          Dcoordinate * Nat.log 2 target := by
      simpa [coordinateBase, Dcoordinate, Nat.add_assoc]
        using
          cleanResponder_log_logProductScale_add_one_le
            T.coordinateCoeff T.p htarget
    have hlogPseudo :
        Nat.log 2 pseudoBase + 1 ≤
          Dpseudo * Nat.log 2 target := by
      simpa [pseudoBase, Dpseudo, Nat.add_assoc]
        using
          cleanResponder_log_logProductScale_add_one_le
            T.pseudoCoeff T.p htarget
    have hlogK :
        Nat.log 2 k ≤
          Dk * Nat.log 2 target := by
      simpa [k, Dk] using
        log_polynomialGridMinorTreewidthBoundCleanResponder_le
          T.K T.b htarget
    have hthreshold :
        cleanResponderHairyConstant
              cHair cGrid cRound responseConstant *
            pseudoBase ^ 6 *
            (Dcoordinate * Nat.log 2 target) ^ 2 *
            (Dpseudo * Nat.log 2 target) ^ 53 *
            (Dk * Nat.log 2 target) ^ cHairLog <
          k := by
      simpa [pseudoBase, k, Dcoordinate, Dpseudo, Dk,
        Nat.add_assoc] using
        cleanResponder_hairy_large_of_coeff
          htarget T.hairy_exponent T.hairy_coeff
    exact lt_of_le_of_lt (by gcongr) hthreshold
  · simpa [systemLength] using
      rounded_cutResponderLocalThreshold_le
        hpseudoBase hcoordinateBase hcRound hc

/-- Canonical constants satisfying every coefficient budget. -/
def canonical
    (cHair cHairLog cGrid cRound responseConstant reserve : ℕ) :
    CleanResponderPolynomialTemplate
      cHair cHairLog cGrid cRound responseConstant reserve := by
  let targetScale :=
    HairyCrossbarGrid.fixedRoundExpanderTargetScale cRound
  let coordinateCoeff :=
    PolynomialGridMinor.crossbarCoefficient
      1 targetScale 1
  let separationCost :=
    20000 * reserve * coordinateCoeff ^ 2
  let pseudoCoeff :=
    PolynomialGridMinor.crossbarCoefficient
      separationCost cGrid 1
  let b := 2 * 6 + 2 + 53 + cHairLog
  let A :=
    cleanResponderHairyConstant
        cHair cGrid cRound responseConstant *
      pseudoCoeff ^ 6 *
      (Nat.clog 2 coordinateCoeff + 2 + 3) ^ 2 *
      (Nat.clog 2 pseudoCoeff + 2 + 3) ^ 53
  let E := 2 * 6 + b
  refine
    { K :=
        PolynomialGridMinor.thresholdCoefficient
          A cHairLog E
      b := b
      coordinateCoeff := coordinateCoeff
      pseudoCoeff := pseudoCoeff
      p := 2
      K_pos := by
        dsimp [PolynomialGridMinor.thresholdCoefficient]
        positivity
      b_pos := by omega
      coordinateCoeff_pos := by
        dsimp [coordinateCoeff,
          PolynomialGridMinor.crossbarCoefficient]
        exact Nat.succ_le_of_lt
          (Nat.pow_pos (by norm_num))
      pseudoCoeff_pos := by
        dsimp [pseudoCoeff,
          PolynomialGridMinor.crossbarCoefficient]
        exact Nat.succ_le_of_lt
          (Nat.pow_pos (by norm_num))
      p_ge_two := le_rfl
      coordinate_direct_coeff := ?_
      pseudo_direct_coeff := ?_
      separation_coeff := ?_
      hairy_exponent := by omega
      hairy_coeff := ?_ }
  · simpa [coordinateCoeff, targetScale] using
      PolynomialGridMinor.direct_coeff_crossbarCoefficient
        1 targetScale 1
  · simpa [pseudoCoeff] using
      PolynomialGridMinor.direct_coeff_crossbarCoefficient
        separationCost cGrid 1
  · have hstrong :=
      PolynomialGridMinor.strong_coeff_crossbarCoefficient
        separationCost cGrid 1
    exact le_trans
      (by
        calc
          4 * (20000 * reserve * coordinateCoeff ^ 2)
              = 4 * separationCost := by
                simp [separationCost]
          _ ≤
            4 * separationCost * (max 2 1) ^ 2 := by
              exact
                Nat.le_mul_of_pos_right
                  (4 * separationCost) (by norm_num))
      (by simpa [pseudoCoeff] using hstrong)
  · simpa [A, E, Nat.add_assoc] using
      PolynomialGridMinor.coeff_mul_clog_thresholdCoefficient_add_pow_lt
        A cHairLog E

end CleanResponderPolynomialTemplate

/-- Consume a bundled numerical choice with the graph-theoretic theorem. -/
theorem containsGridMinor_of_cleanResponderParameterChoice
    {reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatement.{u}
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve) :
    ∃ cRound cHair cHairLog cGrid : ℕ,
      0 < cRound ∧ 0 < cHair ∧
      0 < cHairLog ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) (target : ℕ),
          CleanResponderParameterChoice
              cHair cHairLog cGrid cRound
              responseConstant reserve target
              (treewidth G) →
            ContainsGridMinor G target := by
  rcases
      CutMatchingGame.exists_gridVertex_fixedRound_exact_list_halfExpander
      with ⟨cRound, hcRound, hstrategy⟩
  rcases
      containsGridMinor_of_treewidth_parameters_cleanActive
        (cRound := cRound)
        (responseConstant := responseConstant)
        (reserve := reserve)
        hstrategy
        hclean
      with
    ⟨cHair, cHairLog, cGrid,
      hcHair, hcHairLog, hcGrid, hmain⟩
  refine
    ⟨cRound, cHair, cHairLog, cGrid,
      hcRound, hcHair, hcHairLog, hcGrid, ?_⟩
  intro V _ _ G target P
  exact
    hmain G P.ell_gt_one P.w_gt_one P.k_gt_one
      P.k_le_treewidth P.hairy_large
      P.cRound_pos P.responseConstant_pos P.reserve_pos
      P.pseudo_ge_two P.pseudo_powerOfTwo
      P.coordinate_ge_two P.coordinate_powerOfTwo
      P.target_le_coordinate
      P.systemLength_pos P.cut_length P.matching_width
      P.target_budget P.grid_length P.grid_width
      P.local_width P.target_outer

/-- Conditional excluded-grid theorem with exact polynomial power six.  The
sole research input is the ordinary clean active cut-responder proposition;
no project axiom is declared. -/
theorem polynomial_grid_minor_theorem_cleanResponder
    {reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatement.{u}
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve) :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
          polynomialGridMinorTreewidthBoundCleanResponder
              K b target ≤ treewidth G →
          ContainsGridMinor G target := by
  rcases
      containsGridMinor_of_cleanResponderParameterChoice
        hclean hc hreserve
      with
    ⟨cRound, cHair, cHairLog, cGrid,
      hcRound, hcHair, hcHairLog, hcGrid, hmain⟩
  let T :=
    CleanResponderPolynomialTemplate.canonical
      cHair cHairLog cGrid cRound
      responseConstant reserve
  refine ⟨T.K, T.b, T.K_pos, T.b_pos, ?_⟩
  intro V _ _ G target htarget htw
  let P :=
    T.toParameterChoice target htarget
      hcRound hc hreserve
  exact
    hmain G target
      { P with
        k_le_treewidth :=
          le_trans P.k_le_treewidth htw }

end CutResponder
end Exponent7
end SimpleGraph
