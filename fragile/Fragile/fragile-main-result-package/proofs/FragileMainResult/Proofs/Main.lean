import Fragile.Proofs
import FragileMainResult.Statements.Main

namespace FragileMainResult.Proofs.Main

universe u

private theorem source_threeConnected_iff_statement {V : Type u} [Finite V]
    (G : SimpleGraph V) :
    Fragile.ThreeConnected G <-> FragileMainResult.Statements.Main.ThreeConnected G := by
  rfl

private theorem statement_mfragile_to_source {V : Type u} [Finite V]
    {m : Nat} {G : SimpleGraph V} (hfrag : FragileMainResult.Statements.Main.MFragile m G) :
    Fragile.MFragile m G := by
  intro H hH
  have hHS : FragileMainResult.Statements.Main.ThreeConnected H.coe :=
    (source_threeConnected_iff_statement H.coe).mp hH
  exact Fragile.kColorable_iff_mathlib_colorable.mpr (hfrag H hHS)

private theorem statement_no_three_connected_to_source {V : Type u} [Finite V]
    {G : SimpleGraph V} (hfragile : FragileMainResult.Statements.Main.HasNoThreeConnectedSubgraph G) :
    Fragile.HasNoThreeConnectedSubgraph G := by
  intro H hH
  exact hfragile H ((source_threeConnected_iff_statement H.coe).mp hH)

private theorem source_t3_to_statement {V : Type u} [DecidableEq V]
    {m : Nat} {G : SimpleGraph V} (hT : Fragile.T3Conditions m G) :
    FragileMainResult.Statements.Main.T3Conditions m G := by
  constructor
  · intro x y hnxy
    obtain ⟨c, hc⟩ := hT.c1 hnxy
    exact ⟨c.toMathlib, hc⟩
  constructor
  · intro x y hxy
    obtain ⟨c, hc⟩ := hT.c2 hxy
    exact ⟨c.toMathlib, hc⟩
  constructor
  · intro x y z hxy hxz hyz
    obtain ⟨c, hc⟩ := hT.c3 hxy hxz hyz
    exact ⟨c.toMathlib, hc⟩
  · intro x y z hxy hxz hyz hnot_triangle
    obtain ⟨c, hc⟩ := hT.c4 hxy hxz hyz hnot_triangle
    exact ⟨c.toMathlib, hc⟩

/-- Proof of Theorem 3 for the public statement package. -/
theorem theorem3_mfragile {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hfrag : FragileMainResult.Statements.Main.MFragile m G) :
    FragileMainResult.Statements.Main.T3Conditions m G :=
  source_t3_to_statement
    (Fragile.theorem3_mfragile m G hm (statement_mfragile_to_source hfrag))

/-- Proof of the colorability corollary for the public statement package. -/
theorem mfragile_colorable {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hfrag : FragileMainResult.Statements.Main.MFragile m G) :
    FragileMainResult.Statements.Main.KColorable m G :=
  Fragile.kColorable_iff_mathlib_colorable.mp
    (Fragile.mfragile_colorable m G hm (statement_mfragile_to_source hfrag))

/-- Proof of Theorem 2 in contrapositive form for the public statement package. -/
theorem theorem2_contra {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hnot : ¬ FragileMainResult.Statements.Main.KColorable m G) :
    ∃ H : G.Subgraph, FragileMainResult.Statements.Main.ThreeConnected H.coe ∧ ¬ FragileMainResult.Statements.Main.KColorable (m - 1) H.coe := by
  have hnot_source : ¬ Fragile.KColorable m G := by
    intro hcolor
    exact hnot (Fragile.kColorable_iff_mathlib_colorable.mp hcolor)
  obtain ⟨H, hHconn, hHnot⟩ := Fragile.theorem2_contra m G hm hnot_source
  refine ⟨H, (source_threeConnected_iff_statement H.coe).mp hHconn, ?_⟩
  intro hcolor
  exact hHnot (Fragile.kColorable_iff_mathlib_colorable.mpr hcolor)

/-- Proof of Theorem 2 in chromatic-number form for the public statement package. -/
theorem theorem2 {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hchi : ((m + 1 : Nat) : ℕ∞) ≤ G.chromaticNumber) :
    ∃ H : G.Subgraph, FragileMainResult.Statements.Main.ThreeConnected H.coe ∧ (m : ℕ∞) ≤ H.coe.chromaticNumber := by
  obtain ⟨H, hHconn, hHchi⟩ := Fragile.theorem2 m G hm hchi
  exact ⟨H, (source_threeConnected_iff_statement H.coe).mp hHconn, hHchi⟩

/-- Proof of the four-colorability corollary for the public statement package. -/
theorem fragile_four_colorable {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hfragile : FragileMainResult.Statements.Main.HasNoThreeConnectedSubgraph G) :
    FragileMainResult.Statements.Main.KColorable 4 G :=
  Fragile.kColorable_iff_mathlib_colorable.mp
    (Fragile.fragile_four_colorable G
      (statement_no_three_connected_to_source hfragile))

end FragileMainResult.Proofs.Main
