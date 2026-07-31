import «statements-and-proofs».Exponent7.CutResponder.StrongClusterCutResponder

/-!
# The hub obstruction at the occurrence-multigraph frontier

The source and final-target labels of the routed paths may both be injective
while all selected side-changing occurrences use one common intermediate row.
Thus the occurrence multigraph can be a star, and no endpoint-disjoint
crossing batch can contain more than one occurrence.

This is a counterexample to resolving the hub certificate from labelled
occurrence data alone.  It is not asserted to refute the full
strong-cluster responder: exploiting additional geometry of the strong
cluster remains the mathematical frontier.

The last theorem records the exact additional local hypothesis already
sufficient for the responder: a uniform bound on occurrence multiplicity at
every active row.  This hypothesis is strictly stronger than bounded ambient
vertex degree, because a long bounded-degree row can contain many distinct
attachment vertices.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

open Finset

/-! ## A labelled star of side-changing occurrences -/

/-- Every occurrence has its own left row and the same right hub row. -/
def starOccurrenceSupport
    {n : ℕ} (hn : 0 < n) (p : Fin n) :
    Finset (Sum (Fin n) (Fin n)) :=
  {Sum.inl p, Sum.inr ⟨0, hn⟩}

/-- The original source labels in the star example remain all distinct. -/
def starOriginalSourceLabel {n : ℕ} (p : Fin n) : Fin n := p

/-- The final target labels in the star example also remain all distinct.
They need not equal the intermediate right-row occurrence endpoint. -/
def starFinalTargetLabel {n : ℕ} (p : Fin n) : Fin n := p

theorem starOriginalSourceLabel_injective {n : ℕ} :
    Function.Injective (@starOriginalSourceLabel n) :=
  fun _ _ h => h

theorem starFinalTargetLabel_injective {n : ℕ} :
    Function.Injective (@starFinalTargetLabel n) :=
  fun _ _ h => h

@[simp] theorem mem_starOccurrenceSupport_rightHub
    {n : ℕ} (hn : 0 < n) (p : Fin n) :
    Sum.inr (⟨0, hn⟩ : Fin n) ∈ starOccurrenceSupport hn p := by
  simp [starOccurrenceSupport]

/-- Every support-disjoint family in a star contains at most one occurrence. -/
theorem supportDisjointFamily_star_card_le_one
    {n : ℕ} (hn : 0 < n) (M : Finset (Fin n))
    (hM : SupportDisjointFamily (starOccurrenceSupport hn) M) :
    M.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra hpq
  have hdisjoint := hM hp hq hpq
  exact Finset.disjoint_left.mp hdisjoint
    (mem_starOccurrenceSupport_rightHub hn p)
    (mem_starOccurrenceSupport_rightHub hn q)

/-- In particular, the maximum endpoint-disjoint occurrence subfamily of the
star has cardinality at most one. -/
theorem maximumSupportDisjointSubfamily_star_card_le_one
    {n : ℕ} (hn : 0 < n) :
    (maximumSupportDisjointSubfamily
      (starOccurrenceSupport hn) Finset.univ).card ≤ 1 :=
  supportDisjointFamily_star_card_le_one hn _
    (maximumSupportDisjointSubfamily_spec
      (starOccurrenceSupport hn) Finset.univ).2.1

/-- No fixed response constant can extract a constant fraction from arbitrary
labelled occurrence data: choose a star with more occurrences than the
constant. -/
theorem star_has_no_response_fraction
    {n responseConstant : ℕ}
    (hn : 0 < n) (hlarge : responseConstant < n) :
    ¬ n ≤ responseConstant *
      (maximumSupportDisjointSubfamily
        (starOccurrenceSupport hn) Finset.univ).card := by
  intro hfraction
  have hcard :=
    maximumSupportDisjointSubfamily_star_card_le_one hn
  have hmul :
      responseConstant *
          (maximumSupportDisjointSubfamily
            (starOccurrenceSupport hn) Finset.univ).card
        ≤ responseConstant * 1 :=
    Nat.mul_le_mul_left responseConstant hcard
  omega

/-! ## The exact sufficient extra hypothesis -/

universe u

/-- A source-facing producer for the one extra property that resolves the hub
branch: every active selected row supports at most `d` side-changing
occurrences.

This is deliberately a proposition, not an axiom.  It identifies the weakest
additional hypothesis used by the current occurrence-matching proof; a future
graph-theoretic argument may prove it, replace it by a reserve-row theorem, or
bypass it by extracting a grid from a high-multiplicity hub. -/
def StrongClusterOccurrenceCapacityStatement
    (reserve d : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V)
    {ell w g : ℕ}
    (P : StrongPathOfSetsSystem G ell w)
    (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (cut : CutMatchingGame.Bisection (GridVertex g)),
      MaxDegreeAtMost G 4 →
      2 ≤ g →
      reserve * g ^ 2 ≤ w →
      PrescribedBisectionRouting.OccurrenceDegreeAtMost
        (strongClusterBisectionRouting P i selected cut) d

/-- A uniform occurrence-capacity producer gives the application-specific
cut responder with the exact division-free response constant `2*d`. -/
theorem strongClusterCutResponder_of_occurrenceCapacity
    {reserve d : ℕ}
    (hcapacity :
      StrongClusterOccurrenceCapacityStatement.{u} reserve d) :
    StrongClusterCutResponderStatement.{u} reserve (2 * d) := by
  intro V _ _ G ell w g P i selected cut _hdegree _hg _hwidth
  exact Or.inr
    (strongClusterCrossingResponse_of_occurrenceDegreeAtMost
      P i selected cut
      (hcapacity (V := V) G P i selected cut
        _hdegree _hg _hwidth))

end CutResponder
end Exponent7
end SimpleGraph
