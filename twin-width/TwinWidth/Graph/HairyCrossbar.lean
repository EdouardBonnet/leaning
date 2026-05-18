import TwinWidth.Graph.HairyPathOfSets
import TwinWidth.Graph.CrossbarTheorem
import TwinWidth.Graph.HairyCrossbarGrid

/-!
# Crossbar dichotomy inside a hairy path-of-sets cluster

This file proves the local application of the Chuzhoy--Tan crossbar dichotomy
to one cluster of a hairy Path-of-Sets System.  The hairy-system API supplies
the two required path packings: one from left nails to right nails and one from
left nails to the hair endpoints.
-/

namespace TwinWidth
namespace SimpleGraph
namespace HairyPathOfSetsSystem

universe u

/-- The crossbar dichotomy as an explicit input rather than as a contract
axiom.  Parameterized composition theorems use this interface to keep their
proof terms independent of `CrossbarContract.crossbar_or_strong_pathOfSets_minor`. -/
def CrossbarDichotomyInput (c : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph V) {g kappa : ℕ}
    {A B X : Finset V},
      2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
          A.card = kappa →
            B.card = kappa →
              X.card = kappa →
                Disjoint A B →
                  Disjoint A X →
                    Disjoint B X →
                      2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ kappa →
                        (∀ x ∈ X, DegreeEquals H x 1) →
                          (Pab : PathPacking H A B) →
                            Pab.card = kappa →
                              (Pax : PathPacking H A X) →
                                Pax.card = kappa →
                                  Nonempty (Crossbar H A B X (g ^ 2)) ∨
                                    ∃ ell' w' : ℕ,
                                      g ^ 2 ≤ c * ell' ∧
                                        g ^ 2 ≤ c * w' ∧
                                          CrossbarContract.HasStrongPathOfSetsMinor
                                            H ell' w'

/-- Input form of the local crossbar dichotomy in a hair-local graph. -/
theorem crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph_of_crossbarDichotomy
    (hinput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                Nonempty (Crossbar (Hsys.hairLocalGraph i)
                  (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor
                          (Hsys.hairLocalGraph i) ell' w' := by
  rcases hinput with ⟨c, hc, hcrossbar⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys i hg hpow hlarge
  rcases Hsys.exists_left_right_linkage_inHairLocalGraph_with_staysIn i with
    ⟨Pab, hPab_card, _hPab_stays⟩
  rcases Hsys.exists_left_y_perfect_linkage_inHairLocalGraph i with
    ⟨Pax, hPax_card⟩
  have hleft_card : (Hsys.base.left i).card = w := Hsys.base.left_card i
  have hright_card : (Hsys.base.right i).card = w := Hsys.base.right_card i
  have hy_card : (Hsys.y i).card = w := Hsys.y_card i
  have hleft_y_disjoint : Disjoint (Hsys.base.left i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvleft hvy
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvy)
      (Hsys.base.left_subset_cluster i hvleft)
  have hright_y_disjoint : Disjoint (Hsys.base.right i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvright hvy
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvy)
      (Hsys.base.right_subset_cluster i hvright)
  exact hcrossbar (Hsys.hairLocalGraph i) hg hpow hleft_card hright_card
    hy_card (Hsys.base.left_right_disjoint i) hleft_y_disjoint hright_y_disjoint
    hlarge (fun x hx => Hsys.hairLocalGraph_degreeEquals_one_of_mem_y i hx)
    Pab hPab_card Pax.toPathPacking (by simpa using hPax_card)

/-- In the hair-local graph of a cluster, the crossbar dichotomy applies to the
terminal sets `(left_i, right_i, y_i)`. -/
theorem crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                Nonempty (Crossbar (Hsys.hairLocalGraph i)
                  (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor
                          (Hsys.hairLocalGraph i) ell' w' := by
  rcases CrossbarTheorem.crossbar_or_strong_pathOfSets_minor with
    ⟨c, hc, hcrossbar⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys i hg hpow hlarge
  rcases Hsys.exists_left_right_linkage_inHairLocalGraph_with_staysIn i with
    ⟨Pab, hPab_card, _hPab_stays⟩
  rcases Hsys.exists_left_y_perfect_linkage_inHairLocalGraph i with
    ⟨Pax, hPax_card⟩
  have hleft_card : (Hsys.base.left i).card = w := Hsys.base.left_card i
  have hright_card : (Hsys.base.right i).card = w := Hsys.base.right_card i
  have hy_card : (Hsys.y i).card = w := Hsys.y_card i
  have hleft_y_disjoint : Disjoint (Hsys.base.left i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvleft hvy
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvy)
      (Hsys.base.left_subset_cluster i hvleft)
  have hright_y_disjoint : Disjoint (Hsys.base.right i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvright hvy
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvy)
      (Hsys.base.right_subset_cluster i hvright)
  exact hcrossbar (Hsys.hairLocalGraph i) hg hpow hleft_card hright_card
    hy_card (Hsys.base.left_right_disjoint i) hleft_y_disjoint hright_y_disjoint
    hlarge (fun x hx => Hsys.hairLocalGraph_degreeEquals_one_of_mem_y i hx)
    Pab hPab_card Pax.toPathPacking (by simpa using hPax_card)

/-- Ambient-graph version of
`crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph`: if the dichotomy
returns a strong Path-of-Sets minor inside the hair-local graph, the minor is
transported to the ambient graph. -/
theorem crossbar_or_strong_pathOfSets_minor_in_hairyCluster :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                Nonempty (Crossbar (Hsys.hairLocalGraph i)
                  (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  rcases crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph with
    ⟨c, hc, hlocal⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys i hg hpow hlarge
  rcases hlocal Hsys i hg hpow hlarge with hcrossbar | hstrong
  · exact Or.inl hcrossbar
  · rcases hstrong with ⟨ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw,
      hminor.mono (Hsys.hairLocalGraph_le i)⟩

/-- Input form of the ambient hair-cluster crossbar dichotomy. -/
theorem crossbar_or_strong_pathOfSets_minor_in_hairyCluster_of_crossbarDichotomy
    (hinput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                Nonempty (Crossbar (Hsys.hairLocalGraph i)
                  (Hsys.base.left i) (Hsys.base.right i) (Hsys.y i) (g ^ 2)) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  rcases crossbar_or_strong_pathOfSets_minor_in_hairLocalGraph_of_crossbarDichotomy
      hinput with
    ⟨c, hc, hlocal⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys i hg hpow hlarge
  rcases hlocal Hsys i hg hpow hlarge with hcrossbar | hstrong
  · exact Or.inl hcrossbar
  · rcases hstrong with ⟨ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw,
      hminor.mono (Hsys.hairLocalGraph_le i)⟩

/-- Applying the local crossbar dichotomy at every odd one-based cluster gives
either local crossbars at all those clusters, or a strong Path-of-Sets minor in
the ambient graph.  This is the interface used by the crossbar-grid assembly
theorem, since the proof needs the crossbars to live in `C_i ∪ Q_i`, not merely
in the ambient graph. -/
theorem local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                (∀ i : Fin ell,
                  _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.OneBasedOdd i →
                  Nonempty (Crossbar (Hsys.hairLocalGraph i)
                    (Hsys.base.left i) (Hsys.base.right i)
                    (Hsys.y i) (g ^ 2))) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  rcases crossbar_or_strong_pathOfSets_minor_in_hairyCluster with
    ⟨c, hc, hcluster⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hlarge
  by_cases hstrong :
      ∃ i : Fin ell,
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.OneBasedOdd i ∧
        ∃ ell' w' : ℕ,
          g ^ 2 ≤ c * ell' ∧
            g ^ 2 ≤ c * w' ∧
              CrossbarContract.HasStrongPathOfSetsMinor G ell' w'
  · rcases hstrong with ⟨_i, _hi, ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw, hminor⟩
  · refine Or.inl ?_
    intro i hi
    rcases hcluster Hsys i hg hpow hlarge with hcrossbar | hminor
    · exact hcrossbar
    · exact False.elim (hstrong ⟨i, hi, hminor⟩)

/-- Input form of the odd-cluster crossbar dichotomy. -/
theorem local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor_of_crossbarDichotomy
    (hinput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                (∀ i : Fin ell,
                  _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.OneBasedOdd i →
                  Nonempty (Crossbar (Hsys.hairLocalGraph i)
                    (Hsys.base.left i) (Hsys.base.right i)
                    (Hsys.y i) (g ^ 2))) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  rcases crossbar_or_strong_pathOfSets_minor_in_hairyCluster_of_crossbarDichotomy
      hinput with
    ⟨c, hc, hcluster⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hlarge
  by_cases hstrong :
      ∃ i : Fin ell,
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.OneBasedOdd i ∧
        ∃ ell' w' : ℕ,
          g ^ 2 ≤ c * ell' ∧
            g ^ 2 ≤ c * w' ∧
              CrossbarContract.HasStrongPathOfSetsMinor G ell' w'
  · rcases hstrong with ⟨_i, _hi, ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw, hminor⟩
  · refine Or.inl ?_
    intro i hi
    rcases hcluster Hsys i hg hpow hlarge with hcrossbar | hminor
    · exact hcrossbar
    · exact False.elim (hstrong ⟨i, hi, hminor⟩)

/-- Applying the local crossbar dichotomy at every odd one-based cluster gives
either ambient crossbars at all those clusters, or a strong Path-of-Sets minor
in the ambient graph. -/
theorem ambient_crossbars_at_odd_clusters_or_strong_pathOfSets_minor :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                (∀ i : Fin ell,
                  _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.OneBasedOdd i →
                  Nonempty (Crossbar G (Hsys.base.left i) (Hsys.base.right i)
                    (Hsys.y i) (g ^ 2))) ∨
                  ∃ ell' w' : ℕ,
                    g ^ 2 ≤ c * ell' ∧
                      g ^ 2 ≤ c * w' ∧
                        CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  rcases local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor with
    ⟨c, hc, hlocal⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hlarge
  rcases hlocal Hsys hg hpow hlarge with hcrossbars | hstrong
  · refine Or.inl ?_
    intro i hi
    rcases hcrossbars i hi with ⟨C⟩
    exact ⟨C.mapLe (Hsys.hairLocalGraph_le i)⟩
  · exact Or.inr hstrong

/-- A hairy Path-of-Sets System either directly gives a grid minor via the
crossbars at odd clusters, or yields the strong Path-of-Sets minor outcome of
the local crossbar dichotomy. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                cGrid * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                      (∃ g' : ℕ,
                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g') ∨
                        ∃ ell' w' : ℕ,
                          g ^ 2 ≤ cCross * ell' ∧
                            g ^ 2 ≤ cCross * w' ∧
                              CrossbarContract.HasStrongPathOfSetsMinor
                                G ell' w' := by
  rcases local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor with
    ⟨cCross, hcCross, hodd⟩
  rcases HairyCrossbarGrid.gridMinor_of_hairy_pathOfSets_and_crossbars with
    ⟨cGrid, hcGrid, hgrid⟩
  refine ⟨cCross, cGrid, hcCross, hcGrid, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hlarge
  rcases hodd Hsys hg hpow hlarge with hcrossbars | hstrong
  · exact Or.inl (hgrid G Hsys hg hpow hmaxDegree hell hw hcrossbars)
  · exact Or.inr hstrong

/-- Conditional version of
`gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets` whose direct
grid-minor branch uses the narrowed large-case cut-matching data provider
instead of the monolithic crossbar-grid contract. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_largeCaseCutMatchingDataProvider
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                cGrid * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                      (∃ g' : ℕ,
                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g') ∨
                        ∃ ell' w' : ℕ,
                          g ^ 2 ≤ cCross * ell' ∧
                            g ^ 2 ≤ cCross * w' ∧
                              CrossbarContract.HasStrongPathOfSetsMinor
                                G ell' w' := by
  rcases local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor with
    ⟨cCross, hcCross, hodd⟩
  rcases
    HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_largeCaseCutMatchingDataProvider
      hlargeData with
    ⟨cGrid, hcGrid, hgrid⟩
  refine ⟨cCross, cGrid, hcCross, hcGrid, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hlarge
  rcases hodd Hsys hg hpow hlarge with hcrossbars | hstrong
  · exact Or.inl (hgrid G Hsys hg hpow hmaxDegree hell hw hcrossbars)
  · exact Or.inr hstrong

/-- Input form of
`gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_largeCaseCutMatchingDataProvider`,
with the crossbar dichotomy supplied as an explicit hypothesis. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_crossbarDichotomy_and_largeCaseCutMatchingDataProvider
    (hinput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c)
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                cGrid * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                      (∃ g' : ℕ,
                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g') ∨
                        ∃ ell' w' : ℕ,
                          g ^ 2 ≤ cCross * ell' ∧
                            g ^ 2 ≤ cCross * w' ∧
                              CrossbarContract.HasStrongPathOfSetsMinor
                                G ell' w' := by
  rcases local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor_of_crossbarDichotomy
      hinput with
    ⟨cCross, hcCross, hodd⟩
  rcases
    HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_largeCaseCutMatchingDataProvider
      hlargeData with
    ⟨cGrid, hcGrid, hgrid⟩
  refine ⟨cCross, cGrid, hcCross, hcGrid, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hlarge
  rcases hodd Hsys hg hpow hlarge with hcrossbars | hstrong
  · exact Or.inl (hgrid G Hsys hg hpow hmaxDegree hell hw hcrossbars)
  · exact Or.inr hstrong

/-- Version of
`gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_largeCaseCutMatchingDataProvider`
using the paper-shaped fixed-round cut-matching provider. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_fixedRoundLargeCaseCutMatchingDataProvider
    (hfixed :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundLargeCaseCutMatchingDataProvider.{u}
          cRound cScale) :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                cGrid * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                      (∃ g' : ℕ,
                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g') ∨
                        ∃ ell' w' : ℕ,
                          g ^ 2 ≤ cCross * ell' ∧
                            g ^ 2 ≤ cCross * w' ∧
                              CrossbarContract.HasStrongPathOfSetsMinor
                                G ell' w' :=
  gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_largeCaseCutMatchingDataProvider
    (_root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.exists_largeCaseCutMatchingDataProvider_of_fixedRound
      hfixed)

/-- Version using the unbundled fixed-round cut sequence provider and the
separator-grid provider for the direct crossbar-grid branch. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_unbundledCutMatching_and_separatorProviders
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundSeparatorGridProvider
            cRound cScale) :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                cGrid * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                      (∃ g' : ℕ,
                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g') ∨
                        ∃ ell' w' : ℕ,
                          g ^ 2 ≤ cCross * ell' ∧
                            g ^ 2 ≤ cCross * w' ∧
                              CrossbarContract.HasStrongPathOfSetsMinor
                                G ell' w' :=
  gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_largeCaseCutMatchingDataProvider
    (_root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.exists_largeCaseCutMatchingDataProvider_of_unbundled_and_separator
      hproviders)

/-- Supergraph version of
`gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets`: if the hairy system
lives in a subgraph, both outcomes are transported to the ambient graph. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_subgraph_hairy_pathOfSets :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G H : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem H ell w),
          H ≤ G →
            2 ≤ g →
              CrossbarContract.IsPowerOfTwo g →
                MaxDegreeAtMost H 3 →
                  cGrid * Nat.log 2 g ≤ ell →
                    g ^ 2 ≤ w →
                      2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                        (∃ g' : ℕ,
                          g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                            ContainsGridMinor G g') ∨
                          ∃ ell' w' : ℕ,
                            g ^ 2 ≤ cCross * ell' ∧
                              g ^ 2 ≤ cCross * w' ∧
                                CrossbarContract.HasStrongPathOfSetsMinor
                                  G ell' w' := by
  rcases gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets with
    ⟨cCross, cGrid, hcCross, hcGrid, hmain⟩
  refine ⟨cCross, cGrid, hcCross, hcGrid, ?_⟩
  intro V _ _ G H ell w g Hsys hHG hg hpow hmaxDegree hell hw hlarge
  rcases hmain H Hsys hg hpow hmaxDegree hell hw hlarge with hgrid | hstrong
  · rcases hgrid with ⟨g', hbound, hgrid⟩
    exact Or.inl ⟨g', hbound, hgrid.mono hHG⟩
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    exact Or.inr ⟨ell', w', hell', hw', hminor.mono hHG⟩

/-- Supergraph version of the conditional hairy-crossbar theorem, still using
only the narrowed large-case cut-matching data provider for the direct
crossbar-grid branch. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_subgraph_hairy_pathOfSets_of_largeCaseCutMatchingDataProvider
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G H : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem H ell w),
          H ≤ G →
            2 ≤ g →
              CrossbarContract.IsPowerOfTwo g →
                MaxDegreeAtMost H 3 →
                  cGrid * Nat.log 2 g ≤ ell →
                    g ^ 2 ≤ w →
                      2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                        (∃ g' : ℕ,
                          g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                            ContainsGridMinor G g') ∨
                          ∃ ell' w' : ℕ,
                            g ^ 2 ≤ cCross * ell' ∧
                              g ^ 2 ≤ cCross * w' ∧
                                CrossbarContract.HasStrongPathOfSetsMinor
                                  G ell' w' := by
  rcases
    gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_largeCaseCutMatchingDataProvider
      hlargeData with
    ⟨cCross, cGrid, hcCross, hcGrid, hmain⟩
  refine ⟨cCross, cGrid, hcCross, hcGrid, ?_⟩
  intro V _ _ G H ell w g Hsys hHG hg hpow hmaxDegree hell hw hlarge
  rcases hmain H Hsys hg hpow hmaxDegree hell hw hlarge with hgrid | hstrong
  · rcases hgrid with ⟨g', hbound, hgrid⟩
    exact Or.inl ⟨g', hbound, hgrid.mono hHG⟩
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    exact Or.inr ⟨ell', w', hell', hw', hminor.mono hHG⟩

/-- The graph-theoretic part of the hairy-system proof with the remaining
arithmetic factored out.  If `r^2` fits inside every strong path-of-sets minor
returned by the crossbar dichotomy, then either the crossbar assembly branch or
the strong-minor branch already yields a grid minor. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_strong_scale :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 g ≤ ell →
                      g ^ 2 ≤ w →
                        2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                          (∀ {ell' w' : ℕ},
                            g ^ 2 ≤ cCross * ell' →
                              g ^ 2 ≤ cCross * w' →
                                r ^ 2 ≤ ell' ∧ r ^ 2 ≤ w') →
                            (∃ g' : ℕ,
                              g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                ContainsGridMinor G g') ∨
                              ∃ r' : ℕ,
                                r ≤ cStrong * r' ∧
                                  ContainsGridMinor G r' := by
  rcases gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets with
    ⟨cCross, cGrid, hcCross, hcGrid, hmain⟩
  rcases CrossbarContract.HasStrongPathOfSetsMinor.exists_gridMinor_of_large with
    ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w g r Hsys hg hr hpow hmaxDegree hell hw hlarge hscale
  rcases hmain G Hsys hg hpow hmaxDegree hell hw hlarge with hgrid | hstrong
  · exact Or.inl hgrid
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    rcases hscale hell' hw' with ⟨hrlength, hrwidth⟩
    exact Or.inr (hstrongGrid hr hrlength hrwidth hminor)

/-- Cancel the crossbar constant from a scaled square lower bound. -/
theorem square_le_of_scaled_square_le {c g r n : ℕ}
    (hc : 0 < c) (hscaled : c * r ^ 2 ≤ g ^ 2)
    (hn : g ^ 2 ≤ c * n) :
    r ^ 2 ≤ n :=
  Nat.le_of_mul_le_mul_left (le_trans hscaled hn) hc

/-- Variant of
`gridMinor_or_gridMinor_of_hairy_pathOfSets_with_strong_scale` where the
remaining arithmetic obligation is the single scaled inequality
`cCross * r^2 ≤ g^2`. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 g ≤ ell →
                      g ^ 2 ≤ w →
                        2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                          cCross * r ^ 2 ≤ g ^ 2 →
                            (∃ g' : ℕ,
                              g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                ContainsGridMinor G g') ∨
                              ∃ r' : ℕ,
                                r ≤ cStrong * r' ∧
                                  ContainsGridMinor G r' := by
  rcases gridMinor_or_gridMinor_of_hairy_pathOfSets_with_strong_scale with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w g r Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled
  exact hmain G Hsys hg hr hpow hmaxDegree hell hw hlarge (by
    intro ell' w' hell' hw'
    exact ⟨square_le_of_scaled_square_le hcCross hscaled hell',
      square_le_of_scaled_square_le hcCross hscaled hw'⟩)

/-- Conditional version of
`gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter`
using the cut-matching data provider for the direct crossbar-grid branch. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_largeCaseCutMatchingDataProvider
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 g ≤ ell →
                      g ^ 2 ≤ w →
                        2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                          cCross * r ^ 2 ≤ g ^ 2 →
                            (∃ g' : ℕ,
                              g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                ContainsGridMinor G g') ∨
                              ∃ r' : ℕ,
                                r ≤ cStrong * r' ∧
                                  ContainsGridMinor G r' := by
  rcases
    gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_largeCaseCutMatchingDataProvider
      hlargeData with
    ⟨cCross, cGrid, hcCross, hcGrid, hmain⟩
  rcases CrossbarContract.HasStrongPathOfSetsMinor.exists_gridMinor_of_large with
    ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w g r Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled
  rcases hmain G Hsys hg hpow hmaxDegree hell hw hlarge with hgrid | hstrong
  · exact Or.inl hgrid
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    exact Or.inr (hstrongGrid hr
      (square_le_of_scaled_square_le hcCross hscaled hell')
      (square_le_of_scaled_square_le hcCross hscaled hw')
      hminor)

/-- Input form of the scaled strong-parameter dichotomy: both the crossbar
dichotomy and the strong-path-of-sets-minor-to-grid theorem are explicit
hypotheses, so this composition theorem has no project-contract dependency. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs
    (hcrossInput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          {G : _root_.SimpleGraph V} {ell w g : ℕ},
            2 ≤ g →
              g ^ 2 ≤ ell →
                g ^ 2 ≤ w →
                  CrossbarContract.HasStrongPathOfSetsMinor G ell w →
                    ∃ g' : ℕ, g ≤ cStrong * g' ∧ ContainsGridMinor G g')
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 g ≤ ell →
                      g ^ 2 ≤ w →
                        2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                          cCross * r ^ 2 ≤ g ^ 2 →
                            (∃ g' : ℕ,
                              g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                ContainsGridMinor G g') ∨
                              ∃ r' : ℕ,
                                r ≤ cStrong * r' ∧
                                  ContainsGridMinor G r' := by
  rcases
    gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_crossbarDichotomy_and_largeCaseCutMatchingDataProvider
      hcrossInput hlargeData with
    ⟨cCross, cGrid, hcCross, hcGrid, hmain⟩
  rcases hstrongGrid with ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w g r Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled
  rcases hmain G Hsys hg hpow hmaxDegree hell hw hlarge with hgrid | hstrong
  · exact Or.inl hgrid
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    exact Or.inr (hstrongGrid hr
      (square_le_of_scaled_square_le hcCross hscaled hell')
      (square_le_of_scaled_square_le hcCross hscaled hw')
      hminor)

/-- Scaled-strong-parameter version using the unbundled fixed-round cut
sequence provider and separator-grid provider for the direct branch. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_separatorProviders
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundSeparatorGridProvider
            cRound cScale) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 g ≤ ell →
                      g ^ 2 ≤ w →
                        2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                          cCross * r ^ 2 ≤ g ^ 2 →
                            (∃ g' : ℕ,
                              g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                ContainsGridMinor G g') ∨
                              ∃ r' : ℕ,
                                r ≤ cStrong * r' ∧
                                  ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_largeCaseCutMatchingDataProvider
    (_root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.exists_largeCaseCutMatchingDataProvider_of_unbundled_and_separator
      hproviders)

/-- Supergraph version of
`gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter`. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' := by
  rcases gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G H ell w g r Hsys hHG hg hr hpow hmaxDegree hell hw hlarge
    hscaled
  rcases hmain H Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled with
    hgrid | hgrid
  · rcases hgrid with ⟨g', hbound, hgrid⟩
    exact Or.inl ⟨g', hbound, hgrid.mono hHG⟩
  · rcases hgrid with ⟨r', hbound, hgrid⟩
    exact Or.inr ⟨r', hbound, hgrid.mono hHG⟩

/-- Conditional supergraph version of
`gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter`,
using the cut-matching data provider for the direct crossbar-grid branch. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_largeCaseCutMatchingDataProvider
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' := by
  rcases
    gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_largeCaseCutMatchingDataProvider
      hlargeData with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G H ell w g r Hsys hHG hg hr hpow hmaxDegree hell hw hlarge
    hscaled
  rcases hmain H Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled with
    hgrid | hgrid
  · rcases hgrid with ⟨g', hbound, hgrid⟩
    exact Or.inl ⟨g', hbound, hgrid.mono hHG⟩
  · rcases hgrid with ⟨r', hbound, hgrid⟩
    exact Or.inr ⟨r', hbound, hgrid.mono hHG⟩

/-- Input form of the supergraph scaled-strong-parameter theorem. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs
    (hcrossInput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          {G : _root_.SimpleGraph V} {ell w g : ℕ},
            2 ≤ g →
              g ^ 2 ≤ ell →
                g ^ 2 ≤ w →
                  CrossbarContract.HasStrongPathOfSetsMinor G ell w →
                    ∃ g' : ℕ, g ≤ cStrong * g' ∧ ContainsGridMinor G g')
    (hlargeData :
      ∃ cGrid : ℕ, 0 < cGrid ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.LargeCaseCutMatchingDataProvider.{u}
          cGrid) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' := by
  rcases
    gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs
      hcrossInput hstrongGrid hlargeData with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G H ell w g r Hsys hHG hg hr hpow hmaxDegree hell hw hlarge
    hscaled
  rcases hmain H Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled with
    hgrid | hgrid
  · rcases hgrid with ⟨g', hbound, hgrid⟩
    exact Or.inl ⟨g', hbound, hgrid.mono hHG⟩
  · rcases hgrid with ⟨r', hbound, hgrid⟩
    exact Or.inr ⟨r', hbound, hgrid.mono hHG⟩

/-- Conditional supergraph version using the unbundled fixed-round cut
sequence provider and separator-grid provider for the direct branch. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_separatorProviders
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundSeparatorGridProvider
            cRound cScale) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_largeCaseCutMatchingDataProvider
    (_root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.exists_largeCaseCutMatchingDataProvider_of_unbundled_and_separator
      hproviders)

/-- If the local crossbar dichotomy never returns the strong-minor outcome,
the crossbars obtained at all odd one-based clusters assemble into a grid
minor by the Section 3 assembly theorem. -/
theorem gridMinor_of_hairy_pathOfSets_and_no_strong_outcome :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                cGrid * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                      (¬ ∃ ell' w' : ℕ,
                        g ^ 2 ≤ cCross * ell' ∧
                          g ^ 2 ≤ cCross * w' ∧
                            CrossbarContract.HasStrongPathOfSetsMinor G ell' w') →
                        ∃ g' : ℕ,
                          g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                            ContainsGridMinor G g' := by
  rcases local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor with
    ⟨cCross, hcCross, hodd⟩
  rcases HairyCrossbarGrid.gridMinor_of_hairy_pathOfSets_and_crossbars with
    ⟨cGrid, hcGrid, hgrid⟩
  refine ⟨cCross, cGrid, hcCross, hcGrid, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hlarge hnoStrong
  rcases hodd Hsys hg hpow hlarge with hcrossbars | hstrong
  · exact hgrid G Hsys hg hpow hmaxDegree hell hw hcrossbars
  · exact False.elim (hnoStrong hstrong)

end HairyPathOfSetsSystem
end SimpleGraph
end TwinWidth
