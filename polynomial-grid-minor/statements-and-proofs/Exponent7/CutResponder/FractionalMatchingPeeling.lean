import «statements-and-proofs».Exponent7.CutResponder.ActiveCutResponder

/-!
# Peeling constant-fraction batches into a perfect matching

This is the finite combinatorial core of Task D.  A partial batch injectively
matches some vertices of two equal residual sides.  Repeatedly delete those
endpoints and ask the responder on the residual sides.  Strong induction on
the residual cardinality produces a bijection of the original sides.

The theorem in this file proves termination and the exact matching.  The
sharper logarithmic bound on `batchCount` is intentionally kept separate from
the construction.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- One endpoint-injective partial matching between residual sides. -/
structure FractionalMatchingBatch
    (U W : Finset X) (responseConstant : ℕ) where
  Edge : Type u
  [edgeFintype : Fintype Edge]
  [edgeDecidableEq : DecidableEq Edge]
  left : Edge → {x : X // x ∈ U}
  right : Edge → {x : X // x ∈ W}
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  fraction : U.card ≤ responseConstant * Fintype.card Edge

namespace FractionalMatchingBatch

instance {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c) : Fintype K.Edge :=
  K.edgeFintype

instance {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c) : DecidableEq K.Edge :=
  K.edgeDecidableEq

/-- Left endpoints consumed by a batch. -/
noncomputable def leftSet
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c) : Finset X :=
  Finset.univ.image fun e : K.Edge => (K.left e).1

/-- Right endpoints consumed by a batch. -/
noncomputable def rightSet
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c) : Finset X :=
  Finset.univ.image fun e : K.Edge => (K.right e).1

theorem left_mem_leftSet
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c) (e : K.Edge) :
    (K.left e).1 ∈ K.leftSet := by
  classical
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩

theorem right_mem_rightSet
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c) (e : K.Edge) :
    (K.right e).1 ∈ K.rightSet := by
  classical
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩

theorem leftSet_subset
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c) :
    K.leftSet ⊆ U := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨e, _he, rfl⟩
  exact (K.left e).2

theorem rightSet_subset
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c) :
    K.rightSet ⊆ W := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨e, _he, rfl⟩
  exact (K.right e).2

@[simp] theorem leftSet_card
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c) :
    K.leftSet.card = Fintype.card K.Edge := by
  classical
  rw [leftSet, Finset.card_image_of_injective, Finset.card_univ]
  intro e f hef
  apply K.left_injective
  exact Subtype.ext hef

@[simp] theorem rightSet_card
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c) :
    K.rightSet.card = Fintype.card K.Edge := by
  classical
  rw [rightSet, Finset.card_image_of_injective, Finset.card_univ]
  intro e f hef
  apply K.right_injective
  exact Subtype.ext hef

/-- A response to a nonempty residual pair necessarily consumes at least one
endpoint, independently of the value of the response constant. -/
theorem edge_card_pos
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c)
    (hU : U.Nonempty) :
    0 < Fintype.card K.Edge := by
  by_contra hzero
  have hcard : Fintype.card K.Edge = 0 := by omega
  have hfraction := K.fraction
  rw [hcard, Nat.mul_zero] at hfraction
  exact (not_lt_of_ge hfraction) hU.card_pos

/-- The unmatched sides after one partial batch. -/
noncomputable def residualLeft
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c) : Finset X :=
  U \ K.leftSet

noncomputable def residualRight
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c) : Finset X :=
  W \ K.rightSet

theorem residual_card_eq
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c)
    (hcard : U.card = W.card) :
    K.residualLeft.card = K.residualRight.card := by
  classical
  rw [residualLeft, residualRight,
    Finset.card_sdiff_of_subset K.leftSet_subset,
    Finset.card_sdiff_of_subset K.rightSet_subset,
    K.leftSet_card, K.rightSet_card, hcard]

theorem residual_disjoint
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c)
    (hdisjoint : Disjoint U W) :
    Disjoint K.residualLeft K.residualRight :=
  hdisjoint.mono Finset.sdiff_subset Finset.sdiff_subset

theorem residualLeft_card_lt
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c)
    (hU : U.Nonempty) :
    K.residualLeft.card < U.card := by
  classical
  have hedge := K.edge_card_pos hU
  rw [residualLeft,
    Finset.card_sdiff_of_subset K.leftSet_subset,
    K.leftSet_card]
  have hle :
      Fintype.card K.Edge ≤ U.card := by
    calc
      Fintype.card K.Edge = K.leftSet.card :=
        K.leftSet_card.symm
      _ ≤ U.card := Finset.card_le_card K.leftSet_subset
  omega

end FractionalMatchingBatch

/-- A complete matching assembled from finitely many partial batches. -/
structure PeeledMatching
    (U W : Finset X) where
  Edge : Type u
  [edgeFintype : Fintype Edge]
  [edgeDecidableEq : DecidableEq Edge]
  left : Edge → {x : X // x ∈ U}
  right : Edge → {x : X // x ∈ W}
  left_bijective : Function.Bijective left
  right_bijective : Function.Bijective right
  batchCount : ℕ

namespace PeeledMatching

instance {U W : Finset X} (M : PeeledMatching U W) : Fintype M.Edge :=
  M.edgeFintype

instance {U W : Finset X} (M : PeeledMatching U W) : DecidableEq M.Edge :=
  M.edgeDecidableEq

/-- The abstract perfect matching represented by a peeled matching. -/
noncomputable def toEquiv
    {U W : Finset X} (M : PeeledMatching U W) :
    {x : X // x ∈ U} ≃ {x : X // x ∈ W} :=
  (Equiv.ofBijective M.left M.left_bijective).symm.trans
    (Equiv.ofBijective M.right M.right_bijective)

/-- Empty equal sides need no batch. -/
noncomputable def empty
    {U W : Finset X} (hU : U = ∅) (hW : W = ∅) :
    PeeledMatching U W := by
  classical
  let e :
      {x : X // x ∈ U} ≃ {x : X // x ∈ W} := by
    subst U
    subst W
    exact Equiv.refl _
  exact
    { Edge := {x : X // x ∈ U}
      left := id
      right := e
      left_bijective := Function.bijective_id
      right_bijective := e.bijective
      batchCount := 0 }

/-- Add one partial batch in front of a complete matching of its residual
sides. -/
noncomputable def cons
    {U W : Finset X} {c : ℕ}
    (K : FractionalMatchingBatch U W c)
    (M : PeeledMatching K.residualLeft K.residualRight) :
    PeeledMatching U W := by
  classical
  let left' :
      K.Edge ⊕ M.Edge → {x : X // x ∈ U}
    | Sum.inl e => K.left e
    | Sum.inr e =>
        ⟨(M.left e).1,
          (Finset.mem_sdiff.mp (M.left e).2).1⟩
  let right' :
      K.Edge ⊕ M.Edge → {x : X // x ∈ W}
    | Sum.inl e => K.right e
    | Sum.inr e =>
        ⟨(M.right e).1,
          (Finset.mem_sdiff.mp (M.right e).2).1⟩
  have hleftInj : Function.Injective left' := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            simp only [left'] at hab
            exact congrArg Sum.inl (K.left_injective hab)
        | inr b =>
            exfalso
            have hused : (K.left a).1 ∈ K.leftSet :=
              K.left_mem_leftSet a
            have hnot :
                (M.left b).1 ∉ K.leftSet :=
              (Finset.mem_sdiff.mp (M.left b).2).2
            have hv :
                (K.left a).1 = (M.left b).1 :=
              congrArg Subtype.val hab
            exact hnot (hv ▸ hused)
    | inr a =>
        cases b with
        | inl b =>
            exfalso
            have hnot :
                (M.left a).1 ∉ K.leftSet :=
              (Finset.mem_sdiff.mp (M.left a).2).2
            have hused : (K.left b).1 ∈ K.leftSet :=
              K.left_mem_leftSet b
            have hv :
                (M.left a).1 = (K.left b).1 :=
              congrArg Subtype.val hab
            exact hnot (hv.symm ▸ hused)
        | inr b =>
            simp only [left'] at hab
            have hv :
                (M.left a).1 = (M.left b).1 :=
              congrArg
                (fun z : {x : X // x ∈ U} => z.1) hab
            exact congrArg Sum.inr
              (M.left_bijective.1 (Subtype.ext hv))
  have hrightInj : Function.Injective right' := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            simp only [right'] at hab
            exact congrArg Sum.inl (K.right_injective hab)
        | inr b =>
            exfalso
            have hused : (K.right a).1 ∈ K.rightSet :=
              K.right_mem_rightSet a
            have hnot :
                (M.right b).1 ∉ K.rightSet :=
              (Finset.mem_sdiff.mp (M.right b).2).2
            have hv :
                (K.right a).1 = (M.right b).1 :=
              congrArg Subtype.val hab
            exact hnot (hv ▸ hused)
    | inr a =>
        cases b with
        | inl b =>
            exfalso
            have hnot :
                (M.right a).1 ∉ K.rightSet :=
              (Finset.mem_sdiff.mp (M.right a).2).2
            have hused : (K.right b).1 ∈ K.rightSet :=
              K.right_mem_rightSet b
            have hv :
                (M.right a).1 = (K.right b).1 :=
              congrArg Subtype.val hab
            exact hnot (hv.symm ▸ hused)
        | inr b =>
            simp only [right'] at hab
            have hv :
                (M.right a).1 = (M.right b).1 :=
              congrArg
                (fun z : {x : X // x ∈ W} => z.1) hab
            exact congrArg Sum.inr
              (M.right_bijective.1 (Subtype.ext hv))
  have hleftSurj : Function.Surjective left' := by
    intro x
    by_cases hx : x.1 ∈ K.leftSet
    · rcases Finset.mem_image.mp hx with ⟨e, _he, heq⟩
      exact ⟨Sum.inl e, Subtype.ext heq⟩
    · let xr : {x : X // x ∈ K.residualLeft} :=
        ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩
      rcases M.left_bijective.2 xr with ⟨e, he⟩
      refine ⟨Sum.inr e, ?_⟩
      apply Subtype.ext
      change (M.left e).1 = x.1
      have hv :
          (M.left e).1 = xr.1 :=
        congrArg
          (fun z : {x : X // x ∈ K.residualLeft} => z.1) he
      simpa [xr] using hv
  have hrightSurj : Function.Surjective right' := by
    intro x
    by_cases hx : x.1 ∈ K.rightSet
    · rcases Finset.mem_image.mp hx with ⟨e, _he, heq⟩
      exact ⟨Sum.inl e, Subtype.ext heq⟩
    · let xr : {x : X // x ∈ K.residualRight} :=
        ⟨x.1, Finset.mem_sdiff.mpr ⟨x.2, hx⟩⟩
      rcases M.right_bijective.2 xr with ⟨e, he⟩
      refine ⟨Sum.inr e, ?_⟩
      apply Subtype.ext
      change (M.right e).1 = x.1
      have hv :
          (M.right e).1 = xr.1 :=
        congrArg
          (fun z : {x : X // x ∈ K.residualRight} => z.1) he
      simpa [xr] using hv
  exact
    { Edge := K.Edge ⊕ M.Edge
      left := left'
      right := right'
      left_bijective := ⟨hleftInj, hleftSurj⟩
      right_bijective := ⟨hrightInj, hrightSurj⟩
      batchCount := M.batchCount + 1 }

end PeeledMatching

/-- A constant-fraction responder for arbitrary nonempty residual sides. -/
def FractionalBatchResponder
    (responseConstant : ℕ) : Prop :=
  ∀ (U W : Finset X),
    Disjoint U W →
    U.card = W.card →
    U.Nonempty →
    Nonempty (FractionalMatchingBatch U W responseConstant)

/-- Repeated responses terminate and assemble an exact perfect matching.
The elementary bound uses at most one batch per consumed left endpoint. -/
theorem exists_peeledMatching_with_batchCount_le
    {responseConstant : ℕ}
    (respond : FractionalBatchResponder
      (X := X) responseConstant)
    (U W : Finset X)
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card) :
    ∃ M : PeeledMatching U W, M.batchCount ≤ U.card := by
  classical
  induction hn : U.card using Nat.strong_induction_on generalizing U W with
  | h n ih =>
      subst hn
      by_cases hUempty : U = ∅
      · have hWcard : W.card = 0 := by simpa [hUempty] using hcard.symm
        have hWempty : W = ∅ := Finset.card_eq_zero.mp hWcard
        exact ⟨PeeledMatching.empty hUempty hWempty, by
          simp [PeeledMatching.empty, hUempty]⟩
      · have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hUempty
        rcases respond U W hdisjoint hcard hUne with ⟨K⟩
        have hlt : K.residualLeft.card < U.card :=
          K.residualLeft_card_lt hUne
        rcases ih K.residualLeft.card hlt
            K.residualLeft K.residualRight
            (FractionalMatchingBatch.residual_disjoint K hdisjoint)
            (FractionalMatchingBatch.residual_card_eq K hcard) rfl with
          ⟨M, hMcount⟩
        refine ⟨PeeledMatching.cons K M, ?_⟩
        dsimp [PeeledMatching.cons]
        omega

/-- Nonempty wrapper for consumers which only need the resulting perfect
matching. -/
theorem exists_peeledMatching_of_fractionalBatchResponder
    {responseConstant : ℕ}
    (respond : FractionalBatchResponder
      (X := X) responseConstant)
    (U W : Finset X)
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card) :
    Nonempty (PeeledMatching U W) := by
  rcases
      exists_peeledMatching_with_batchCount_le
        respond U W hdisjoint hcard with
    ⟨M, _hcount⟩
  exact ⟨M⟩

end CutResponder
end Exponent7
end SimpleGraph
