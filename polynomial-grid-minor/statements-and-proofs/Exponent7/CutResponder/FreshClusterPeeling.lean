import «statements-and-proofs».Exponent7.CutResponder.CleanResidualResponder
import «statements-and-proofs».Exponent7.CutResponder.FractionalPeelingLogBound

/-!
# Fresh-cluster geometric peeling

This module is the proof-producing bridge from a sequence of clean
constant-fraction batches to one exact matching with concrete host paths.
Each batch is assigned a different finite slot.  Paths in different slots are
separated by disjoint regions; paths in one slot are supplied pairwise
node-disjoint by the responder.

The bounded construction uses exactly

```
responseConstant * (Nat.log 2 initialCardinality + 1)
```

available slots.  If all slots were exhausted while unmatched vertices
remained, their batch sizes would form an unfinished peeling prefix of that
length, contradicting `FractionalPeelingPrefixProfile.length_lt_mul_log_succ`.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u v

open Finset

variable {V : Type u} {X : Type v}
variable [Fintype V] [DecidableEq V]
variable [Fintype X] [DecidableEq X]
variable {G : _root_.SimpleGraph V}

/-- One fractional matching batch together with its concrete clean paths in a
specified host region. -/
structure CleanGeometricFractionalBatch
    (rows : X → GraphPath G)
    (cleanSet region : Finset V)
    (U W : Finset X) (responseConstant : ℕ) where
  matching : FractionalMatchingBatch U W responseConstant
  path : matching.Edge → GraphPath G
  source_mem_row :
    ∀ e, (path e).source ∈ (rows (matching.left e).1).vertexSet
  target_mem_row :
    ∀ e, (path e).target ∈ (rows (matching.right e).1).vertexSet
  stays : ∀ e, (path e).vertexSet ⊆ region
  node_disjoint :
    ∀ {e f}, e ≠ f → GraphPath.NodeDisjoint (path e) (path f)
  internallyDisjoint_clean :
    ∀ e, (path e).InternallyDisjointFromSet cleanSet

namespace CleanGeometricFractionalBatch

instance
    {rows : X → GraphPath G} {cleanSet region : Finset V}
    {U W : Finset X} {c : ℕ}
    (K : CleanGeometricFractionalBatch
      rows cleanSet region U W c) :
    Fintype K.matching.Edge :=
  K.matching.edgeFintype

instance
    {rows : X → GraphPath G} {cleanSet region : Finset V}
    {U W : Finset X} {c : ℕ}
    (K : CleanGeometricFractionalBatch
      rows cleanSet region U W c) :
    DecidableEq K.matching.Edge :=
  K.matching.edgeDecidableEq

end CleanGeometricFractionalBatch

/-- A finite scheduled responder: slot `t` returns a clean batch whose paths
stay in `regions t`. -/
def FiniteCleanGeometricBatchResponder
    (rows : X → GraphPath G)
    (cleanSet : Finset V)
    (regions : Fin budget → Finset V)
    (responseConstant : ℕ) : Prop :=
  ∀ (t : Fin budget) (U W : Finset X),
    Disjoint U W →
    U.card = W.card →
    U.Nonempty →
    Nonempty
      (CleanGeometricFractionalBatch
        rows cleanSet (regions t) U W responseConstant)

/-- An exact perfect matching, its logarithmic peeling profile, and a clean
host path for every matching edge.  The slot lower bound is used while
prepending a fresh batch. -/
structure CleanGeometricPeeledMatching
    (rows : X → GraphPath G)
    (cleanSet : Finset V)
    (regions : Fin budget → Finset V)
    (U W : Finset X) (responseConstant start : ℕ) where
  matching : ProfiledPeeledMatching U W responseConstant
  path : matching.Edge → GraphPath G
  slot : matching.Edge → Fin budget
  slot_lower : ∀ e, start ≤ (slot e).1
  source_mem_row :
    ∀ e, (path e).source ∈
      (rows (matching.left e).1).vertexSet
  target_mem_row :
    ∀ e, (path e).target ∈
      (rows (matching.right e).1).vertexSet
  stays : ∀ e, (path e).vertexSet ⊆ regions (slot e)
  node_disjoint :
    ∀ {e f}, e ≠ f → GraphPath.NodeDisjoint (path e) (path f)
  internallyDisjoint_clean :
    ∀ e, (path e).InternallyDisjointFromSet cleanSet

namespace CleanGeometricPeeledMatching

/-- There are no edges to realize when both sides are empty. -/
noncomputable def empty
    {rows : X → GraphPath G}
    {cleanSet : Finset V}
    {regions : Fin budget → Finset V}
    {U W : Finset X} {c start : ℕ}
    (hU : U = ∅) (hW : W = ∅) :
    CleanGeometricPeeledMatching
      rows cleanSet regions U W c start := by
  classical
  let M : ProfiledPeeledMatching U W c :=
    ProfiledPeeledMatching.empty hU hW
  have noEdge : ∀ e : M.Edge, False := by
    intro e
    have he := (M.left e).2
    simpa [hU] using he
  exact
    { matching := M
      path := fun e => False.elim (noEdge e)
      slot := fun e => False.elim (noEdge e)
      slot_lower := fun e => False.elim (noEdge e)
      source_mem_row := fun e => False.elim (noEdge e)
      target_mem_row := fun e => False.elim (noEdge e)
      stays := fun e => False.elim (noEdge e)
      node_disjoint := fun {e} => False.elim (noEdge e)
      internallyDisjoint_clean := fun e => False.elim (noEdge e) }

/-- Prepend the clean batch in slot `start` to a clean realization using only
later slots. -/
noncomputable def cons
    {rows : X → GraphPath G}
    {cleanSet : Finset V}
    {regions : Fin budget → Finset V}
    {U W : Finset X} {c start : ℕ}
    (hstart : start < budget)
    (hregions :
      Pairwise fun s t : Fin budget =>
        Disjoint (regions s) (regions t))
    (K : CleanGeometricFractionalBatch
      rows cleanSet (regions ⟨start, hstart⟩) U W c)
    (hU : U.Nonempty)
    (M : CleanGeometricPeeledMatching
      rows cleanSet regions
      K.matching.residualLeft K.matching.residualRight
      c (start + 1)) :
    CleanGeometricPeeledMatching
      rows cleanSet regions U W c start := by
  classical
  let N : ProfiledPeeledMatching U W c :=
    ProfiledPeeledMatching.cons K.matching hU M.matching
  let path' : N.Edge → GraphPath G
    | Sum.inl e => K.path e
    | Sum.inr e => M.path e
  let slot' : N.Edge → Fin budget
    | Sum.inl _ => ⟨start, hstart⟩
    | Sum.inr e => M.slot e
  have hslotLower : ∀ e, start ≤ (slot' e).1 := by
    intro e
    cases e with
    | inl e =>
        simp [slot']
    | inr e =>
        exact le_trans (Nat.le_succ start) (M.slot_lower e)
  have hsource :
      ∀ e, (path' e).source ∈
        (rows (N.left e).1).vertexSet := by
    intro e
    cases e with
    | inl e =>
        simpa [path', N, ProfiledPeeledMatching.cons,
          PeeledMatching.cons] using K.source_mem_row e
    | inr e =>
        simpa [path', N, ProfiledPeeledMatching.cons,
          PeeledMatching.cons] using M.source_mem_row e
  have htarget :
      ∀ e, (path' e).target ∈
        (rows (N.right e).1).vertexSet := by
    intro e
    cases e with
    | inl e =>
        simpa [path', N, ProfiledPeeledMatching.cons,
          PeeledMatching.cons] using K.target_mem_row e
    | inr e =>
        simpa [path', N, ProfiledPeeledMatching.cons,
          PeeledMatching.cons] using M.target_mem_row e
  have hstays :
      ∀ e, (path' e).vertexSet ⊆ regions (slot' e) := by
    intro e
    cases e with
    | inl e =>
        simpa [path', slot'] using K.stays e
    | inr e =>
        simpa [path', slot'] using M.stays e
  have hnode :
      ∀ {e f : N.Edge}, e ≠ f →
        GraphPath.NodeDisjoint (path' e) (path' f) := by
    intro e f hef
    cases e with
    | inl e =>
        cases f with
        | inl f =>
            apply K.node_disjoint
            intro heq
            exact hef (congrArg Sum.inl heq)
        | inr f =>
            have hslotNe :
                (⟨start, hstart⟩ : Fin budget) ≠ M.slot f := by
              intro heq
              have hval :
                  start = (M.slot f).1 :=
                congrArg Fin.val heq
              have hlower := M.slot_lower f
              omega
            exact (hregions hslotNe).mono
              (K.stays e) (M.stays f)
    | inr e =>
        cases f with
        | inl f =>
            have hslotNe :
                M.slot e ≠ (⟨start, hstart⟩ : Fin budget) := by
              intro heq
              have hval :
                  (M.slot e).1 = start :=
                congrArg Fin.val heq
              have hlower := M.slot_lower e
              omega
            exact (hregions hslotNe).mono
              (M.stays e) (K.stays f)
        | inr f =>
            apply M.node_disjoint
            intro heq
            exact hef (congrArg Sum.inr heq)
  exact
    { matching := N
      path := path'
      slot := slot'
      slot_lower := hslotLower
      source_mem_row := hsource
      target_mem_row := htarget
      stays := hstays
      node_disjoint := hnode
      internallyDisjoint_clean := by
        intro e
        cases e with
        | inl e =>
            simpa [path'] using K.internallyDisjoint_clean e
        | inr e =>
            simpa [path'] using M.internallyDisjoint_clean e }

end CleanGeometricPeeledMatching

/-- With `fuel` consecutive fresh slots beginning at `start`, either peeling
finishes, or it exposes an unfinished numerical prefix of exactly that
length. -/
theorem cleanGeometricPeeling_attempt
    {rows : X → GraphPath G}
    {cleanSet : Finset V}
    {regions : Fin budget → Finset V}
    {c : ℕ}
    (respond :
      FiniteCleanGeometricBatchResponder
        rows cleanSet regions c)
    (hregions :
      Pairwise fun s t : Fin budget =>
        Disjoint (regions s) (regions t))
    (start fuel : ℕ)
    (hslots : start + fuel ≤ budget)
    (U W : Finset X)
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card) :
    (∃ M : CleanGeometricPeeledMatching
        rows cleanSet regions U W c start,
        M.matching.batchCount ≤ fuel) ∨
      ∃ ks r,
        FractionalPeelingPrefixProfile c U.card ks r ∧
        0 < r ∧ ks.length = fuel := by
  classical
  induction fuel generalizing start U W with
  | zero =>
      by_cases hUempty : U = ∅
      · have hWcard : W.card = 0 := by
          simpa [hUempty] using hcard.symm
        have hWempty : W = ∅ := Finset.card_eq_zero.mp hWcard
        exact Or.inl
          ⟨CleanGeometricPeeledMatching.empty hUempty hWempty,
            by simp [CleanGeometricPeeledMatching.empty,
              ProfiledPeeledMatching.empty,
              PeeledMatching.empty]⟩
      · exact Or.inr
          ⟨[], U.card,
            FractionalPeelingPrefixProfile.nil U.card,
            (Finset.nonempty_iff_ne_empty.mpr hUempty).card_pos,
            rfl⟩
  | succ fuel ih =>
      by_cases hUempty : U = ∅
      · have hWcard : W.card = 0 := by
          simpa [hUempty] using hcard.symm
        have hWempty : W = ∅ := Finset.card_eq_zero.mp hWcard
        exact Or.inl
          ⟨CleanGeometricPeeledMatching.empty hUempty hWempty,
            by simp [CleanGeometricPeeledMatching.empty,
              ProfiledPeeledMatching.empty,
              PeeledMatching.empty]⟩
      · have hUne : U.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hUempty
        have hstart : start < budget := by
          omega
        rcases
            respond ⟨start, hstart⟩ U W
              hdisjoint hcard hUne with
          ⟨K⟩
        have hnextSlots : start + 1 + fuel ≤ budget := by
          omega
        have hresDisjoint :
            Disjoint K.matching.residualLeft
              K.matching.residualRight :=
          K.matching.residual_disjoint hdisjoint
        have hresCard :
            K.matching.residualLeft.card =
              K.matching.residualRight.card :=
          K.matching.residual_card_eq hcard
        rcases ih (start + 1) hnextSlots
            K.matching.residualLeft
            K.matching.residualRight
            hresDisjoint hresCard with
          hcomplete | hexhausted
        · rcases hcomplete with ⟨M, hMcount⟩
          let N :=
            CleanGeometricPeeledMatching.cons
              hstart hregions K hUne M
          exact Or.inl ⟨N, by
            dsimp [N, CleanGeometricPeeledMatching.cons,
              ProfiledPeeledMatching.cons, PeeledMatching.cons]
            omega⟩
        · rcases hexhausted with
            ⟨ks, r, hprefix, hrpos, hlen⟩
          have hkPos :
              0 < Fintype.card K.matching.Edge :=
            K.matching.edge_card_pos hUne
          have hkLe :
              Fintype.card K.matching.Edge ≤ U.card := by
            calc
              Fintype.card K.matching.Edge =
                  K.matching.leftSet.card :=
                K.matching.leftSet_card.symm
              _ ≤ U.card :=
                Finset.card_le_card K.matching.leftSet_subset
          have hres :
              U.card - Fintype.card K.matching.Edge =
                K.matching.residualLeft.card := by
            rw [FractionalMatchingBatch.residualLeft,
              Finset.card_sdiff_of_subset
                K.matching.leftSet_subset,
              K.matching.leftSet_card]
          refine Or.inr
            ⟨Fintype.card K.matching.Edge :: ks, r, ?_, hrpos, ?_⟩
          · apply FractionalPeelingPrefixProfile.cons
              hkPos hkLe K.matching.fraction
            rw [hres]
            exact hprefix
          · simp [hlen]

/-- The exact fresh-slot theorem.  The strict prefix bound rules out the
fuel-exhausted branch. -/
theorem exists_cleanGeometricPeeledMatching
    {rows : X → GraphPath G}
    {cleanSet : Finset V}
    {regions : Fin budget → Finset V}
    {c : ℕ}
    (respond :
      FiniteCleanGeometricBatchResponder
        rows cleanSet regions c)
    (hregions :
      Pairwise fun s t : Fin budget =>
        Disjoint (regions s) (regions t))
    (hc : 0 < c)
    (U W : Finset X)
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card)
    (hbudget :
      c * (Nat.log 2 U.card + 1) ≤ budget) :
    ∃ M : CleanGeometricPeeledMatching
        rows cleanSet regions U W c 0,
      M.matching.batchCount ≤
        c * (Nat.log 2 U.card + 1) := by
  let fuel := c * (Nat.log 2 U.card + 1)
  rcases cleanGeometricPeeling_attempt
      respond hregions 0 fuel (by simpa [fuel] using hbudget)
      U W hdisjoint hcard with
    hcomplete | hexhausted
  · rcases hcomplete with ⟨M, hMcount⟩
    exact ⟨M, by simpa [fuel] using hMcount⟩
  · rcases hexhausted with
      ⟨ks, r, hprefix, hrpos, hlen⟩
    have hlt := hprefix.length_lt_mul_log_succ hc hrpos
    rw [hlen] at hlt
    exact False.elim (Nat.lt_irrefl _ hlt)

end CutResponder
end Exponent7
end SimpleGraph
