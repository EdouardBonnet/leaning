import «statements-and-proofs».Exponent7.CleanMatchingDichotomy

/-!
# Strength audit for the generic prescribed-matching frontier

The conditional exponent-seven endpoint is intentionally frozen.  This
parallel module records why its remaining generic hypothesis is substantially
stronger than the application needs.

Instantiate `CleanMatchingDichotomyStatement` with the reflexive path packing
on a large node-well-linked terminal set.  Every selected "row" is then a
singleton terminal.  A clean realization of an arbitrary row matching is
therefore a simultaneous routing of the corresponding prescribed terminal
pairs.  In particular, when `g` is even and the matching has `g / 2` edges,
the generic frontier gives arbitrary `g / 2`-linkedness on the selected
`g` terminals unless the graph already contains a `g` by `g` grid minor.

This is a reduction theorem only.  It adds no axiom and is not imported by the
frozen conditional endpoint.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- A simultaneous realization of a prescribed matching on named terminals.

The paths have the prescribed endpoints, stay in `C`, avoid every selected
terminal internally, and are pairwise node-disjoint. -/
structure CleanTerminalMatchingRealization
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (G : _root_.SimpleGraph V) (selected : ι ↪ V)
    (M : RowMatching ι) (C : Finset V) where
  path : M.EdgeIndex → GraphPath G
  source_eq :
    ∀ e, (path e).source = selected (M.left e)
  target_eq :
    ∀ e, (path e).target = selected (M.right e)
  staysIn :
    ∀ e, (path e).vertexSet ⊆ C
  internallyDisjoint_selected :
    ∀ e,
      (path e).InternallyDisjointFromSet
        ((Finset.univ : Finset ι).image selected)
  node_disjoint :
    Pairwise fun e f => GraphPath.NodeDisjoint (path e) (path f)

/-- Embed named selected terminals into the canonical finite index type of
the reflexive path packing on `T`. -/
noncomputable def singletonRowIndexEmbedding
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (T : Finset V) (selected : ι ↪ V)
    (hselected : ∀ x, selected x ∈ T) :
    ι ↪ Fin T.card where
  toFun := fun x => T.equivFin ⟨selected x, hselected x⟩
  inj' := by
    intro x y hxy
    apply selected.injective
    exact congrArg Subtype.val (T.equivFin.injective hxy)

@[simp] theorem singletonRowIndexEmbedding_vertex
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (T : Finset V) (selected : ι ↪ V)
    (hselected : ∀ x, selected x ∈ T) (x : ι) :
    (T.equivFin.symm
      (singletonRowIndexEmbedding T selected hselected x)).1 =
        selected x := by
  change
    (T.equivFin.symm
      (T.equivFin ⟨selected x, hselected x⟩)).1 = selected x
  simp

@[simp] theorem singletonRowPath_vertexSet
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (T : Finset V) (selected : ι ↪ V)
    (hselected : ∀ x, selected x ∈ T) (x : ι) :
    (((PerfectPathPacking.refl G T).toPathPacking.path
      (singletonRowIndexEmbedding T selected hselected x)).vertexSet) =
        {selected x} := by
  classical
  simp [PerfectPathPacking.refl, singletonRowIndexEmbedding]

theorem selectedRowVertexSet_singletonRows
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (T : Finset V) (selected : ι ↪ V)
    (hselected : ∀ x, selected x ∈ T) :
    selectedRowVertexSet
        (PerfectPathPacking.refl G T).toPathPacking
        ((Finset.univ : Finset ι).image
          (singletonRowIndexEmbedding T selected hselected)) =
      (Finset.univ : Finset ι).image selected := by
  classical
  ext v
  constructor
  · intro hv
    rcases
        (mem_selectedRowVertexSet
          (PerfectPathPacking.refl G T).toPathPacking
          ((Finset.univ : Finset ι).image
            (singletonRowIndexEmbedding T selected hselected))).1 hv with
      ⟨r, hr, hvr⟩
    rcases Finset.mem_image.mp hr with ⟨x, _hx, rfl⟩
    have : v = selected x := by
      simpa [singletonRowPath_vertexSet] using hvr
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, this.symm⟩
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨x, _hx, rfl⟩
    apply
      (mem_selectedRowVertexSet
        (PerfectPathPacking.refl G T).toPathPacking
        ((Finset.univ : Finset ι).image
          (singletonRowIndexEmbedding T selected hselected))).2
    refine
      ⟨singletonRowIndexEmbedding T selected hselected x,
        Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, ?_⟩
    simp [singletonRowPath_vertexSet]

/-- A clean matching realization on the singleton-row packing is exactly a
clean prescribed terminal-pair routing. -/
noncomputable def terminalRealizationOfSingletonRows
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (T : Finset V) (selected : ι ↪ V)
    (hselected : ∀ x, selected x ∈ T)
    (M : RowMatching ι) (C : Finset V)
    (B :
      CleanMatchingRealization
        (PerfectPathPacking.refl G T).toPathPacking
        (singletonRowIndexEmbedding T selected hselected) M C) :
    CleanTerminalMatchingRealization G selected M C where
  path := B.path
  source_eq := by
    intro e
    have h := B.source_mem e
    change
      (B.path e).source ∈
        (GraphPath.refl G
          (T.equivFin.symm
            (singletonRowIndexEmbedding T selected hselected
              (M.left e))).1).vertexSet at h
    rw [GraphPath.refl_vertexSet] at h
    exact (Finset.mem_singleton.mp h).trans
      (singletonRowIndexEmbedding_vertex
        T selected hselected (M.left e))
  target_eq := by
    intro e
    have h := B.target_mem e
    change
      (B.path e).target ∈
        (GraphPath.refl G
          (T.equivFin.symm
            (singletonRowIndexEmbedding T selected hselected
              (M.right e))).1).vertexSet at h
    rw [GraphPath.refl_vertexSet] at h
    exact (Finset.mem_singleton.mp h).trans
      (singletonRowIndexEmbedding_vertex
        T selected hselected (M.right e))
  staysIn := B.staysIn
  internallyDisjoint_selected := by
    intro e
    intro v hvPath hvSelected
    apply B.internallyDisjoint_selectedRows e hvPath
    rcases Finset.mem_image.mp hvSelected with ⟨x, _hx, rfl⟩
    apply
      (mem_selectedRowVertexSet
        (PerfectPathPacking.refl G T).toPathPacking
        ((Finset.univ : Finset ι).image
          (singletonRowIndexEmbedding T selected hselected))).2
    refine
      ⟨singletonRowIndexEmbedding T selected hselected x,
        Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, ?_⟩
    simp [PerfectPathPacking.refl, singletonRowIndexEmbedding]
  node_disjoint := B.node_disjoint

/-- The generic clean-matching frontier implies arbitrary prescribed matching
routing on every selected subset of a sufficiently large node-well-linked
terminal set.

For even `g`, taking any matching of cardinality `g / 2` makes this the usual
arbitrary `g / 2`-linkedness conclusion on the selected `g` terminals, modulo
the alternative that a `g` by `g` grid minor already exists. -/
theorem cleanMatchingDichotomy_implies_arbitrary_terminal_matching
    {reserve : ℕ}
    (hDichotomy : CleanMatchingDichotomyStatement.{u} reserve)
    (G : _root_.SimpleGraph V) (g : ℕ)
    (C T : Finset V) (selected : Fin g ↪ V)
    (hselected : ∀ x, selected x ∈ T)
    (M : RowMatching (Fin g))
    (hg : 2 ≤ g)
    (hsize : reserve * g ^ 2 ≤ T.card)
    (hwell : NodeWellLinkedIn G C T)
    (hMcard : M.card ≤ g / 2) :
    ContainsGridMinor G g ∨
      Nonempty (CleanTerminalMatchingRealization G selected M C) := by
  classical
  let R : PathPacking G T T :=
    (PerfectPathPacking.refl G T).toPathPacking
  let row : Fin g ↪ R.Index :=
    singletonRowIndexEmbedding T selected hselected
  have hRcard : R.card = T.card := by
    simpa [R] using PerfectPathPacking.refl_card G T
  have hstay : R.StaysIn C := by
    intro i v hv
    have hvEq : v = (T.equivFin.symm i).1 := by
      simpa [R, PerfectPathPacking.refl] using hv
    rw [hvEq]
    exact hwell.1 (T.equivFin.symm i).2
  have hsource : R.sourceSet = T :=
    R.sourceSet_eq_left_of_card_eq hRcard
  have hRwell : NodeWellLinkedIn G C R.sourceSet := by
    rw [hsource]
    exact hwell
  rcases
      hDichotomy G g R C row M hg
        (by simpa [hRcard] using hsize) hstay hRwell hMcard with
    hgrid | hrealization
  · exact Or.inl hgrid
  · exact Or.inr
      ⟨terminalRealizationOfSingletonRows
        T selected hselected M C hrealization.some⟩

end CutResponder
end Exponent7
end SimpleGraph
