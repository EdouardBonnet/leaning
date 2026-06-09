import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

namespace GallaiMilgramAux

variable {V : Type u}

/-- The set of last vertices of the paths in a finite list-path family. -/
def TerminalSet (P : Finset (List V)) : Set V :=
  {v | ∃ p : List V, p ∈ P ∧ v ∈ p.getLast?}

/-- A fixed path cover has one representative on each path, and these representatives are independent. -/
def PathCoverHasIndependentRepresentatives (D : DirectedGraph V) (P : Finset (List V)) :
    Prop :=
  ∃ rep : {p : List V // p ∈ P} → V,
    (∀ p, rep p ∈ p.1) ∧ DirectedIndependentSet D (Set.range rep)

/-- A path cover whose terminal set is inclusion-minimal among terminal sets of path covers. -/
def InclusionMinimalTerminalPathCover (D : DirectedGraph V) (P : Finset (List V)) : Prop :=
  IsDirectedPathCover D P ∧
    ∀ Q : Finset (List V), IsDirectedPathCover D Q → ¬ TerminalSet Q ⊂ TerminalSet P

/-- A path cover of a specified finite vertex set. -/
def IsDirectedPathCoverOn (D : DirectedGraph V) (X : Finset V)
    (P : Finset (List V)) : Prop :=
  (∀ p ∈ P, IsDirectedPath D p) ∧
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (listVertexSet p) (listVertexSet q)) ∧
      (∀ p ∈ P, ∀ v ∈ p, v ∈ X) ∧
        ∀ v ∈ X, ∃ p ∈ P, v ∈ p

/-- A cover of `X` whose terminal set is inclusion-minimal among covers of `X`. -/
def InclusionMinimalTerminalPathCoverOn (D : DirectedGraph V) (X : Finset V)
    (P : Finset (List V)) : Prop :=
  IsDirectedPathCoverOn D X P ∧
    ∀ Q : Finset (List V), IsDirectedPathCoverOn D X Q → ¬ TerminalSet Q ⊂ TerminalSet P

lemma terminalSet_subset_of_pathCoverOn {D : DirectedGraph V} {X : Finset V}
    {P : Finset (List V)} (hcover : IsDirectedPathCoverOn D X P) :
    TerminalSet P ⊆ (X : Set V) := by
  intro v hv
  rcases hv with ⟨p, hp, hvlast⟩
  rcases List.mem_getLast?_eq_getLast hvlast with ⟨hpne, rfl⟩
  exact hcover.2.2.1 p hp (p.getLast hpne) (List.getLast_mem hpne)

lemma terminalSet_finite_of_pathCoverOn {D : DirectedGraph V} {X : Finset V}
    {P : Finset (List V)} (hcover : IsDirectedPathCoverOn D X P) :
    (TerminalSet P).Finite :=
  (Finset.finite_toSet X).subset (terminalSet_subset_of_pathCoverOn hcover)

lemma pathCoverOn_univ_to_pathCover (D : DirectedGraph V) [Fintype V]
    {P : Finset (List V)}
    (hcover : IsDirectedPathCoverOn D (Finset.univ : Finset V) P) :
    IsDirectedPathCover D P := by
  exact ⟨hcover.1, hcover.2.1, fun v => hcover.2.2.2 v (Finset.mem_univ v)⟩

lemma singleton_path_cover_on (D : DirectedGraph V) [DecidableEq V] (X : Finset V) :
    IsDirectedPathCoverOn D (X.image id) (X.image fun v => [v]) := by
  classical
  constructor
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨v, _hv, rfl⟩
    simp [IsDirectedPath, IsDirectedWalkList]
  constructor
  · intro p hp q hq hpq
    rcases Finset.mem_image.mp hp with ⟨v, _hv, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨w, _hw, rfl⟩
    have hvw : v ≠ w := by
      intro h
      exact hpq (by simp [h])
    refine Set.disjoint_left.mpr ?_
    intro x hx hy
    simp [listVertexSet] at hx hy
    subst x
    exact hvw hy
  constructor
  · intro p hp x hx
    rcases Finset.mem_image.mp hp with ⟨v, hv, rfl⟩
    simp at hx
    subst x
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  · intro v hv
    rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
    refine ⟨[w], ?_, by simp⟩
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

lemma singleton_path_cover_on_self (D : DirectedGraph V) [DecidableEq V] (X : Finset V) :
    IsDirectedPathCoverOn D X (X.image fun v => [v]) := by
  simpa using singleton_path_cover_on D X

lemma exists_path_cover_on (D : DirectedGraph V) [DecidableEq V] (X : Finset V) :
    ∃ P : Finset (List V), IsDirectedPathCoverOn D X P :=
  ⟨X.image fun v => [v], singleton_path_cover_on_self D X⟩

lemma directedIndependentSet_mono {D : DirectedGraph V} {A B : Set V}
    (hB : DirectedIndependentSet D B) (hAB : A ⊆ B) :
    DirectedIndependentSet D A := by
  intro x y hx hy hxy
  exact hB (hAB hx) (hAB hy) hxy

lemma exists_terminal_arc_of_not_directedIndependent {D : DirectedGraph V} {S : Set V}
    (h : ¬ DirectedIndependentSet D S) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ (D x y ∨ D y x) := by
  classical
  rw [DirectedIndependentSet] at h
  push Not at h
  rcases h with ⟨x, y, hx, hy, hxy, hbad⟩
  refine ⟨x, hx, y, hy, hxy, ?_⟩
  by_cases hDxy : D x y
  · exact Or.inl hDxy
  · exact Or.inr (hbad hDxy)

lemma path_eq_of_common_vertex_pathCoverOn {D : DirectedGraph V} {X : Finset V}
    {P : Finset (List V)} (hcover : IsDirectedPathCoverOn D X P)
    {p q : List V} (hp : p ∈ P) (hq : q ∈ P) {x : V}
    (hxp : x ∈ p) (hxq : x ∈ q) :
    p = q := by
  by_contra hpq
  exact Set.disjoint_left.mp (hcover.2.1 p hp q hq hpq) hxp hxq

lemma path_eq_of_common_terminal_pathCoverOn {D : DirectedGraph V} {X : Finset V}
    {P : Finset (List V)} (hcover : IsDirectedPathCoverOn D X P)
    {p q : List V} (hp : p ∈ P) (hq : q ∈ P) {x : V}
    (hxp : x ∈ p.getLast?) (hxq : x ∈ q.getLast?) :
    p = q := by
  rcases List.mem_getLast?_eq_getLast hxp with ⟨hpne, rfl⟩
  rcases List.mem_getLast?_eq_getLast hxq with ⟨hqne, hxq_last⟩
  exact path_eq_of_common_vertex_pathCoverOn hcover hp hq
    (List.getLast_mem hpne) (by simpa [hxq_last] using List.getLast_mem hqne)

lemma terminal_mem_of_path {P : Finset (List V)} {p : List V} (hp : p ∈ P)
    (hn : p ≠ []) :
    p.getLast hn ∈ TerminalSet P := by
  refine ⟨p, hp, ?_⟩
  rw [List.getLast?_eq_getLast hn]
  simp

lemma directedIndependent_terminal_representatives {D : DirectedGraph V}
    {P : Finset (List V)} (hcover : IsDirectedPathCover D P)
    (hind : DirectedIndependentSet D (TerminalSet P)) :
    PathCoverHasIndependentRepresentatives D P := by
  classical
  let rep : {p : List V // p ∈ P} → V := fun p =>
    p.1.getLast (hcover.1 p.1 p.2).2.1
  refine ⟨rep, ?_, ?_⟩
  · intro p
    exact List.getLast_mem (hcover.1 p.1 p.2).2.1
  · intro x y hx hy hxy
    rcases hx with ⟨p, rfl⟩
    rcases hy with ⟨q, rfl⟩
    exact hind
      (terminal_mem_of_path p.2 (hcover.1 p.1 p.2).2.1)
      (terminal_mem_of_path q.2 (hcover.1 q.1 q.2).2.1)
      hxy

lemma directedIndependent_terminal_representatives_on {D : DirectedGraph V}
    {X : Finset V} {P : Finset (List V)} (hcover : IsDirectedPathCoverOn D X P)
    (hind : DirectedIndependentSet D (TerminalSet P)) :
    PathCoverHasIndependentRepresentatives D P := by
  classical
  let rep : {p : List V // p ∈ P} → V := fun p =>
    p.1.getLast (hcover.1 p.1 p.2).2.1
  refine ⟨rep, ?_, ?_⟩
  · intro p
    exact List.getLast_mem (hcover.1 p.1 p.2).2.1
  · intro x y hx hy hxy
    rcases hx with ⟨p, rfl⟩
    rcases hy with ⟨q, rfl⟩
    exact hind
      (terminal_mem_of_path p.2 (hcover.1 p.1 p.2).2.1)
      (terminal_mem_of_path q.2 (hcover.1 q.1 q.2).2.1)
      hxy

lemma hasIndependentPathCoverRepresentatives_of_cover {D : DirectedGraph V}
    {P : Finset (List V)} (hcover : IsDirectedPathCover D P)
    (hrep : PathCoverHasIndependentRepresentatives D P) :
    HasIndependentPathCoverRepresentatives D :=
  ⟨P, hcover, hrep⟩

lemma hasIndependentPathCoverRepresentatives_of_independent_terminal {D : DirectedGraph V}
    {P : Finset (List V)} (hcover : IsDirectedPathCover D P)
    (hind : DirectedIndependentSet D (TerminalSet P)) :
    HasIndependentPathCoverRepresentatives D :=
  hasIndependentPathCoverRepresentatives_of_cover hcover
    (directedIndependent_terminal_representatives hcover hind)

lemma singleton_path_cover (D : DirectedGraph V) [Fintype V] [DecidableEq V] :
    IsDirectedPathCover D ((Finset.univ : Finset V).image fun v => [v]) := by
  classical
  constructor
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨v, _hv, rfl⟩
    simp [IsDirectedPath, IsDirectedWalkList]
  constructor
  · intro p hp q hq hpq
    rcases Finset.mem_image.mp hp with ⟨v, _hv, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨w, _hw, rfl⟩
    have hvw : v ≠ w := by
      intro h
      exact hpq (by simp [h])
    refine Set.disjoint_left.mpr ?_
    intro x hx hy
    simp [listVertexSet] at hx hy
    subst x
    exact hvw hy
  · intro v
    refine ⟨[v], ?_, by simp⟩
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩

lemma exists_path_cover (D : DirectedGraph V) [Fintype V] [DecidableEq V] :
    ∃ P : Finset (List V), IsDirectedPathCover D P :=
  ⟨(Finset.univ : Finset V).image fun v => [v], singleton_path_cover D⟩

noncomputable def terminalCount (P : Finset (List V)) : ℕ :=
  (TerminalSet P).ncard

lemma exists_minimal_terminal_path_cover_on (D : DirectedGraph V) [DecidableEq V]
    (X : Finset V) :
    ∃ P : Finset (List V), IsDirectedPathCoverOn D X P ∧
      ∀ Q : Finset (List V), IsDirectedPathCoverOn D X Q →
        terminalCount P ≤ terminalCount Q := by
  classical
  let good : ℕ → Prop := fun n =>
    ∃ P : Finset (List V), IsDirectedPathCoverOn D X P ∧ terminalCount P = n
  letI : DecidablePred good := Classical.decPred good
  have hgood : ∃ n : ℕ, good n := by
    rcases exists_path_cover_on D X with ⟨P, hP⟩
    exact ⟨terminalCount P, P, hP, rfl⟩
  rcases Nat.find_spec hgood with ⟨P, hPcover, hPcount⟩
  refine ⟨P, hPcover, ?_⟩
  intro Q hQcover
  have hQgood : good (terminalCount Q) := ⟨Q, hQcover, rfl⟩
  simpa [hPcount] using Nat.find_min' hgood hQgood

lemma not_terminalSet_ssubset_of_minimal_on {D : DirectedGraph V} [DecidableEq V]
    {X : Finset V} {P Q : Finset (List V)}
    (hPcover : IsDirectedPathCoverOn D X P)
    (hmin : ∀ R : Finset (List V), IsDirectedPathCoverOn D X R →
      terminalCount P ≤ terminalCount R)
    (hQcover : IsDirectedPathCoverOn D X Q) :
    ¬ TerminalSet Q ⊂ TerminalSet P := by
  intro hproper
  have hfinite : (TerminalSet P).Finite := terminalSet_finite_of_pathCoverOn hPcover
  have hlt : terminalCount Q < terminalCount P := by
    simpa [terminalCount] using Set.ncard_lt_ncard hproper hfinite
  exact (not_lt_of_ge (hmin Q hQcover)) hlt

lemma exists_inclusion_minimal_terminal_path_cover_on (D : DirectedGraph V)
    [DecidableEq V] (X : Finset V) :
    ∃ P : Finset (List V), InclusionMinimalTerminalPathCoverOn D X P := by
  classical
  rcases exists_minimal_terminal_path_cover_on D X with ⟨P, hPcover, hmin⟩
  exact ⟨P, hPcover, fun Q hQ =>
    not_terminalSet_ssubset_of_minimal_on hPcover hmin hQ⟩

lemma exists_minimal_terminal_path_cover (D : DirectedGraph V) [Fintype V] [DecidableEq V] :
    ∃ P : Finset (List V), IsDirectedPathCover D P ∧
      ∀ Q : Finset (List V), IsDirectedPathCover D Q →
        terminalCount P ≤ terminalCount Q := by
  classical
  let good : ℕ → Prop := fun n =>
    ∃ P : Finset (List V), IsDirectedPathCover D P ∧ terminalCount P = n
  letI : DecidablePred good := Classical.decPred good
  have hgood : ∃ n : ℕ, good n := by
    rcases exists_path_cover D with ⟨P, hP⟩
    exact ⟨terminalCount P, P, hP, rfl⟩
  rcases Nat.find_spec hgood with ⟨P, hPcover, hPcount⟩
  refine ⟨P, hPcover, ?_⟩
  intro Q hQcover
  have hQgood : good (terminalCount Q) := ⟨Q, hQcover, rfl⟩
  simpa [hPcount] using Nat.find_min' hgood hQgood

lemma not_terminalSet_ssubset_of_minimal [Fintype V]
    {D : DirectedGraph V} {P Q : Finset (List V)}
    (hmin : ∀ R : Finset (List V), IsDirectedPathCover D R →
      terminalCount P ≤ terminalCount R)
    (hQcover : IsDirectedPathCover D Q) :
    ¬ TerminalSet Q ⊂ TerminalSet P := by
  intro hproper
  have hlt : terminalCount Q < terminalCount P := by
    simpa [terminalCount] using Set.ncard_lt_ncard hproper
  exact (not_lt_of_ge (hmin Q hQcover)) hlt

lemma exists_inclusion_minimal_terminal_path_cover (D : DirectedGraph V)
    [Fintype V] [DecidableEq V] :
    ∃ P : Finset (List V), InclusionMinimalTerminalPathCover D P := by
  classical
  rcases exists_minimal_terminal_path_cover D with ⟨P, hPcover, hmin⟩
  exact ⟨P, hPcover, fun Q hQ => not_terminalSet_ssubset_of_minimal hmin hQ⟩

/-- The directed graph obtained by deleting one vertex. -/
def deleteVertexDirected (D : DirectedGraph V) (v : V) : DirectedGraph {w : V // w ≠ v} :=
  fun x y => D x.1 y.1

/-- Lift a path in a deleted directed graph back to the original vertex type. -/
def liftDeletedList {v : V} (p : List {w : V // w ≠ v}) : List V :=
  p.map Subtype.val

lemma liftDeletedList_ne_nil {v : V} {p : List {w : V // w ≠ v}} (hp : p ≠ []) :
    liftDeletedList p ≠ [] := by
  cases p with
  | nil => exact False.elim (hp rfl)
  | cons x xs => simp [liftDeletedList]

lemma isDirectedWalkList_liftDeleted {D : DirectedGraph V} {v : V} :
    ∀ {p : List {w : V // w ≠ v}},
      IsDirectedWalkList (deleteVertexDirected D v) p →
        IsDirectedWalkList D (liftDeletedList p)
  | [], _ => by simp [liftDeletedList, IsDirectedWalkList]
  | [_], _ => by simp [liftDeletedList, IsDirectedWalkList]
  | x :: y :: zs, h => by
      exact ⟨h.1, isDirectedWalkList_liftDeleted h.2⟩

lemma isDirectedPath_liftDeleted {D : DirectedGraph V} {v : V}
    {p : List {w : V // w ≠ v}}
    (hp : IsDirectedPath (deleteVertexDirected D v) p) :
    IsDirectedPath D (liftDeletedList p) := by
  refine ⟨?_, liftDeletedList_ne_nil hp.2.1, ?_⟩
  · exact hp.1.map Subtype.val_injective
  · exact isDirectedWalkList_liftDeleted hp.2.2

lemma mem_liftDeletedList_iff {v x : V} {p : List {w : V // w ≠ v}} :
    x ∈ liftDeletedList p ↔ ∃ y : {w : V // w ≠ v}, y ∈ p ∧ y.1 = x := by
  simp [liftDeletedList]

lemma deleted_vertex_not_mem_liftDeletedList {v : V} {p : List {w : V // w ≠ v}} :
    v ∉ liftDeletedList p := by
  intro hv
  rcases (mem_liftDeletedList_iff.mp hv) with ⟨y, _hy, hyv⟩
  exact y.2 hyv

/-- Lift a path cover of `D - v` and add `v` back as a singleton path. -/
def liftDeletedCoverWithSingleton [DecidableEq V] {v : V}
    (P : Finset (List {w : V // w ≠ v})) : Finset (List V) :=
  insert [v] (P.image liftDeletedList)

lemma liftDeletedCoverWithSingleton_isPathCover {D : DirectedGraph V}
    [DecidableEq V] {v : V} {P : Finset (List {w : V // w ≠ v})}
    (hP : IsDirectedPathCover (deleteVertexDirected D v) P) :
    IsDirectedPathCover D (liftDeletedCoverWithSingleton P) := by
  classical
  constructor
  · intro p hp
    rw [liftDeletedCoverWithSingleton, Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · simp [IsDirectedPath, IsDirectedWalkList]
    · rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      exact isDirectedPath_liftDeleted (hP.1 q hq)
  constructor
  · intro p hp q hq hpq
    rw [liftDeletedCoverWithSingleton, Finset.mem_insert] at hp hq
    rcases hp with rfl | hp
    · rcases hq with rfl | hq
      · exact False.elim (hpq rfl)
      · rcases Finset.mem_image.mp hq with ⟨q0, hq0, rfl⟩
        refine Set.disjoint_left.mpr ?_
        intro x hx hxq
        simp [listVertexSet] at hx
        subst x
        exact deleted_vertex_not_mem_liftDeletedList hxq
    · rcases Finset.mem_image.mp hp with ⟨p0, hp0, rfl⟩
      rcases hq with rfl | hq
      · refine Set.disjoint_left.mpr ?_
        intro x hxp hx
        simp [listVertexSet] at hx
        subst x
        exact deleted_vertex_not_mem_liftDeletedList hxp
      · rcases Finset.mem_image.mp hq with ⟨q0, hq0, rfl⟩
        have hpq0 : p0 ≠ q0 := by
          intro h
          exact hpq (by simp [h])
        have hdisj := hP.2.1 p0 hp0 q0 hq0 hpq0
        refine Set.disjoint_left.mpr ?_
        intro x hxp hxq
        rcases (mem_liftDeletedList_iff.mp hxp) with ⟨xp, hxp0, hxpval⟩
        rcases (mem_liftDeletedList_iff.mp hxq) with ⟨xq, hxq0, hxqval⟩
        have hsub : xp = xq := Subtype.ext (hxpval.trans hxqval.symm)
        exact (Set.disjoint_left.mp hdisj hxp0) (by simpa [listVertexSet, hsub] using hxq0)
  · intro x
    by_cases hxv : x = v
    · refine ⟨[v], ?_, by simp [hxv]⟩
      simp [liftDeletedCoverWithSingleton]
    · obtain ⟨p, hp, hxp⟩ := hP.2.2 ⟨x, hxv⟩
      refine ⟨liftDeletedList p, ?_, ?_⟩
      · rw [liftDeletedCoverWithSingleton, Finset.mem_insert]
        exact Or.inr (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      · exact (mem_liftDeletedList_iff.mpr ⟨⟨x, hxv⟩, hxp, rfl⟩)

lemma isDirectedWalkList_dropLast {D : DirectedGraph V} :
    ∀ {p : List V}, IsDirectedWalkList D p → IsDirectedWalkList D p.dropLast
  | [], _ => by simp [IsDirectedWalkList]
  | [_], _ => by simp [IsDirectedWalkList]
  | x :: y :: zs, h => by
      cases zs with
      | nil => simp [IsDirectedWalkList]
      | cons z zs =>
          exact ⟨h.1, isDirectedWalkList_dropLast h.2⟩

lemma isDirectedPath_dropLast {D : DirectedGraph V} {p : List V}
    (hp : IsDirectedPath D p) (hne : p.dropLast ≠ []) :
    IsDirectedPath D p.dropLast := by
  refine ⟨(List.dropLast_sublist p).nodup hp.1, hne, ?_⟩
  exact isDirectedWalkList_dropLast hp.2.2

lemma last_edge_of_isDirectedWalkList_append_singleton {D : DirectedGraph V} :
    ∀ {p : List V} (hpne : p ≠ []) {t : V},
      IsDirectedWalkList D (p ++ [t]) → D (p.getLast hpne) t
  | [], hpne, _, _ => False.elim (hpne rfl)
  | [x], _, t, hwalk => by
      simpa [IsDirectedWalkList] using hwalk
  | x :: y :: zs, _, t, hwalk => by
      exact last_edge_of_isDirectedWalkList_append_singleton (p := y :: zs)
        (by simp) hwalk.2

lemma last_edge_dropLast_to_getLast {D : DirectedGraph V} {p : List V}
    (hp : IsDirectedPath D p) (hdrop : p.dropLast ≠ []) :
    D (p.dropLast.getLast hdrop) (p.getLast hp.2.1) := by
  have hwalk : IsDirectedWalkList D (p.dropLast ++ [p.getLast hp.2.1]) := by
    simpa [List.dropLast_append_getLast hp.2.1] using hp.2.2
  exact last_edge_of_isDirectedWalkList_append_singleton hdrop hwalk

/-- Replace one list path in a finite path family. -/
def replacePath [DecidableEq V] (P : Finset (List V)) (old new : List V) :
    Finset (List V) :=
  insert new (P.erase old)

lemma terminalSet_erase_subset [DecidableEq V] {P : Finset (List V)} {p : List V} :
    TerminalSet (P.erase p) ⊆ TerminalSet P := by
  intro x hx
  rcases hx with ⟨q, hq, hxlast⟩
  rw [Finset.mem_erase] at hq
  exact ⟨q, hq.2, hxlast⟩

lemma not_mem_terminalSet_erase_of_path_ends_pathCoverOn [DecidableEq V]
    {D : DirectedGraph V} {X : Finset V} {P : Finset (List V)}
    (hcover : IsDirectedPathCoverOn D X P) {p : List V} (hp : p ∈ P)
    {z : V} (hz : z ∈ p.getLast?) :
    z ∉ TerminalSet (P.erase p) := by
  intro hzterm
  rcases hzterm with ⟨q, hq, hzq⟩
  rw [Finset.mem_erase] at hq
  exact hq.1 (path_eq_of_common_terminal_pathCoverOn hcover hp hq.2 hz hzq).symm

/-- Drop the terminal vertex of one path in a finite path family. -/
def dropTerminalCover [DecidableEq V] (P : Finset (List V)) (p : List V) :
    Finset (List V) :=
  replacePath P p p.dropLast

lemma getLast_not_mem_dropLast_of_nodup {p : List V} (hp : p.Nodup) (hne : p ≠ []) :
    p.getLast hne ∉ p.dropLast := by
  intro hmem
  have hnodup : (p.dropLast ++ [p.getLast hne]).Nodup := by
    simpa [List.dropLast_append_getLast hne] using hp
  have hsep := (List.nodup_append.mp hnodup).2.2
  exact hsep (p.getLast hne) hmem (p.getLast hne) (by simp) rfl

lemma dropTerminalCover_isPathCoverOn [DecidableEq V] {D : DirectedGraph V}
    {X : Finset V} {P : Finset (List V)} {p : List V} {t : V}
    (hcover : IsDirectedPathCoverOn D X P) (hpP : p ∈ P)
    (hpne : p ≠ []) (ht : p.getLast hpne = t) (hdrop : p.dropLast ≠ []) :
    IsDirectedPathCoverOn D (X.erase t) (dropTerminalCover P p) := by
  classical
  have hppath : IsDirectedPath D p := hcover.1 p hpP
  have htmem : t ∈ p := by
    simpa [← ht] using List.getLast_mem hpne
  constructor
  · intro r hr
    rw [dropTerminalCover, replacePath, Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · exact isDirectedPath_dropLast hppath hdrop
    · rw [Finset.mem_erase] at hr
      exact hcover.1 r hr.2
  constructor
  · intro r hr s hs hrs
    rw [dropTerminalCover, replacePath, Finset.mem_insert] at hr hs
    rcases hr with rfl | hr
    · rcases hs with rfl | hs
      · exact False.elim (hrs rfl)
      · rw [Finset.mem_erase] at hs
        have hdisj := hcover.2.1 p hpP s hs.2 (by
          intro h
          exact hs.1 h.symm)
        refine Set.disjoint_left.mpr ?_
        intro x hx hy
        exact Set.disjoint_left.mp hdisj ((List.dropLast_sublist p).subset hx) hy
    · rw [Finset.mem_erase] at hr
      rcases hs with rfl | hs
      · have hdisj := hcover.2.1 r hr.2 p hpP hr.1
        refine Set.disjoint_left.mpr ?_
        intro x hx hy
        exact Set.disjoint_left.mp hdisj hx ((List.dropLast_sublist p).subset hy)
      · rw [Finset.mem_erase] at hs
        exact hcover.2.1 r hr.2 s hs.2 hrs
  constructor
  · intro r hr x hx
    rw [dropTerminalCover, replacePath, Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · have hxX : x ∈ X := hcover.2.2.1 p hpP x ((List.dropLast_sublist p).subset hx)
      have hxne : x ≠ t := by
        intro hxt
        have hlastdrop : p.getLast hpne ∈ p.dropLast := by simpa [ht, hxt] using hx
        exact getLast_not_mem_dropLast_of_nodup hppath.1 hpne hlastdrop
      exact Finset.mem_erase.mpr ⟨hxne, hxX⟩
    · rw [Finset.mem_erase] at hr
      have hxX : x ∈ X := hcover.2.2.1 r hr.2 x hx
      have hxne : x ≠ t := by
        intro hxt
        subst x
        have hdisj := hcover.2.1 p hpP r hr.2 (by
          intro h
          exact hr.1 h.symm)
        exact Set.disjoint_left.mp hdisj htmem hx
      exact Finset.mem_erase.mpr ⟨hxne, hxX⟩
  · intro x hx
    rw [Finset.mem_erase] at hx
    rcases hcover.2.2.2 x hx.2 with ⟨q, hqP, hxq⟩
    by_cases hqp : q = p
    · subst q
      refine ⟨p.dropLast, ?_, ?_⟩
      · simp [dropTerminalCover, replacePath]
      · exact List.mem_dropLast_of_mem_of_ne_getLast hxq (by
          intro hlast
          exact hx.1 (hlast.trans ht))
    · refine ⟨q, ?_, hxq⟩
      rw [dropTerminalCover, replacePath, Finset.mem_insert]
      exact Or.inr (Finset.mem_erase.mpr ⟨hqp, hqP⟩)

lemma representatives_of_dropTerminalCover [DecidableEq V] {D : DirectedGraph V}
    {P : Finset (List V)} {p : List V} (hpP : p ∈ P)
    (hrep : PathCoverHasIndependentRepresentatives D (dropTerminalCover P p)) :
    PathCoverHasIndependentRepresentatives D P := by
  classical
  rcases hrep with ⟨rep, hrep_mem, hind⟩
  let toDrop : {r : List V // r ∈ P} →
      {q : List V // q ∈ dropTerminalCover P p} := fun r =>
    if h : r.1 = p then
      ⟨p.dropLast, by simp [dropTerminalCover, replacePath]⟩
    else
      ⟨r.1, by
        rw [dropTerminalCover, replacePath, Finset.mem_insert]
        exact Or.inr (Finset.mem_erase.mpr ⟨h, r.2⟩)⟩
  refine ⟨fun r => rep (toDrop r), ?_, ?_⟩
  · intro r
    dsimp [toDrop]
    split_ifs with hrp
    · have hmem_p : rep ⟨p.dropLast, by
          simp [dropTerminalCover, replacePath]⟩ ∈ p :=
        (List.dropLast_sublist p).subset (hrep_mem ⟨p.dropLast, by
          simp [dropTerminalCover, replacePath]⟩)
      simpa [hrp] using hmem_p
    · exact hrep_mem ⟨r.1, by
        rw [dropTerminalCover, replacePath, Finset.mem_insert]
        exact Or.inr (Finset.mem_erase.mpr ⟨hrp, r.2⟩)⟩
  · refine directedIndependentSet_mono hind ?_
    intro x hx
    rcases hx with ⟨r, rfl⟩
    exact ⟨toDrop r, rfl⟩

lemma eraseSingletonTerminalCover_isPathCoverOn [DecidableEq V] {D : DirectedGraph V}
    {X : Finset V} {P : Finset (List V)} {p : List V} {t : V}
    (hcover : IsDirectedPathCoverOn D X P) (hpP : p ∈ P) (hp : p = [t]) :
    IsDirectedPathCoverOn D (X.erase t) (P.erase p) := by
  classical
  have htmem : t ∈ p := by simp [hp]
  constructor
  · intro r hr
    rw [Finset.mem_erase] at hr
    exact hcover.1 r hr.2
  constructor
  · intro r hr s hs hrs
    rw [Finset.mem_erase] at hr hs
    exact hcover.2.1 r hr.2 s hs.2 hrs
  constructor
  · intro r hr x hx
    rw [Finset.mem_erase] at hr
    have hxX : x ∈ X := hcover.2.2.1 r hr.2 x hx
    have hxne : x ≠ t := by
      intro hxt
      subst x
      have hdisj := hcover.2.1 p hpP r hr.2 (by
        intro h
        exact hr.1 h.symm)
      exact Set.disjoint_left.mp hdisj htmem hx
    exact Finset.mem_erase.mpr ⟨hxne, hxX⟩
  · intro x hx
    rw [Finset.mem_erase] at hx
    rcases hcover.2.2.2 x hx.2 with ⟨q, hqP, hxq⟩
    by_cases hqp : q = p
    · subst q
      simp [hp] at hxq
      exact False.elim (hx.1 hxq)
    · exact ⟨q, Finset.mem_erase.mpr ⟨hqp, hqP⟩, hxq⟩

/-- Add a deleted vertex back as a singleton path. -/
def insertSingletonCover [DecidableEq V] (P : Finset (List V)) (t : V) :
    Finset (List V) :=
  insert [t] P

lemma terminalSet_insertSingletonCover_subset_insert [DecidableEq V]
    {P : Finset (List V)} {t : V} :
    TerminalSet (insertSingletonCover P t) ⊆ Set.insert t (TerminalSet P) := by
  intro x hx
  rcases hx with ⟨q, hq, hxlast⟩
  rw [insertSingletonCover, Finset.mem_insert] at hq
  change x = t ∨ x ∈ TerminalSet P
  rcases hq with rfl | hq
  · left
    simpa [eq_comm] using hxlast
  · right
    exact ⟨q, hq, hxlast⟩

lemma subset_of_subset_insert_of_not_mem {A B : Set V} {a : V}
    (hsub : A ⊆ Set.insert a B) (ha : a ∉ A) :
    A ⊆ B := by
  intro x hx
  have hxins := hsub hx
  change x = a ∨ x ∈ B at hxins
  rcases hxins with rfl | hxB
  · exact False.elim (ha hx)
  · exact hxB

lemma terminalSet_insertSingletonCover_subset_of_subset [DecidableEq V]
    {P Q : Finset (List V)} {t : V}
    (hQ : TerminalSet Q ⊆ TerminalSet P) (ht : t ∈ TerminalSet P) :
    TerminalSet (insertSingletonCover Q t) ⊆ TerminalSet P := by
  intro x hx
  have hxins := terminalSet_insertSingletonCover_subset_insert (P := Q) (t := t) hx
  change x = t ∨ x ∈ TerminalSet Q at hxins
  rcases hxins with rfl | hxQ
  · exact ht
  · exact hQ hxQ

lemma terminalSet_insertSingletonCover_ssubset_of_subset [DecidableEq V]
    {P Q : Finset (List V)} {t z : V}
    (hQ : TerminalSet Q ⊆ TerminalSet P) (ht : t ∈ TerminalSet P)
    (hzP : z ∈ TerminalSet P) (hzt : z ≠ t) (hzQ : z ∉ TerminalSet Q) :
    TerminalSet (insertSingletonCover Q t) ⊂ TerminalSet P := by
  refine ⟨terminalSet_insertSingletonCover_subset_of_subset hQ ht, ?_⟩
  intro hback
  have hznew : z ∈ TerminalSet (insertSingletonCover Q t) := hback hzP
  have hzins := terminalSet_insertSingletonCover_subset_insert (P := Q) (t := t) hznew
  change z = t ∨ z ∈ TerminalSet Q at hzins
  rcases hzins with hzt' | hzQ'
  · exact hzt hzt'
  · exact hzQ hzQ'

lemma insertSingletonCover_isPathCoverOn [DecidableEq V] {D : DirectedGraph V}
    {X : Finset V} {P : Finset (List V)} {t : V}
    (hcover : IsDirectedPathCoverOn D (X.erase t) P) (htX : t ∈ X) :
    IsDirectedPathCoverOn D X (insertSingletonCover P t) := by
  classical
  constructor
  · intro p hp
    rw [insertSingletonCover, Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · simp [IsDirectedPath, IsDirectedWalkList]
    · exact hcover.1 p hp
  constructor
  · intro p hp q hq hpq
    rw [insertSingletonCover, Finset.mem_insert] at hp hq
    rcases hp with rfl | hp
    · rcases hq with rfl | hq
      · exact False.elim (hpq rfl)
      · refine Set.disjoint_left.mpr ?_
        intro x hx hxq
        simp [listVertexSet] at hx
        subst x
        have htq := hcover.2.2.1 q hq t hxq
        exact (Finset.mem_erase.mp htq).1 rfl
    · rcases hq with rfl | hq
      · refine Set.disjoint_left.mpr ?_
        intro x hxp hx
        simp [listVertexSet] at hx
        subst x
        have htp := hcover.2.2.1 p hp t hxp
        exact (Finset.mem_erase.mp htp).1 rfl
      · exact hcover.2.1 p hp q hq hpq
  constructor
  · intro p hp x hx
    rw [insertSingletonCover, Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · simp at hx
      subst x
      exact htX
    · exact (Finset.mem_erase.mp (hcover.2.2.1 p hp x hx)).2
  · intro x hx
    by_cases hxt : x = t
    · subst x
      exact ⟨[t], by simp [insertSingletonCover], by simp⟩
    · have hxerase : x ∈ X.erase t := Finset.mem_erase.mpr ⟨hxt, hx⟩
      rcases hcover.2.2.2 x hxerase with ⟨p, hp, hxp⟩
      exact ⟨p, by simp [insertSingletonCover, hp], hxp⟩

lemma isDirectedWalkList_append_singleton {D : DirectedGraph V} {t : V} :
    ∀ {p : List V} (hpne : p ≠ []), IsDirectedWalkList D p →
      D (p.getLast hpne) t → IsDirectedWalkList D (p ++ [t])
  | [], hpne, _, _ => False.elim (hpne rfl)
  | [x], _, _, hlast => by
      simpa [IsDirectedWalkList] using hlast
  | x :: y :: zs, _, hwalk, hlast => by
      exact ⟨hwalk.1, isDirectedWalkList_append_singleton (p := y :: zs)
        (by simp) hwalk.2 (by simpa using hlast)⟩

lemma isDirectedPath_append_singleton {D : DirectedGraph V} {p : List V} {t : V}
    (hp : IsDirectedPath D p) (htp : t ∉ p)
    (hedge : D (p.getLast hp.2.1) t) :
    IsDirectedPath D (p ++ [t]) := by
  refine ⟨?_, by simp, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hp.1, by simp, ?_⟩
    intro a ha b hb
    simp at hb
    subst b
    intro hat
    exact htp (hat ▸ ha)
  · exact isDirectedWalkList_append_singleton hp.2.1 hp.2.2 hedge

/-- Extend one path in a finite path family by one terminal vertex. -/
def extendTerminalCover [DecidableEq V] (P : Finset (List V)) (p : List V) (t : V) :
    Finset (List V) :=
  replacePath P p (p ++ [t])

lemma terminalSet_extendTerminalCover_subset_insert_erase [DecidableEq V]
    {P : Finset (List V)} {p : List V} {t : V} :
    TerminalSet (extendTerminalCover P p t) ⊆
      Set.insert t (TerminalSet (P.erase p)) := by
  intro x hx
  rcases hx with ⟨q, hq, hxlast⟩
  rw [extendTerminalCover, replacePath, Finset.mem_insert] at hq
  change x = t ∨ x ∈ TerminalSet (P.erase p)
  rcases hq with rfl | hq
  · left
    simpa [eq_comm] using hxlast
  · right
    exact ⟨q, hq, hxlast⟩

lemma terminalSet_extendTerminalCover_subset_insert [DecidableEq V]
    {P : Finset (List V)} {p : List V} {t : V} :
    TerminalSet (extendTerminalCover P p t) ⊆ Set.insert t (TerminalSet P) := by
  intro x hx
  rcases hx with ⟨q, hq, hxlast⟩
  rw [extendTerminalCover, replacePath, Finset.mem_insert] at hq
  change x = t ∨ x ∈ TerminalSet P
  rcases hq with rfl | hq
  · left
    simpa [eq_comm] using hxlast
  · right
    rw [Finset.mem_erase] at hq
    exact ⟨q, hq.2, hxlast⟩

lemma terminalSet_extendTerminalCover_ssubset_of_erase_subset [DecidableEq V]
    {P Q : Finset (List V)} {q : List V} {t z : V}
    (hQerase : TerminalSet (Q.erase q) ⊆ TerminalSet P)
    (htP : t ∈ TerminalSet P) (hzP : z ∈ TerminalSet P)
    (hzt : z ≠ t) (hzErase : z ∉ TerminalSet (Q.erase q)) :
    TerminalSet (extendTerminalCover Q q t) ⊂ TerminalSet P := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxins := terminalSet_extendTerminalCover_subset_insert_erase (P := Q) (p := q) (t := t) hx
    change x = t ∨ x ∈ TerminalSet (Q.erase q) at hxins
    rcases hxins with rfl | hxQ
    · exact htP
    · exact hQerase hxQ
  · intro hback
    have hznew : z ∈ TerminalSet (extendTerminalCover Q q t) := hback hzP
    have hzins := terminalSet_extendTerminalCover_subset_insert_erase (P := Q) (p := q) (t := t) hznew
    change z = t ∨ z ∈ TerminalSet (Q.erase q) at hzins
    rcases hzins with hzt' | hzQ
    · exact hzt hzt'
    · exact hzErase hzQ

lemma terminalSet_dropTerminalCover_subset_insert [DecidableEq V]
    {P : Finset (List V)} {p : List V} (hdrop : p.dropLast ≠ []) :
    TerminalSet (dropTerminalCover P p) ⊆
      Set.insert (p.dropLast.getLast hdrop) (TerminalSet P) := by
  intro x hx
  rcases hx with ⟨q, hq, hxlast⟩
  rw [dropTerminalCover, replacePath, Finset.mem_insert] at hq
  change x = p.dropLast.getLast hdrop ∨ x ∈ TerminalSet P
  rcases hq with rfl | hq
  · left
    rw [List.getLast?_eq_getLast_of_ne_nil hdrop] at hxlast
    simpa [eq_comm] using hxlast
  · right
    rw [Finset.mem_erase] at hq
    exact ⟨q, hq.2, hxlast⟩

lemma terminalSet_subset_original_of_subset_dropTerminal [DecidableEq V]
    {P Q : Finset (List V)} {p : List V} (hdrop : p.dropLast ≠ [])
    (hQ : TerminalSet Q ⊆ TerminalSet (dropTerminalCover P p))
    (hpred : p.dropLast.getLast hdrop ∉ TerminalSet Q) :
    TerminalSet Q ⊆ TerminalSet P :=
  subset_of_subset_insert_of_not_mem
    (fun _ hx => terminalSet_dropTerminalCover_subset_insert (P := P) (p := p) hdrop (hQ hx))
    hpred

lemma terminalSet_erase_subset_original_of_subset_dropTerminal [DecidableEq V]
    {P Q : Finset (List V)} {p q : List V} (hdrop : p.dropLast ≠ [])
    (hQ : TerminalSet Q ⊆ TerminalSet (dropTerminalCover P p))
    (hpred : p.dropLast.getLast hdrop ∉ TerminalSet (Q.erase q)) :
    TerminalSet (Q.erase q) ⊆ TerminalSet P :=
  subset_of_subset_insert_of_not_mem
    (fun _ hx => terminalSet_dropTerminalCover_subset_insert (P := P) (p := p) hdrop
      (hQ (terminalSet_erase_subset hx)))
    hpred

lemma terminalSet_insertSingletonCover_ssubset_of_subset_dropTerminal [DecidableEq V]
    {P Q : Finset (List V)} {p : List V} {t z : V} (hdrop : p.dropLast ≠ [])
    (hQ : TerminalSet Q ⊆ TerminalSet (dropTerminalCover P p))
    (hpred : p.dropLast.getLast hdrop ∉ TerminalSet Q)
    (htP : t ∈ TerminalSet P) (hzP : z ∈ TerminalSet P)
    (hzt : z ≠ t) (hzQ : z ∉ TerminalSet Q) :
    TerminalSet (insertSingletonCover Q t) ⊂ TerminalSet P :=
  terminalSet_insertSingletonCover_ssubset_of_subset
    (terminalSet_subset_original_of_subset_dropTerminal hdrop hQ hpred)
    htP hzP hzt hzQ

lemma terminalSet_extendTerminalCover_ssubset_of_subset_dropTerminal [DecidableEq V]
    {P Q : Finset (List V)} {p q : List V} {t z : V} (hdrop : p.dropLast ≠ [])
    (hQ : TerminalSet Q ⊆ TerminalSet (dropTerminalCover P p))
    (hpred : p.dropLast.getLast hdrop ∉ TerminalSet (Q.erase q))
    (htP : t ∈ TerminalSet P) (hzP : z ∈ TerminalSet P)
    (hzt : z ≠ t) (hzErase : z ∉ TerminalSet (Q.erase q)) :
    TerminalSet (extendTerminalCover Q q t) ⊂ TerminalSet P :=
  terminalSet_extendTerminalCover_ssubset_of_erase_subset
    (terminalSet_erase_subset_original_of_subset_dropTerminal hdrop hQ hpred)
    htP hzP hzt hzErase

lemma extendTerminalCover_isPathCoverOn [DecidableEq V] {D : DirectedGraph V}
    {X : Finset V} {P : Finset (List V)} {p : List V} {t : V}
    (hcover : IsDirectedPathCoverOn D (X.erase t) P) (hpP : p ∈ P)
    (hedge : D (p.getLast (hcover.1 p hpP).2.1) t) (htX : t ∈ X) :
    IsDirectedPathCoverOn D X (extendTerminalCover P p t) := by
  classical
  have hp : IsDirectedPath D p := hcover.1 p hpP
  have ht_not_mem_p : t ∉ p := by
    intro htp
    have htin := hcover.2.2.1 p hpP t htp
    exact (Finset.mem_erase.mp htin).1 rfl
  constructor
  · intro r hr
    rw [extendTerminalCover, replacePath, Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · exact isDirectedPath_append_singleton hp ht_not_mem_p hedge
    · rw [Finset.mem_erase] at hr
      exact hcover.1 r hr.2
  constructor
  · intro r hr s hs hrs
    rw [extendTerminalCover, replacePath, Finset.mem_insert] at hr hs
    rcases hr with rfl | hr
    · rcases hs with rfl | hs
      · exact False.elim (hrs rfl)
      · rw [Finset.mem_erase] at hs
        have hdisj := hcover.2.1 p hpP s hs.2 (by
          intro h
          exact hs.1 h.symm)
        refine Set.disjoint_left.mpr ?_
        intro x hx hy
        change x ∈ p ++ [t] at hx
        change x ∈ s at hy
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact Set.disjoint_left.mp hdisj hx hy
        · simp at hx
          subst x
          have htin := hcover.2.2.1 s hs.2 t hy
          exact (Finset.mem_erase.mp htin).1 rfl
    · rw [Finset.mem_erase] at hr
      rcases hs with rfl | hs
      · have hdisj := hcover.2.1 r hr.2 p hpP hr.1
        refine Set.disjoint_left.mpr ?_
        intro x hx hy
        change x ∈ r at hx
        change x ∈ p ++ [t] at hy
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · exact Set.disjoint_left.mp hdisj hx hy
        · simp at hy
          subst x
          have htin := hcover.2.2.1 r hr.2 t hx
          exact (Finset.mem_erase.mp htin).1 rfl
      · rw [Finset.mem_erase] at hs
        exact hcover.2.1 r hr.2 s hs.2 hrs
  constructor
  · intro r hr x hx
    rw [extendTerminalCover, replacePath, Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · change x ∈ p ++ [t] at hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact (Finset.mem_erase.mp (hcover.2.2.1 p hpP x hx)).2
      · simp at hx
        subst x
        exact htX
    · rw [Finset.mem_erase] at hr
      exact (Finset.mem_erase.mp (hcover.2.2.1 r hr.2 x hx)).2
  · intro x hx
    by_cases hxt : x = t
    · subst x
      refine ⟨p ++ [t], ?_, by simp⟩
      simp [extendTerminalCover, replacePath]
    · have hxerase : x ∈ X.erase t := Finset.mem_erase.mpr ⟨hxt, hx⟩
      rcases hcover.2.2.2 x hxerase with ⟨q, hqP, hxq⟩
      by_cases hqp : q = p
      · subst q
        refine ⟨p ++ [t], ?_, ?_⟩
        · simp [extendTerminalCover, replacePath]
        · exact List.mem_append_left [t] hxq
      · refine ⟨q, ?_, hxq⟩
        rw [extendTerminalCover, replacePath, Finset.mem_insert]
        exact Or.inr (Finset.mem_erase.mpr ⟨hqp, hqP⟩)

lemma dropTerminalCover_inclusionMinimal_of_terminal_arc [DecidableEq V]
    {D : DirectedGraph V} {X : Finset V} {P : Finset (List V)}
    {p : List V} {t s : V}
    (hmin : InclusionMinimalTerminalPathCoverOn D X P) (hpP : p ∈ P)
    (hpne : p ≠ []) (htlast : p.getLast hpne = t) (hdrop : p.dropLast ≠ [])
    (hsP : s ∈ TerminalSet P) (hst : s ≠ t)
    (hpredEdge : D (p.dropLast.getLast hdrop) t) (hsEdge : D s t) :
    InclusionMinimalTerminalPathCoverOn D (X.erase t) (dropTerminalCover P p) := by
  classical
  let pred := p.dropLast.getLast hdrop
  have hcoverP : IsDirectedPathCoverOn D X P := hmin.1
  have htP : t ∈ TerminalSet P := by
    simpa [htlast] using terminal_mem_of_path hpP hpne
  have htX : t ∈ X := by
    exact hcoverP.2.2.1 p hpP t (by simpa [← htlast] using List.getLast_mem hpne)
  have hdropCover :
      IsDirectedPathCoverOn D (X.erase t) (dropTerminalCover P p) :=
    dropTerminalCover_isPathCoverOn hcoverP hpP hpne htlast hdrop
  refine ⟨hdropCover, ?_⟩
  intro Q hQcover hproper
  have hQsub : TerminalSet Q ⊆ TerminalSet (dropTerminalCover P p) := hproper.1
  by_cases hpredQ : pred ∈ TerminalSet Q
  · rcases hpredQ with ⟨q, hqQ, hqpred⟩
    have hpredQterm : pred ∈ TerminalSet Q := ⟨q, hqQ, hqpred⟩
    have hqedge : D (q.getLast (hQcover.1 q hqQ).2.1) t := by
      rcases List.mem_getLast?_eq_getLast hqpred with ⟨hqne, hpred_eq⟩
      simpa [pred, hpred_eq] using hpredEdge
    have hRcover : IsDirectedPathCoverOn D X (extendTerminalCover Q q t) :=
      extendTerminalCover_isPathCoverOn hQcover hqQ hqedge htX
    have hpredErase : pred ∉ TerminalSet (Q.erase q) :=
      not_mem_terminalSet_erase_of_path_ends_pathCoverOn hQcover hqQ hqpred
    have hnotback : ¬ TerminalSet (dropTerminalCover P p) ⊆ TerminalSet Q := hproper.2
    rcases Set.not_subset.mp hnotback with ⟨z, hzDrop, hzQ⟩
    have hz_ne_pred : z ≠ pred := by
      intro hz
      exact hzQ (by simpa [hz] using hpredQterm)
    have hzP : z ∈ TerminalSet P := by
      have hzins := terminalSet_dropTerminalCover_subset_insert (P := P) (p := p) hdrop hzDrop
      change z = pred ∨ z ∈ TerminalSet P at hzins
      rcases hzins with hzpred | hzP
      · exact False.elim (hz_ne_pred hzpred)
      · exact hzP
    have hzt : z ≠ t := by
      have hzXerase := terminalSet_subset_of_pathCoverOn hdropCover hzDrop
      exact (Finset.mem_erase.mp hzXerase).1
    have hzErase : z ∉ TerminalSet (Q.erase q) := by
      intro hzE
      exact hzQ (terminalSet_erase_subset hzE)
    have hstrict :
        TerminalSet (extendTerminalCover Q q t) ⊂ TerminalSet P :=
      terminalSet_extendTerminalCover_ssubset_of_subset_dropTerminal
        (P := P) (Q := Q) (p := p) (q := q) (t := t) (z := z)
        hdrop hQsub hpredErase htP hzP hzt hzErase
    exact (hmin.2 (extendTerminalCover Q q t) hRcover) hstrict
  · by_cases hsQ : s ∈ TerminalSet Q
    · rcases hsQ with ⟨q, hqQ, hqs⟩
      have hqedge : D (q.getLast (hQcover.1 q hqQ).2.1) t := by
        rcases List.mem_getLast?_eq_getLast hqs with ⟨hqne, hs_eq⟩
        simpa [hs_eq] using hsEdge
      have hRcover : IsDirectedPathCoverOn D X (extendTerminalCover Q q t) :=
        extendTerminalCover_isPathCoverOn hQcover hqQ hqedge htX
      have hpredErase : pred ∉ TerminalSet (Q.erase q) := by
        intro hpredErase
        exact hpredQ (terminalSet_erase_subset hpredErase)
      have hsErase : s ∉ TerminalSet (Q.erase q) :=
        not_mem_terminalSet_erase_of_path_ends_pathCoverOn hQcover hqQ hqs
      have hstrict :
          TerminalSet (extendTerminalCover Q q t) ⊂ TerminalSet P :=
        terminalSet_extendTerminalCover_ssubset_of_subset_dropTerminal
          (P := P) (Q := Q) (p := p) (q := q) (t := t) (z := s)
          hdrop hQsub hpredErase htP hsP hst hsErase
      exact (hmin.2 (extendTerminalCover Q q t) hRcover) hstrict
    · have hRcover : IsDirectedPathCoverOn D X (insertSingletonCover Q t) :=
        insertSingletonCover_isPathCoverOn hQcover htX
      have hstrict :
          TerminalSet (insertSingletonCover Q t) ⊂ TerminalSet P :=
        terminalSet_insertSingletonCover_ssubset_of_subset_dropTerminal
          (P := P) (Q := Q) (p := p) (t := t) (z := s)
          hdrop hQsub hpredQ htP hsP hst hsQ
      exact (hmin.2 (insertSingletonCover Q t) hRcover) hstrict

lemma dropLast_ne_nil_of_ne_singleton_getLast {p : List V} {t : V}
    (hpne : p ≠ []) (htlast : p.getLast hpne = t) (hnot : p ≠ [t]) :
    p.dropLast ≠ [] := by
  cases p with
  | nil => exact False.elim (hpne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          exact False.elim (hnot (by simpa using htlast))
      | cons y ys =>
          simp

lemma terminal_path_not_singleton_of_terminal_arc [DecidableEq V]
    {D : DirectedGraph V} {X : Finset V} {P : Finset (List V)}
    {p : List V} {t s : V}
    (hmin : InclusionMinimalTerminalPathCoverOn D X P) (hpP : p ∈ P)
    (hpne : p ≠ []) (htlast : p.getLast hpne = t)
    (hsP : s ∈ TerminalSet P) (hst : s ≠ t) (hsEdge : D s t) :
    p ≠ [t] := by
  classical
  intro hp_single
  have hcoverP : IsDirectedPathCoverOn D X P := hmin.1
  have htP : t ∈ TerminalSet P := by
    simpa [htlast] using terminal_mem_of_path hpP hpne
  have htX : t ∈ X := by
    exact hcoverP.2.2.1 p hpP t (by simpa [← htlast] using List.getLast_mem hpne)
  have heraseCover : IsDirectedPathCoverOn D (X.erase t) (P.erase p) :=
    eraseSingletonTerminalCover_isPathCoverOn hcoverP hpP hp_single
  rcases hsP with ⟨q, hqP, hqs⟩
  have hqp : q ≠ p := by
    intro h
    subst q
    rcases List.mem_getLast?_eq_getLast hqs with ⟨hpne', hs_eq⟩
    have hst' : s = t := by
      simpa [hp_single] using hs_eq
    exact hst hst'
  have hqErase : q ∈ P.erase p := Finset.mem_erase.mpr ⟨hqp, hqP⟩
  have hqedge : D (q.getLast (heraseCover.1 q hqErase).2.1) t := by
    rcases List.mem_getLast?_eq_getLast hqs with ⟨hqne, hs_eq⟩
    simpa [hs_eq] using hsEdge
  have hRcover : IsDirectedPathCoverOn D X (extendTerminalCover (P.erase p) q t) :=
    extendTerminalCover_isPathCoverOn heraseCover hqErase hqedge htX
  have hEraseSubset : TerminalSet ((P.erase p).erase q) ⊆ TerminalSet P := by
    intro x hx
    exact terminalSet_erase_subset (terminalSet_erase_subset hx)
  have hsErase : s ∉ TerminalSet ((P.erase p).erase q) :=
    not_mem_terminalSet_erase_of_path_ends_pathCoverOn heraseCover hqErase hqs
  have hstrict :
      TerminalSet (extendTerminalCover (P.erase p) q t) ⊂ TerminalSet P :=
    terminalSet_extendTerminalCover_ssubset_of_erase_subset
      (P := P) (Q := P.erase p) (q := q) (t := t) (z := s)
      hEraseSubset htP ⟨q, hqP, hqs⟩ hst hsErase
  exact (hmin.2 (extendTerminalCover (P.erase p) q t) hRcover) hstrict

lemma minimal_pathCoverOn_has_representatives (D : DirectedGraph V) [DecidableEq V] :
    ∀ X : Finset V, ∀ P : Finset (List V),
      InclusionMinimalTerminalPathCoverOn D X P →
        PathCoverHasIndependentRepresentatives D P := by
  classical
  have hmain : ∀ n : ℕ, ∀ X : Finset V, X.card = n →
      ∀ P : Finset (List V), InclusionMinimalTerminalPathCoverOn D X P →
        PathCoverHasIndependentRepresentatives D P := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro X hXcard P hmin
        by_cases hind : DirectedIndependentSet D (TerminalSet P)
        · exact directedIndependent_terminal_representatives_on hmin.1 hind
        · rcases exists_terminal_arc_of_not_directedIndependent hind with
            ⟨x, hxP, y, hyP, hxy_ne, hxy_edge⟩
          have step : ∀ {s t : V}, s ∈ TerminalSet P → t ∈ TerminalSet P →
              s ≠ t → D s t → PathCoverHasIndependentRepresentatives D P := by
            intro s t hsP htP hst hstEdge
            rcases htP with ⟨p, hpP, hpt⟩
            have hpPath : IsDirectedPath D p := hmin.1.1 p hpP
            rcases List.mem_getLast?_eq_getLast hpt with ⟨hpne, ht_eq⟩
            have htlast : p.getLast hpne = t := ht_eq.symm
            have hnotSingleton : p ≠ [t] :=
              terminal_path_not_singleton_of_terminal_arc hmin hpP hpne htlast hsP hst hstEdge
            have hdrop : p.dropLast ≠ [] :=
              dropLast_ne_nil_of_ne_singleton_getLast hpne htlast hnotSingleton
            have hpredEdge : D (p.dropLast.getLast hdrop) t := by
              simpa [htlast] using last_edge_dropLast_to_getLast hpPath hdrop
            have hminDrop :
                InclusionMinimalTerminalPathCoverOn D (X.erase t) (dropTerminalCover P p) :=
              dropTerminalCover_inclusionMinimal_of_terminal_arc
                hmin hpP hpne htlast hdrop hsP hst hpredEdge hstEdge
            have htX : t ∈ X := by
              exact hmin.1.2.2.1 p hpP t (by simpa [← htlast] using List.getLast_mem hpne)
            have hcard_lt : (X.erase t).card < n := by
              simpa [hXcard] using Finset.card_erase_lt_of_mem htX
            have hrepDrop : PathCoverHasIndependentRepresentatives D (dropTerminalCover P p) :=
              ih (X.erase t).card hcard_lt (X.erase t) rfl (dropTerminalCover P p) hminDrop
            exact representatives_of_dropTerminalCover hpP hrepDrop
          rcases hxy_edge with hxy | hyx
          · exact step hxP hyP hxy_ne hxy
          · exact step hyP hxP hxy_ne.symm hyx
  intro X P hmin
  exact hmain X.card X rfl P hmin

end GallaiMilgramAux

end Chapter02
end Diestel
