import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

namespace StableMatchingAux

variable {V : Type u} (G : SimpleGraph V)

def HeldBy (B : Set V) (P : Preferences G) (S : Finset G.edgeSet)
    (b : V) (e : G.edgeSet) : Prop :=
  e ∈ S ∧ b ∈ B ∧
    ∃ he : b ∈ (e : Sym2 V),
      ∀ f : G.edgeSet, f ∈ S → (hb : b ∈ (f : Sym2 V)) →
        f = e ∨ P.lt b ⟨f, hb⟩ ⟨e, he⟩

def Held (B : Set V) (P : Preferences G) (S : Finset G.edgeSet)
    (e : G.edgeSet) : Prop :=
  ∃ b : V, HeldBy G B P S b e

def PrefixState (A : Set V) (P : Preferences G) (S : Finset G.edgeSet) : Prop :=
  ∀ a : V, a ∈ A →
    ∀ e : G.edgeSet, e ∈ S → (he : a ∈ (e : Sym2 V)) →
      ∀ f : G.edgeSet, f ∉ S → (hf : a ∈ (f : Sym2 V)) →
        P.lt a ⟨f, hf⟩ ⟨e, he⟩

def AUniqueHeld (A B : Set V) (P : Preferences G) (S : Finset G.edgeSet) : Prop :=
  ∀ a : V, a ∈ A →
    ∀ e f : G.edgeSet, Held G B P S e → Held G B P S f →
      a ∈ (e : Sym2 V) → a ∈ (f : Sym2 V) → e = f

def ValidState (A B : Set V) (P : Preferences G) (S : Finset G.edgeSet) : Prop :=
  PrefixState G A P S ∧ AUniqueHeld G A B P S

def TerminalState (A B : Set V) (P : Preferences G) (S : Finset G.edgeSet) : Prop :=
  ∀ a : V, a ∈ A →
    (∀ e : G.edgeSet, Held G B P S e → a ∈ (e : Sym2 V) → False) →
      ∀ e : G.edgeSet, a ∈ (e : Sym2 V) → e ∈ S

def heldSubgraph (B : Set V) (P : Preferences G) (S : Finset G.edgeSet) :
    G.Subgraph where
  verts := {v | ∃ e : G.edgeSet, Held G B P S e ∧ v ∈ (e : Sym2 V)}
  Adj x y := ∃ e : G.edgeSet, Held G B P S e ∧ (e : Sym2 V) = s(x, y)
  adj_sub := by
    rintro x y ⟨e, _he, hexy⟩
    rw [← G.mem_edgeSet, ← hexy]
    exact e.2
  edge_vert := by
    rintro x y ⟨e, he, hexy⟩
    exact ⟨e, he, by simpa [hexy, Sym2.mem_iff]⟩
  symm := by
    rintro x y ⟨e, he, hexy⟩
    exact ⟨e, he, hexy.trans Sym2.eq_swap⟩

lemma heldBy_mem {B : Set V} {P : Preferences G} {S : Finset G.edgeSet}
    {b : V} {e : G.edgeSet} (h : HeldBy G B P S b e) : e ∈ S :=
  h.1

lemma heldBy_mem_right {B : Set V} {P : Preferences G} {S : Finset G.edgeSet}
    {b : V} {e : G.edgeSet} (h : HeldBy G B P S b e) : b ∈ B :=
  h.2.1

lemma heldBy_incident {B : Set V} {P : Preferences G} {S : Finset G.edgeSet}
    {b : V} {e : G.edgeSet} (h : HeldBy G B P S b e) :
    b ∈ (e : Sym2 V) :=
  h.2.2.choose

lemma held_mem {B : Set V} {P : Preferences G} {S : Finset G.edgeSet}
    {e : G.edgeSet} (h : Held G B P S e) : e ∈ S :=
  heldBy_mem G h.choose_spec

lemma held_incident_right {B : Set V} {P : Preferences G} {S : Finset G.edgeSet}
    {e : G.edgeSet} (h : Held G B P S e) :
    ∃ b : V, b ∈ B ∧ b ∈ (e : Sym2 V) :=
  ⟨h.choose, (heldBy_mem_right G h.choose_spec), (heldBy_incident G h.choose_spec)⟩

lemma heldBy_of_subset {B : Set V} {P : Preferences G}
    {S T : Finset G.edgeSet} {b : V} {e : G.edgeSet}
    (hST : S ⊆ T) (h : HeldBy G B P T b e) (heS : e ∈ S) :
    HeldBy G B P S b e := by
  refine ⟨heS, h.2.1, ?_⟩
  rcases h.2.2 with ⟨he, hbest⟩
  refine ⟨he, ?_⟩
  intro f hfS hbf
  exact hbest f (hST hfS) hbf

lemma held_of_subset {B : Set V} {P : Preferences G}
    {S T : Finset G.edgeSet} {e : G.edgeSet}
    (hST : S ⊆ T) (h : Held G B P T e) (heS : e ∈ S) :
    Held G B P S e :=
  ⟨h.choose, heldBy_of_subset G hST h.choose_spec heS⟩

lemma edge_unique_left {A B : Set V} (hAB : G.IsBipartiteWith A B)
    {e : G.edgeSet} {x y : V} (hxA : x ∈ A) (hyA : y ∈ A)
    (hx : x ∈ (e : Sym2 V)) (hy : y ∈ (e : Sym2 V)) : x = y := by
  by_contra hne
  have heq : (e : Sym2 V) = s(x, y) := (Sym2.mem_and_mem_iff hne).mp ⟨hx, hy⟩
  have hadj : G.Adj x y := by
    rw [← G.mem_edgeSet, ← heq]
    exact e.2
  rcases hAB.mem_of_adj hadj with h | h
  · exact (Set.disjoint_left.mp hAB.disjoint hyA) h.2
  · exact (Set.disjoint_left.mp hAB.disjoint hxA) h.1

lemma edge_unique_right {A B : Set V} (hAB : G.IsBipartiteWith A B)
    {e : G.edgeSet} {x y : V} (hxB : x ∈ B) (hyB : y ∈ B)
    (hx : x ∈ (e : Sym2 V)) (hy : y ∈ (e : Sym2 V)) : x = y := by
  by_contra hne
  have heq : (e : Sym2 V) = s(x, y) := (Sym2.mem_and_mem_iff hne).mp ⟨hx, hy⟩
  have hadj : G.Adj x y := by
    rw [← G.mem_edgeSet, ← heq]
    exact e.2
  rcases hAB.mem_of_adj hadj with h | h
  · exact (Set.disjoint_left.mp hAB.disjoint h.1) hxB
  · exact (Set.disjoint_left.mp hAB.disjoint h.2) hyB

lemma heldBy_same_holder_unique {B : Set V} {P : Preferences G}
    {S : Finset G.edgeSet} {b : V} {e f : G.edgeSet}
    (he : HeldBy G B P S b e) (hf : HeldBy G B P S b f) :
    e = f := by
  classical
  letI := P.strictTotal b
  rcases he.2.2 with ⟨hbe, hbest_e⟩
  rcases hf.2.2 with ⟨hbf, hbest_f⟩
  rcases hbest_e f hf.1 hbf with hfe | hfe
  · exact hfe.symm
  rcases hbest_f e he.1 hbe with hef | hef
  · exact hef
  exact False.elim (asymm_of (P.lt b) hfe hef)

lemma held_unique_at_right {A B : Set V} {P : Preferences G}
    {S : Finset G.edgeSet} (hAB : G.IsBipartiteWith A B)
    {b : V} (hb : b ∈ B) {e f : G.edgeSet}
    (he : Held G B P S e) (hf : Held G B P S f)
    (hbe : b ∈ (e : Sym2 V)) (hbf : b ∈ (f : Sym2 V)) :
    e = f := by
  rcases he with ⟨be, hbeHeld⟩
  rcases hf with ⟨bf, hbfHeld⟩
  have hbe_eq : be = b :=
    edge_unique_right G hAB (heldBy_mem_right G hbeHeld) hb
      (heldBy_incident G hbeHeld) hbe
  have hbf_eq : bf = b :=
    edge_unique_right G hAB (heldBy_mem_right G hbfHeld) hb
      (heldBy_incident G hbfHeld) hbf
  subst hbe_eq
  subst hbf_eq
  exact heldBy_same_holder_unique G hbeHeld hbfHeld

lemma heldSubgraph_isMatching {A B : Set V} {P : Preferences G}
    {S : Finset G.edgeSet} (hAB : G.IsBipartiteWith A B)
    (hcover : A ∪ B = Set.univ) (hValid : ValidState G A B P S) :
    (heldSubgraph G B P S).IsMatching := by
  classical
  intro v hv
  rcases hv with ⟨e, heHeld, hve⟩
  let w0 := Sym2.Mem.other hve
  have hother : s(v, w0) = (e : Sym2 V) := Sym2.other_spec hve
  refine ⟨w0, ?_, ?_⟩
  · exact ⟨e, heHeld, hother.symm⟩
  · intro y hy
    rcases hy with ⟨f, hfHeld, hfy⟩
    have hvf : v ∈ (f : Sym2 V) := by
      rw [hfy]
      simp [Sym2.mem_iff]
    have hef : e = f := by
      have hvside : v ∈ A ∨ v ∈ B := by
        have : v ∈ A ∪ B := by
          rw [hcover]
          exact Set.mem_univ v
        exact this
      rcases hvside with hvA | hvB
      · exact hValid.2 v hvA e f heHeld hfHeld hve hvf
      · exact held_unique_at_right G hAB hvB heHeld hfHeld hve hvf
    have hsym : s(v, y) = s(v, w0) := by
      calc
        s(v, y) = (f : Sym2 V) := hfy.symm
        _ = (e : Sym2 V) := by rw [hef]
        _ = s(v, w0) := hother.symm
    exact Sym2.congr_right.mp hsym

lemma heldSubgraph_edgeSet_iff {B : Set V} {P : Preferences G}
    {S : Finset G.edgeSet} (e : G.edgeSet) :
    (e : Sym2 V) ∈ (heldSubgraph G B P S).edgeSet ↔ Held G B P S e := by
  constructor
  · intro h
    rcases e with ⟨e, heG⟩
    induction e using Sym2.ind with
    | h x y =>
      have hadj : (heldSubgraph G B P S).Adj x y := by
        simpa [SimpleGraph.Subgraph.mem_edgeSet] using h
      rcases hadj with ⟨f, hfHeld, hfxy⟩
      have hfe : f = ⟨s(x, y), heG⟩ := by
        apply Subtype.ext
        exact hfxy
      simpa [hfe] using hfHeld
  · intro h
    rcases e with ⟨e, heG⟩
    induction e using Sym2.ind with
    | h x y =>
      have hadj : (heldSubgraph G B P S).Adj x y := ⟨⟨s(x, y), heG⟩, h, rfl⟩
      simpa [SimpleGraph.Subgraph.mem_edgeSet] using hadj

/--
Every nonempty finite set in a strict total order has a best element.

The relation direction is chosen to match `Preferences.lt`: `r x y` means
that `y` is preferred to `x`, so the best element `a` satisfies
`b = a ∨ r b a` for every `b` in the set.
-/
lemma exists_best_of_strictTotal {α : Type u} [DecidableEq α]
    (r : α → α → Prop) [IsStrictTotalOrder α r]
    (s : Finset α) (hs : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, b = a ∨ r b a := by
  classical
  refine Finset.induction_on s ?nil ?insert hs
  · intro hs0
    simp at hs0
  · intro a s _has ih _hne
    by_cases hs' : s.Nonempty
    · rcases ih hs' with ⟨m, hm, hbest⟩
      rcases trichotomous_of r a m with ham | rfl | hma
      · refine ⟨m, by simp [hm], ?_⟩
        intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact Or.inr ham
        · exact hbest b hb
      · refine ⟨a, by simp, ?_⟩
        intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact Or.inl rfl
        · exact hbest b hb
      · refine ⟨a, by simp, ?_⟩
        intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact Or.inl rfl
        · rcases hbest b hb with rfl | hbm
          · exact Or.inr hma
          · exact Or.inr (Trans.trans hbm hma)
    · refine ⟨a, by simp, ?_⟩
      intro b hb
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact False.elim (hs' ⟨b, hb⟩)

lemma exists_heldBy_of_mem [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {B : Set V} {P : Preferences G} {S : Finset G.edgeSet}
    {b : V} (hbB : b ∈ B) {e : G.edgeSet} (heS : e ∈ S)
    (hbe : b ∈ (e : Sym2 V)) :
    ∃ f : G.edgeSet, HeldBy G B P S b f := by
  classical
  let T : Finset (IncidentEdge G b) := Finset.univ.filter (fun ie => ie.1 ∈ S)
  have hTnon : T.Nonempty := by
    refine ⟨⟨e, hbe⟩, ?_⟩
    simp [T, heS]
  letI := P.strictTotal b
  rcases exists_best_of_strictTotal (P.lt b) T hTnon with ⟨m, hmT, hbest⟩
  have hmS : m.1 ∈ S := by
    simpa [T] using hmT
  refine ⟨m.1, hmS, hbB, ⟨m.2, ?_⟩⟩
  intro f hfS hbf
  have hfT : (⟨f, hbf⟩ : IncidentEdge G b) ∈ T := by
    simp [T, hfS]
  rcases hbest ⟨f, hbf⟩ hfT with hfm | hfm
  · exact Or.inl (congrArg (fun x : IncidentEdge G b => x.1) hfm)
  · exact Or.inr hfm

lemma edge_has_left_right {A B : Set V} (hAB : G.IsBipartiteWith A B)
    (e : G.edgeSet) :
    ∃ a : V, a ∈ A ∧ ∃ b : V, b ∈ B ∧
      a ∈ (e : Sym2 V) ∧ b ∈ (e : Sym2 V) := by
  rcases e with ⟨e, heG⟩
  induction e using Sym2.ind with
  | h x y =>
    have hadj : G.Adj x y := by
      simpa [SimpleGraph.mem_edgeSet] using heG
    rcases hAB.mem_of_adj hadj with h | h
    · exact ⟨x, h.1, y, h.2, by simp [Sym2.mem_iff], by simp [Sym2.mem_iff]⟩
    · exact ⟨y, h.2, x, h.1, by simp [Sym2.mem_iff], by simp [Sym2.mem_iff]⟩

lemma terminalState_stable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {A B : Set V} {P : Preferences G} {S : Finset G.edgeSet}
    (hAB : G.IsBipartiteWith A B) (hcover : A ∪ B = Set.univ)
    (hValid : ValidState G A B P S) (hTerm : TerminalState G A B P S) :
    StableMatching G P (heldSubgraph G B P S) := by
  classical
  refine ⟨heldSubgraph_isMatching G hAB hcover hValid, ?_⟩
  intro e heNotMatched
  have heNotHeld : ¬ Held G B P S e := by
    intro heHeld
    exact heNotMatched ((heldSubgraph_edgeSet_iff G e).mpr heHeld)
  rcases edge_has_left_right G hAB e with ⟨a, haA, b, hbB, hae, hbe⟩
  by_cases heS : e ∈ S
  · rcases exists_heldBy_of_mem G hbB heS hbe with ⟨f, hfHeldBy⟩
    have hfHeld : Held G B P S f := ⟨b, hfHeldBy⟩
    rcases hfHeldBy.2.2 with ⟨hbf, hbest⟩
    rcases hbest e heS hbe with hef | hlt
    · exact False.elim (heNotHeld (by simpa [hef] using hfHeld))
    · refine ⟨f, (heldSubgraph_edgeSet_iff G f).mpr hfHeld, b, hbe, hbf, hlt⟩
  · have hMatchedAtA : ∃ f : G.edgeSet, Held G B P S f ∧ a ∈ (f : Sym2 V) := by
      by_contra hnone
      have hnone' :
          ∀ f : G.edgeSet, Held G B P S f → a ∈ (f : Sym2 V) → False := by
        intro f hfHeld hfa
        exact hnone ⟨f, hfHeld, hfa⟩
      exact heS (hTerm a haA hnone' e hae)
    rcases hMatchedAtA with ⟨f, hfHeld, hfa⟩
    have hlt : P.lt a ⟨e, hae⟩ ⟨f, hfa⟩ :=
      hValid.1 a haA f (held_mem G hfHeld) hfa e heS hae
    refine ⟨f, (heldSubgraph_edgeSet_iff G f).mpr hfHeld, a, hae, hfa, hlt⟩

lemma validState_empty {A B : Set V} {P : Preferences G} :
    ValidState G A B P (∅ : Finset G.edgeSet) := by
  constructor
  · intro a ha e heS
    exact False.elim (by simpa using heS)
  · intro a ha e f heHeld hfHeld hae hfa
    exact False.elim (by simpa using (held_mem G heHeld))

lemma validState_extend_of_not_terminal [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {A B : Set V} {P : Preferences G} {S : Finset G.edgeSet}
    (hAB : G.IsBipartiteWith A B) (hValid : ValidState G A B P S)
    (hnot : ¬ TerminalState G A B P S) :
    ∃ T : Finset G.edgeSet, ValidState G A B P T ∧ S.card < T.card := by
  classical
  rw [TerminalState] at hnot
  push Not at hnot
  rcases hnot with ⟨a, haA, hUnmatched, e0, he0a, he0NotS⟩
  let U : Finset (IncidentEdge G a) := Finset.univ.filter (fun ie => ie.1 ∉ S)
  have hUnonempty : U.Nonempty := by
    refine ⟨⟨e0, he0a⟩, ?_⟩
    simp [U, he0NotS]
  letI := P.strictTotal a
  rcases exists_best_of_strictTotal (P.lt a) U hUnonempty with ⟨m, hmU, hbest⟩
  let g : G.edgeSet := m.1
  have hga : a ∈ (g : Sym2 V) := m.2
  have hgNotS : g ∉ S := by
    simpa [U, g] using hmU
  let T : Finset G.edgeSet := insert g S
  have hST : S ⊆ T := by
    intro q hq
    simp [T, hq]
  have held_old_of_ne :
      ∀ {q : G.edgeSet}, Held G B P T q → q ≠ g → Held G B P S q := by
    intro q hqHeld hqne
    have hqT : q ∈ T := held_mem G hqHeld
    have hqS : q ∈ S := by
      have hqT' : q ∈ insert g S := by
        simpa [T] using hqT
      rw [Finset.mem_insert] at hqT'
      rcases hqT' with hqeq | hqS
      · exact False.elim (hqne hqeq)
      · exact hqS
    exact held_of_subset G hST hqHeld hqS
  refine ⟨T, ?_, ?_⟩
  · constructor
    · intro x hxA e heT hxe f hfNotT hxf
      have hfNotS : f ∉ S := by
        intro hfS
        exact hfNotT (by simp [T, hfS])
      have heT' : e ∈ insert g S := by
        simpa [T] using heT
      rw [Finset.mem_insert] at heT'
      rcases heT' with heg | heS
      · subst e
        have hxa : x = a :=
          edge_unique_left G hAB hxA haA hxe hga
        subst x
        have hfU : (⟨f, hxf⟩ : IncidentEdge G a) ∈ U := by
          simp [U, hfNotS]
        rcases hbest ⟨f, hxf⟩ hfU with hfg | hlt
        · have hfg' : f = g :=
            congrArg (fun ie : IncidentEdge G a => ie.1) hfg
          exact False.elim (hfNotT (by simp [T, hfg']))
        · simpa [g, hga] using hlt
      · exact hValid.1 x hxA e heS hxe f hfNotS hxf
    · intro x hxA e f heHeldT hfHeldT hxe hxf
      by_cases heg : e = g
      · subst e
        by_cases hfg : f = g
        · exact hfg.symm
        · have hfOld : Held G B P S f := held_old_of_ne hfHeldT hfg
          have hxa : x = a :=
            edge_unique_left G hAB hxA haA hxe hga
          subst x
          exact False.elim (hUnmatched f hfOld hxf)
      · have heOld : Held G B P S e := held_old_of_ne heHeldT heg
        by_cases hfg : f = g
        · subst f
          have hxa : x = a :=
            edge_unique_left G hAB hxA haA hxf hga
          subst x
          exact False.elim (hUnmatched e heOld hxe)
        · have hfOld : Held G B P S f := held_old_of_ne hfHeldT hfg
          exact hValid.2 x hxA e f heOld hfOld hxe hxf
  · have hcard : (insert g S).card = S.card + 1 :=
      Finset.card_insert_of_notMem hgNotS
    simpa [T, hcard] using Nat.lt_succ_self S.card

end StableMatchingAux

end Chapter02
end Diestel
