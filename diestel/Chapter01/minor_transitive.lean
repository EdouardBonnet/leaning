import Chapter01.minor_basic

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v w

private def composedBranchSet {A : Type u} {B : Type v} {C : Type w}
    {X : SimpleGraph A} {Y : SimpleGraph B} {Z : SimpleGraph C}
    (MXY : Model X Y) (MYZ : Model Y Z) (x : A) : Set C :=
  {z | ∃ y : B, y ∈ MXY.branchSet x ∧ z ∈ MYZ.branchSet y}

private lemma walk_inside_model_branch {B : Type v} {C : Type w}
    {Y : SimpleGraph B} {Z : SimpleGraph C} (M : Model Y Z)
    {y : B} {a b : C} (ha : a ∈ M.branchSet y) (hb : b ∈ M.branchSet y) :
    ∃ p : Z.Walk a b, ∀ z : C, z ∈ p.support → z ∈ M.branchSet y := by
  let A := M.branchSet y
  let aA : A := ⟨a, ha⟩
  let bA : A := ⟨b, hb⟩
  have hreach : (Z.induce A).Reachable aA bA := (M.connected y) aA bA
  rcases hreach with ⟨q⟩
  let incl : (Z.induce A) →g Z :=
    { toFun := fun z => z.1
      map_rel' := by
        intro z z' hzz'
        exact hzz' }
  refine ⟨q.map incl, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  rcases List.mem_map.mp hz with ⟨zA, _hzA, rfl⟩
  exact zA.2

private lemma composed_walk_of_index_walk {A : Type u} {B : Type v} {C : Type w}
    {X : SimpleGraph A} {Y : SimpleGraph B} {Z : SimpleGraph C}
    (MXY : Model X Y) (MYZ : Model Y Z) (x : A) :
    ∀ {y₀ y₁ : MXY.branchSet x},
      (Y.induce (MXY.branchSet x)).Walk y₀ y₁ →
        ∀ {z₀ z₁ : C}, z₀ ∈ MYZ.branchSet y₀.1 → z₁ ∈ MYZ.branchSet y₁.1 →
          ∃ p : Z.Walk z₀ z₁,
            ∀ z : C, z ∈ p.support → z ∈ composedBranchSet MXY MYZ x := by
  intro y₀ y₁ q
  induction q with
  | nil =>
      rename_i y
      intro z₀ z₁ hz₀ hz₁
      obtain ⟨p, hp⟩ := walk_inside_model_branch MYZ hz₀ hz₁
      refine ⟨p, ?_⟩
      intro z hz
      exact ⟨y.1, y.2, hp z hz⟩
  | cons h q ih =>
      rename_i yStart _yNext _yEnd
      intro z₀ z₂ hz₀ hz₂
      have hY : Y.Adj _ _ := h
      obtain ⟨a, ha, b, hb, hab⟩ := MYZ.adjacent hY
      obtain ⟨p₀, hp₀⟩ := walk_inside_model_branch MYZ hz₀ ha
      obtain ⟨p₂, hp₂⟩ := ih hb hz₂
      let bridge : Z.Walk a z₂ := SimpleGraph.Walk.cons hab p₂
      let p : Z.Walk z₀ z₂ := p₀.append bridge
      refine ⟨p, ?_⟩
      intro z hz
      have hz' : z ∈ p₀.support ∨ z ∈ p₂.support := by
        have hz'' : z ∈ p₀.support ++ p₂.support := by
          simpa [p, bridge, SimpleGraph.Walk.support_append,
            SimpleGraph.Walk.support_cons] using hz
        exact List.mem_append.mp hz''
      rcases hz' with hz' | hz'
      · exact ⟨_, yStart.2, hp₀ z hz'⟩
      · exact hp₂ z hz'

private noncomputable def walk_induce_of_support {C : Type w} {Z : SimpleGraph C} {S : Set C}
    {a b : C} (p : Z.Walk a b) (ha : a ∈ S) (hb : b ∈ S)
    (hp : ∀ z : C, z ∈ p.support → z ∈ S) :
    (Z.induce S).Walk ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction p with
  | nil =>
      have hEq : (⟨_, ha⟩ : S) = ⟨_, hb⟩ := Subtype.ext rfl
      simpa [hEq] using (SimpleGraph.Walk.nil : (Z.induce S).Walk ⟨_, ha⟩ ⟨_, ha⟩)
  | cons hab q ih =>
      rename_i u v w
      have hv : v ∈ S := by
        apply hp v
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
      have htail :
          ∀ z : C, z ∈ q.support → z ∈ S := by
        intro z hz
        exact hp z (by simp [SimpleGraph.Walk.support_cons, hz])
      exact SimpleGraph.Walk.cons (show (Z.induce S).Adj ⟨u, ha⟩ ⟨v, hv⟩ from hab)
        (ih hv hb htail)

private lemma composed_branch_connected {A : Type u} {B : Type v} {C : Type w}
    {X : SimpleGraph A} {Y : SimpleGraph B} {Z : SimpleGraph C}
    (MXY : Model X Y) (MYZ : Model Y Z) (x : A) :
    (Z.induce (composedBranchSet MXY MYZ x)).Connected := by
  classical
  obtain ⟨y, hy⟩ := MXY.nonempty x
  obtain ⟨z, hz⟩ := MYZ.nonempty y
  let zC : composedBranchSet MXY MYZ x := ⟨z, ⟨y, hy, hz⟩⟩
  letI : Nonempty (composedBranchSet MXY MYZ x) := ⟨zC⟩
  refine SimpleGraph.Connected.mk ?_
  intro a b
  rcases a.2 with ⟨ya, hya, hza⟩
  rcases b.2 with ⟨yb, hyb, hzb⟩
  have hreach :
      (Y.induce (MXY.branchSet x)).Reachable ⟨ya, hya⟩ ⟨yb, hyb⟩ :=
    (MXY.connected x) ⟨ya, hya⟩ ⟨yb, hyb⟩
  rcases hreach with ⟨q⟩
  obtain ⟨p, hp⟩ := composed_walk_of_index_walk MXY MYZ x q hza hzb
  exact ⟨walk_induce_of_support p a.2 b.2 hp⟩

theorem isMinor_trans {A : Type u} {B : Type v} {C : Type w}
    (X : SimpleGraph A) (Y : SimpleGraph B) (Z : SimpleGraph C) :
    IsMinor X Y → IsMinor Y Z → IsMinor X Z := by
  rintro ⟨MXY⟩ ⟨MYZ⟩
  refine ⟨{
    branchSet := composedBranchSet MXY MYZ
    nonempty := ?_
    pairwise_disjoint := ?_
    connected := ?_
    adjacent := ?_
  }⟩
  · intro x
    obtain ⟨y, hy⟩ := MXY.nonempty x
    obtain ⟨z, hz⟩ := MYZ.nonempty y
    exact ⟨z, y, hy, hz⟩
  · intro x x' hxx'
    rw [Set.disjoint_left]
    intro z hz hz'
    rcases hz with ⟨y, hy, hzy⟩
    rcases hz' with ⟨y', hy', hzy'⟩
    by_cases hyy' : y = y'
    · subst y'
      have hdisj := MXY.pairwise_disjoint hxx'
      change Disjoint (MXY.branchSet x) (MXY.branchSet x') at hdisj
      rw [Set.disjoint_left] at hdisj
      exact hdisj hy hy'
    · have hdisj := MYZ.pairwise_disjoint hyy'
      change Disjoint (MYZ.branchSet y) (MYZ.branchSet y') at hdisj
      rw [Set.disjoint_left] at hdisj
      exact hdisj hzy hzy'
  · intro x
    exact composed_branch_connected MXY MYZ x
  · intro x x' hxx'
    obtain ⟨y, hy, y', hy', hyy'⟩ := MXY.adjacent hxx'
    obtain ⟨z, hz, z', hz', hzz'⟩ := MYZ.adjacent hyy'
    exact ⟨z, ⟨y, hy, hz⟩, z', ⟨y', hy', hz'⟩, hzz'⟩

end Chapter01
end Diestel
