import TwinWidth.Graph.BonnetDepres
import TwinWidth.Graph.Partition
import Batteries.Data.Fin.OfBits
import Mathlib.Combinatorics.Pigeonhole

/-!
# Lower-bound infrastructure for the Bonnet--Déprés graphs

This file collects the concrete, reusable facts about the Bonnet--Déprés
construction that are used in the twin-width lower-bound proof.  The statements
are deliberately phrased in the semantic partition language from
`TwinWidth.Graph.Partition`: red adjacency means non-homogeneity of two bags in
the original graph.
-/

namespace TwinWidth
namespace SimpleGraph

namespace BonnetDepres

/-- The explicit Bonnet--Déprés tree depth is positive. -/
theorem depth_pos (k : ℕ) : 0 < bonnetDepresDepth k := by
  simp [bonnetDepresDepth]

/-- The explicit depth is greater than `2`, so grandchildren have children. -/
theorem two_lt_depth (k : ℕ) : 2 < bonnetDepresDepth k := by
  simp [bonnetDepresDepth]

/-- The root is an internal tree node in the Bonnet--Déprés construction. -/
theorem root_level_lt_depth (k : ℕ) :
    (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k)).1.val <
      bonnetDepresDepth k := by
  simp [FullTreeNode.root, depth_pos k]

/-- Internal nodes of the Bonnet--Déprés tree are precisely nodes with children. -/
def IsInternal {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) : Prop :=
  u.1.val < bonnetDepresDepth k

/-- A preleaf is an internal node whose children are leaves. -/
def IsPreleaf {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) : Prop :=
  u.1.val + 1 = bonnetDepresDepth k

/-- A non-preleaf internal node is an internal node whose children are internal. -/
def IsNonPreleafInternal {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) : Prop :=
  u.1.val + 1 < bonnetDepresDepth k

theorem isInternal_iff {k : ℕ}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)} :
    IsInternal u ↔ u.1.val < bonnetDepresDepth k := Iff.rfl

theorem isNonPreleafInternal.isInternal {k : ℕ}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : IsNonPreleafInternal u) :
    IsInternal u := by
  unfold IsNonPreleafInternal IsInternal at *
  omega

theorem child_isInternal_of_isNonPreleafInternal {k : ℕ}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : IsNonPreleafInternal u)
    (label : Fin (bonnetDepresBranch k)) :
    IsInternal (FullTreeNode.child u
      (isNonPreleafInternal.isInternal h) label) := by
  unfold IsNonPreleafInternal at h
  unfold IsInternal
  simp [FullTreeNode.child]
  omega

/-- A canonical apex vertex distinct from `x`. -/
def otherApex (k : ℕ) (x : Fin (bonnetDepresApexCount k)) :
    Fin (bonnetDepresApexCount k) :=
  if hx : x.val = 0 then
    ⟨1, by
      unfold bonnetDepresApexCount
      omega⟩
  else
    ⟨0, by
      unfold bonnetDepresApexCount
      omega⟩

theorem otherApex_ne (k : ℕ) (x : Fin (bonnetDepresApexCount k)) :
    otherApex k x ≠ x := by
  unfold otherApex
  by_cases hx : x.val = 0
  · intro h
    have hval := congrArg Fin.val h
    simp [hx] at hval
  · intro h
    have hval := congrArg Fin.val h
    simp [hx] at hval
    exact hx hval.symm

/-- The bit vector coding the singleton apex neighborhood `{y}`. -/
def singletonApexNeighborhood {k : ℕ}
    (y : Fin (bonnetDepresApexCount k)) :
    Fin (bonnetDepresApexCount k) → Bool :=
  fun z => decide (z = y)

@[simp] theorem singletonApexNeighborhood_self {k : ℕ}
    (y : Fin (bonnetDepresApexCount k)) :
    singletonApexNeighborhood y y = true := by
  simp [singletonApexNeighborhood]

@[simp] theorem singletonApexNeighborhood_of_ne {k : ℕ}
    {x y : Fin (bonnetDepresApexCount k)} (hxy : x ≠ y) :
    singletonApexNeighborhood y x = false := by
  simp [singletonApexNeighborhood, hxy]

/-- The child label whose bits realize a prescribed neighborhood in the apex
set.  Bits are read little-endian, matching `Nat.testBit`. -/
def labelOfNeighborhood {k : ℕ}
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    Fin (bonnetDepresBranch k) := by
  simpa [bonnetDepresBranch] using (Fin.ofBits f)

@[simp] theorem labelOfNeighborhood_testBit {k : ℕ}
    (f : Fin (bonnetDepresApexCount k) → Bool)
    (x : Fin (bonnetDepresApexCount k)) :
    (labelOfNeighborhood f).val.testBit x.val = f x := by
  unfold labelOfNeighborhood
  simp [bonnetDepresBranch, Nat.testBit_ofBits_lt f x.val x.isLt]

/-- Distinct prescribed apex neighborhoods give distinct child labels. -/
theorem labelOfNeighborhood_injective {k : ℕ} :
    Function.Injective
      (labelOfNeighborhood (k := k) :
        (Fin (bonnetDepresApexCount k) → Bool) →
          Fin (bonnetDepresBranch k)) := by
  intro f g h
  funext x
  have hbit := congrArg (fun label : Fin (bonnetDepresBranch k) =>
    label.val.testBit x.val) h
  simpa using hbit

/-- Two distinct labels below `2^n` differ on one of their first `n` bits. -/
theorem exists_bit_ne_of_fin_pow_ne {n : ℕ}
    {a b : Fin (2 ^ n)} (hab : a ≠ b) :
    ∃ x : Fin n, a.val.testBit x.val ≠ b.val.testBit x.val := by
  by_contra hnone
  have hbits : ∀ i : ℕ, a.val.testBit i = b.val.testBit i := by
    intro i
    by_cases hi : i < n
    · by_contra hbit
      exact hnone ⟨⟨i, hi⟩, hbit⟩
    · have hni : n ≤ i := le_of_not_gt hi
      have hpow : 2 ^ n ≤ 2 ^ i := by
        apply Nat.pow_le_pow_right
        · omega
        · exact hni
      have ha : a.val.testBit i = false :=
        Nat.testBit_eq_false_of_lt (a.isLt.trans_le hpow)
      have hb : b.val.testBit i = false :=
        Nat.testBit_eq_false_of_lt (b.isLt.trans_le hpow)
      rw [ha, hb]
  apply hab
  exact Fin.ext (Nat.eq_of_testBit_eq hbits)

/-- For a fixed internal node, child labels inject into actual children. -/
theorem child_injective_label {branch depth : ℕ}
    (parent : FullTreeNode branch depth) (hlevel : parent.1.val < depth) :
    Function.Injective (FullTreeNode.child parent hlevel) := by
  intro a b h
  have hposa : 0 < (FullTreeNode.child parent hlevel a).1.val := by
    simp [FullTreeNode.child]
  have hposb : 0 < (FullTreeNode.child parent hlevel b).1.val := by
    simp [FullTreeNode.child]
  have hposb' : 0 < (FullTreeNode.child parent hlevel a).1.val := by
    simpa [h] using hposb
  have hb :
      FullTreeNode.lastLabel (FullTreeNode.child parent hlevel a) hposb' = b := by
    simpa [h] using FullTreeNode.lastLabel_child parent hlevel b hposb
  calc
    a = FullTreeNode.lastLabel (FullTreeNode.child parent hlevel a) hposa :=
      (FullTreeNode.lastLabel_child parent hlevel a hposa).symm
    _ = FullTreeNode.lastLabel (FullTreeNode.child parent hlevel a) hposb' := by
      congr
    _ = b := hb

/-- Ancestor relation in the concrete full tree: `u` is an ancestor of `v` when
the path of `u` is a prefix of the path of `v`. -/
def IsTreeAncestor {branch depth : ℕ}
    (u v : FullTreeNode branch depth) : Prop :=
  ∃ hle : u.1.val ≤ v.1.val,
    ∀ i : Fin u.1.val, v.2 ⟨i.val, lt_of_lt_of_le i.isLt hle⟩ = u.2 i

theorem isTreeAncestor_refl {branch depth : ℕ}
    (u : FullTreeNode branch depth) :
    IsTreeAncestor u u := by
  refine ⟨le_rfl, ?_⟩
  intro i
  rfl

theorem isTreeAncestor_child {branch depth : ℕ}
    (u : FullTreeNode branch depth) (hlevel : u.1.val < depth)
    (label : Fin branch) :
    IsTreeAncestor u (FullTreeNode.child u hlevel label) := by
  refine ⟨by simp [FullTreeNode.child], ?_⟩
  intro i
  simp [FullTreeNode.child, i.isLt]

/-- A parent is an ancestor of its child. -/
theorem isTreeAncestor_of_isParent {branch depth : ℕ}
    {parent child : FullTreeNode branch depth}
    (h : FullTreeNode.IsParent parent child) :
    IsTreeAncestor parent child := by
  rcases h with ⟨hlevel, hpath⟩
  refine ⟨by omega, ?_⟩
  intro i
  exact hpath i

/-- The parent endpoint of a full-tree parent relation is internal. -/
theorem parent_level_lt_depth_of_isParent {branch depth : ℕ}
    {parent child : FullTreeNode branch depth}
    (h : FullTreeNode.IsParent parent child) :
    parent.1.val < depth := by
  rcases h with ⟨hlevel, _hpath⟩
  exact Nat.lt_of_succ_lt_succ (by simpa [hlevel] using child.1.isLt)

theorem isTreeAncestor_trans {branch depth : ℕ}
    {u v w : FullTreeNode branch depth}
    (huv : IsTreeAncestor u v) (hvw : IsTreeAncestor v w) :
    IsTreeAncestor u w := by
  rcases huv with ⟨huv_le, huv_path⟩
  rcases hvw with ⟨hvw_le, hvw_path⟩
  refine ⟨huv_le.trans hvw_le, ?_⟩
  intro i
  exact (hvw_path ⟨i.val, lt_of_lt_of_le i.isLt huv_le⟩).trans (huv_path i)

/-- Two ancestors of a common full-tree node are comparable. -/
theorem isTreeAncestor_or_isTreeAncestor_of_common_descendant {branch depth : ℕ}
    {u v w : FullTreeNode branch depth}
    (huw : IsTreeAncestor u w) (hvw : IsTreeAncestor v w) :
    IsTreeAncestor u v ∨ IsTreeAncestor v u := by
  rcases huw with ⟨huw_le, huw_path⟩
  rcases hvw with ⟨hvw_le, hvw_path⟩
  by_cases huv_level : u.1.val ≤ v.1.val
  · left
    refine ⟨huv_level, ?_⟩
    intro i
    have hvw_i :=
      hvw_path ⟨i.val, lt_of_lt_of_le i.isLt huv_level⟩
    have huw_i := huw_path i
    exact hvw_i.symm.trans (by simpa using huw_i)
  · right
    have hvu_level : v.1.val ≤ u.1.val := le_of_not_ge huv_level
    refine ⟨hvu_level, ?_⟩
    intro i
    have huw_i :=
      huw_path ⟨i.val, lt_of_lt_of_le i.isLt hvu_level⟩
    have hvw_i := hvw_path i
    exact huw_i.symm.trans (by simpa using hvw_i)

/-- Two ancestors of the same node at the same level are equal. -/
theorem eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq {branch depth : ℕ}
    {u v w : FullTreeNode branch depth}
    (huw : IsTreeAncestor u w) (hvw : IsTreeAncestor v w)
    (hlevel : u.1.val = v.1.val) :
    u = v := by
  rcases huw with ⟨huw_le, huw_path⟩
  rcases hvw with ⟨hvw_le, hvw_path⟩
  cases u with
  | mk ulevel upath =>
  cases v with
  | mk vlevel vpath =>
    simp only at hlevel huw_path hvw_path ⊢
    have hlevel_fin : ulevel = vlevel := Fin.ext hlevel
    subst vlevel
    congr
    funext i
    exact (huw_path i).symm.trans (hvw_path i)

/-- If `z` is a strict descendant of `q`, then the parent of `z` is still a
descendant of `q`. -/
theorem isTreeAncestor_parent_of_strict_descendant {branch depth : ℕ}
    {q p z : FullTreeNode branch depth}
    (hqz : IsTreeAncestor q z)
    (hpz : FullTreeNode.IsParent p z)
    (hqzLevel : q.1.val < z.1.val) :
    IsTreeAncestor q p := by
  rcases hqz with ⟨hqz_le, hqz_path⟩
  rcases hpz with ⟨hz_level, hpz_path⟩
  have hq_le_p : q.1.val ≤ p.1.val := by omega
  refine ⟨hq_le_p, ?_⟩
  intro i
  have hp := hpz_path ⟨i.val, lt_of_lt_of_le i.isLt hq_le_p⟩
  have hq := hqz_path i
  exact hp.symm.trans hq

/-- A parent on one branch of an ancestor-antichain is not adjacent to a
descendant on another branch. -/
theorem not_tree_adj_parent_descendant_of_antichain {branch depth : ℕ}
    {a b za zb p : FullTreeNode branch depth}
    (hanti : ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (haza : IsTreeAncestor a za)
    (hbzb : IsTreeAncestor b zb)
    (hpza : FullTreeNode.IsParent p za)
    (ha_strict : a.1.val < za.1.val) :
    ¬ (FullTreeNode.graph branch depth).Adj p zb := by
  intro hadj
  have hap : IsTreeAncestor a p :=
    isTreeAncestor_parent_of_strict_descendant haza hpza ha_strict
  rcases hadj with hpzb | hzbp
  · have hazb : IsTreeAncestor a zb :=
      isTreeAncestor_trans hap (isTreeAncestor_of_isParent hpzb)
    rcases isTreeAncestor_or_isTreeAncestor_of_common_descendant hazb hbzb with
      hab | hba
    · exact hanti.1 hab
    · exact hanti.2 hba
  · have hbp : IsTreeAncestor b p :=
      isTreeAncestor_trans hbzb (isTreeAncestor_of_isParent hzbp)
    rcases isTreeAncestor_or_isTreeAncestor_of_common_descendant hap hbp with
      hab | hba
    · exact hanti.1 hab
    · exact hanti.2 hba

/-- Ranked variant of `not_tree_adj_parent_descendant_of_antichain`: when the
selected descendant on the first branch is the branch node itself, the distinct
level invariant rules out the only sibling-parent obstruction. -/
theorem not_tree_adj_parent_descendant_of_ranked_antichain {branch depth : ℕ}
    {a b za zb p : FullTreeNode branch depth}
    (hanti : ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hlevel_ne : a.1.val ≠ b.1.val)
    (haza : IsTreeAncestor a za)
    (hbzb : IsTreeAncestor b zb)
    (hpza : FullTreeNode.IsParent p za) :
    ¬ (FullTreeNode.graph branch depth).Adj p zb := by
  by_cases ha_strict : a.1.val < za.1.val
  · exact not_tree_adj_parent_descendant_of_antichain
      hanti haza hbzb hpza ha_strict
  · intro hadj
    have hza_level : za.1.val = a.1.val := by
      rcases haza with ⟨hlevel, _⟩
      omega
    have hza_eq : a = za :=
      eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
        haza (isTreeAncestor_refl za) hza_level.symm
    subst za
    rcases hadj with hpzb | hzbp
    · have hp_level := FullTreeNode.isParent_level hpza
      have hzb_level := FullTreeNode.isParent_level hpzb
      by_cases hb_level : b.1.val = zb.1.val
      · have hb_eq_zb : b = zb :=
          eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
            hbzb (isTreeAncestor_refl zb) hb_level
        subst zb
        exact hlevel_ne (by omega)
      · have hb_lt_zb : b.1.val < zb.1.val := by
          rcases hbzb with ⟨hb_le, _⟩
          omega
        have hbp : IsTreeAncestor b p :=
          isTreeAncestor_parent_of_strict_descendant hbzb hpzb hb_lt_zb
        have hba : IsTreeAncestor b a :=
          isTreeAncestor_trans hbp (isTreeAncestor_of_isParent hpza)
        exact hanti.2 hba
    · have hbp : IsTreeAncestor b p :=
        isTreeAncestor_trans hbzb (isTreeAncestor_of_isParent hzbp)
      have hba : IsTreeAncestor b a :=
        isTreeAncestor_trans hbp (isTreeAncestor_of_isParent hpza)
      exact hanti.2 hba

/-- The root child realizing a prescribed apex neighborhood. -/
def rootChildWithNeighborhood (k : ℕ)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
  FullTreeNode.child
    (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
    (root_level_lt_depth k) (labelOfNeighborhood f)

@[simp] theorem rootChildWithNeighborhood_apexAdj (k : ℕ)
    (f : Fin (bonnetDepresApexCount k) → Bool)
    (x : Fin (bonnetDepresApexCount k)) :
    bonnetDepresApexAdj x (rootChildWithNeighborhood k f) ↔
      f x = true := by
  rw [rootChildWithNeighborhood,
    bonnetDepresApexAdj_child x
      (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
      (root_level_lt_depth k) (labelOfNeighborhood f)]
  simp

/-- The tree root is adjacent to every root child. -/
theorem root_adj_rootChildWithNeighborhood (k : ℕ)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    (bonnetDepresGraph k).Adj
      (Sum.inr (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k)) :
        BonnetDepresVertex k)
      (Sum.inr (rootChildWithNeighborhood k f)) := by
  simpa [bonnetDepresGraph, rootChildWithNeighborhood] using
    (Or.inl
      (FullTreeNode.isParent_child
        (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
        (root_level_lt_depth k) (labelOfNeighborhood f)))

@[simp] theorem rootChildWithNeighborhood_level (k : ℕ)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    (rootChildWithNeighborhood k f).1.val = 1 := by
  simp [rootChildWithNeighborhood, FullTreeNode.child, FullTreeNode.root]

/-- Every root child is internal in the Bonnet--Déprés tree. -/
theorem rootChildWithNeighborhood_isInternal (k : ℕ)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    IsInternal (rootChildWithNeighborhood k f) := by
  unfold IsInternal
  rw [rootChildWithNeighborhood_level]
  have hdepth := two_lt_depth k
  omega

/-- Every root child is a non-preleaf internal node in the chosen depth. -/
theorem rootChildWithNeighborhood_isNonPreleafInternal (k : ℕ)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    IsNonPreleafInternal (rootChildWithNeighborhood k f) := by
  unfold IsNonPreleafInternal
  rw [rootChildWithNeighborhood_level]
  exact two_lt_depth k

/-- A tree vertex whose level is neither root level nor grandchild level is not
adjacent to any root child. -/
theorem not_adj_rootChildWithNeighborhood_of_level_ne_zero_ne_two (k : ℕ)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hzero : u.1.val ≠ 0) (htwo : u.1.val ≠ 2)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    ¬ (bonnetDepresGraph k).Adj
      (Sum.inr u : BonnetDepresVertex k)
      (Sum.inr (rootChildWithNeighborhood k f)) := by
  intro hadj
  have htree :
      (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj
        u (rootChildWithNeighborhood k f) := by
    simpa [bonnetDepresGraph] using hadj
  have hlevels :=
    FullTreeNode.adj_level_eq_succ_or_succ_eq htree
  rw [rootChildWithNeighborhood_level] at hlevels
  rcases hlevels with h | h
  · exact hzero (by omega)
  · exact htwo (by omega)

/-- The map from apex-neighborhood bit vectors to root children is injective. -/
theorem rootChildWithNeighborhood_injective (k : ℕ) :
    Function.Injective (rootChildWithNeighborhood k) := by
  intro f g h
  exact labelOfNeighborhood_injective
    ((child_injective_label
      (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
      (root_level_lt_depth k)) h)

/-- Every level-one tree node is one of the root children selected by a bit
vector. -/
theorem exists_rootChildWithNeighborhood_eq_of_level_one (k : ℕ)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : u.1.val = 1) :
    ∃ f : Fin (bonnetDepresApexCount k) → Bool,
      rootChildWithNeighborhood k f = u := by
  let hpos : 0 < u.1.val := by omega
  let f : Fin (bonnetDepresApexCount k) → Bool :=
    fun x => (FullTreeNode.lastLabel u hpos).val.testBit x.val
  refine ⟨f, ?_⟩
  have hlabel :
      labelOfNeighborhood f = FullTreeNode.lastLabel u hpos := by
    apply Fin.ext
    simp [labelOfNeighborhood, bonnetDepresBranch, f, Nat.ofBits_testBit,
      Nat.mod_eq_of_lt]
  cases u with
  | mk level path =>
    cases level with
    | mk n hn =>
      simp only at hlevel
      subst n
      simp [rootChildWithNeighborhood, FullTreeNode.child, FullTreeNode.root]
      funext i
      have hi : i = (0 : Fin 1) := Fin.ext (by omega)
      subst i
      simpa [FullTreeNode.lastLabel, f] using hlabel

/-- Bit vectors that contain `x` and omit `y`; these are exactly the root
children separating the two apex vertices `x` and `y`. -/
abbrev SeparatingApexBits {k : ℕ}
    (x y : Fin (bonnetDepresApexCount k)) : Type :=
  {f : Fin (bonnetDepresApexCount k) → Bool // f x = true ∧ f y = false}

/-- The free coordinates of a bit vector separating two distinct apex
vertices. -/
abbrev RemainingApexVertex {k : ℕ}
    (x y : Fin (bonnetDepresApexCount k)) : Type :=
  {z : Fin (bonnetDepresApexCount k) // z ≠ x ∧ z ≠ y}

/-- Bit vectors whose value at a fixed apex vertex is prescribed. -/
abbrev ApexBitFiber {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) (b : Bool) : Type :=
  {f : Fin (bonnetDepresApexCount k) → Bool // f x = b}

/-- Apex coordinates other than a fixed one. -/
abbrev OtherApexVertex {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) : Type :=
  {z : Fin (bonnetDepresApexCount k) // z ≠ x}

/-- A fixed bit at `x` leaves arbitrary choices on all other apex vertices. -/
noncomputable def apexBitFiberEquiv {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) (b : Bool) :
    ApexBitFiber x b ≃ (OtherApexVertex x → Bool) where
  toFun f z := f.1 z.1
  invFun g :=
    ⟨fun z => if hx : z = x then b else g ⟨z, hx⟩, by simp⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext z
    by_cases hx : z = x
    · subst z
      simp [f.2]
    · simp [hx]
  right_inv := by
    intro g
    funext z
    rcases z with ⟨z, hz⟩
    simp [hz]

/-- The number of apex coordinates other than one fixed coordinate. -/
theorem card_otherApexVertex {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) :
    Fintype.card (OtherApexVertex x) = bonnetDepresApexCount k - 1 := by
  classical
  have hcompl :
      Fintype.card {z : Fin (bonnetDepresApexCount k) // z ≠ x} =
        Fintype.card (Fin (bonnetDepresApexCount k)) -
          Fintype.card {z : Fin (bonnetDepresApexCount k) // z = x} :=
    Fintype.card_subtype_compl
      (fun z : Fin (bonnetDepresApexCount k) => z = x)
  rw [hcompl, Fintype.card_subtype_eq, Fintype.card_fin]

/-- Exactly half of the root-child labels realize a prescribed bit at a fixed
apex vertex. -/
theorem card_apexBitFiber {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) (b : Bool) :
    Fintype.card (ApexBitFiber x b) =
      2 ^ (bonnetDepresApexCount k - 1) := by
  classical
  rw [Fintype.card_congr (apexBitFiberEquiv x b)]
  rw [Fintype.card_fun, Fintype.card_bool, card_otherApexVertex x]

/-- Separating bit vectors are equivalent to arbitrary choices on the remaining
apex vertices. -/
noncomputable def separatingApexBitsEquiv {k : ℕ}
    {x y : Fin (bonnetDepresApexCount k)} (hxy : x ≠ y) :
    SeparatingApexBits x y ≃ (RemainingApexVertex x y → Bool) where
  toFun f z := f.1 z.1
  invFun g :=
    ⟨fun z =>
      if hx : z = x then
        true
      else if hy : z = y then
        false
      else
        g ⟨z, hx, hy⟩,
      by simp,
      by simp [hxy.symm]⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext z
    by_cases hx : z = x
    · subst z
      simp [f.2.1]
    · by_cases hy : z = y
      · subst z
        simp [hx, f.2.2]
      · simp [hx, hy]
  right_inv := by
    intro g
    funext z
    rcases z with ⟨z, hz⟩
    simp [hz.1, hz.2]

/-- The number of remaining apex vertices after deleting two distinct ones. -/
theorem card_remainingApexVertex {k : ℕ}
    {x y : Fin (bonnetDepresApexCount k)} (hxy : x ≠ y) :
    Fintype.card (RemainingApexVertex x y) =
      bonnetDepresApexCount k - 2 := by
  classical
  calc
    Fintype.card {z : Fin (bonnetDepresApexCount k) // z ≠ x ∧ z ≠ y} =
        Fintype.card {z : Fin (bonnetDepresApexCount k) // ¬ (z = x ∨ z = y)} :=
      Fintype.card_congr <|
        Equiv.subtypeEquivRight fun z => by
          constructor
          · rintro ⟨hzx, hzy⟩ (rfl | rfl)
            · exact hzx rfl
            · exact hzy rfl
          · intro h
            exact ⟨fun hzx => h (Or.inl hzx), fun hzy => h (Or.inr hzy)⟩
    _ = bonnetDepresApexCount k - 2 := by
      have hcompl :
          Fintype.card
              {z : Fin (bonnetDepresApexCount k) // ¬ (z = x ∨ z = y)} =
            Fintype.card (Fin (bonnetDepresApexCount k)) -
              Fintype.card
                {z : Fin (bonnetDepresApexCount k) // z = x ∨ z = y} :=
        Fintype.card_subtype_compl
          (fun z : Fin (bonnetDepresApexCount k) => z = x ∨ z = y)
      rw [hcompl, Fintype.card_subtype_eq_or_eq_of_ne hxy, Fintype.card_fin]

/-- There are `2^(|X|-2)` root children separating two distinct apex vertices. -/
theorem card_separatingApexBits {k : ℕ}
    {x y : Fin (bonnetDepresApexCount k)} (hxy : x ≠ y) :
    Fintype.card (SeparatingApexBits x y) =
      2 ^ (bonnetDepresApexCount k - 2) := by
  classical
  rw [Fintype.card_congr (separatingApexBitsEquiv hxy)]
  rw [Fintype.card_fun, Fintype.card_bool, card_remainingApexVertex hxy]

/-- Root-child vertices whose apex neighborhoods contain `x` and omit `y`. -/
def separatingRootChildren {k : ℕ}
    (x y : Fin (bonnetDepresApexCount k)) :
    Finset (BonnetDepresVertex k) :=
  Finset.univ.image fun f : SeparatingApexBits x y =>
    (Sum.inr (rootChildWithNeighborhood k f.1) : BonnetDepresVertex k)

/-- The root children separating two distinct apex vertices are all distinct,
so their count is exactly `2^(|X|-2)`. -/
theorem card_separatingRootChildren {k : ℕ}
    {x y : Fin (bonnetDepresApexCount k)} (hxy : x ≠ y) :
    (separatingRootChildren x y).card =
      2 ^ (bonnetDepresApexCount k - 2) := by
  classical
  rw [separatingRootChildren, Finset.card_image_of_injective]
  · simp [card_separatingApexBits hxy]
  · intro f g h
    apply Subtype.ext
    exact rootChildWithNeighborhood_injective k (Sum.inr.inj h)

/-- Singleton bags of root children whose apex neighborhoods contain `x` and
omit `y`. -/
def separatingRootChildBags {k : ℕ}
    (x y : Fin (bonnetDepresApexCount k)) :
    Finset (Finset (BonnetDepresVertex k)) :=
  Finset.univ.image fun f : SeparatingApexBits x y =>
    ({Sum.inr (rootChildWithNeighborhood k f.1)} :
      Finset (BonnetDepresVertex k))

/-- A partition has kept every child of the root as a singleton bag.  This is
the condition used for the initial segment of the Bonnet--Déprés lower-bound
argument, before the first contraction involving a root child. -/
def RootChildrenSingleton {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k))) : Prop :=
  ∀ f : Fin (bonnetDepresApexCount k) → Bool,
    ({Sum.inr (rootChildWithNeighborhood k f)} :
      Finset (BonnetDepresVertex k)) ∈ P

/-- The singleton bag containing a root child with a prescribed apex
neighborhood. -/
def rootChildBag (k : ℕ) (f : Fin (bonnetDepresApexCount k) → Bool) :
    Finset (BonnetDepresVertex k) :=
  {Sum.inr (rootChildWithNeighborhood k f)}

theorem rootChildrenSingleton_iff {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))} :
    RootChildrenSingleton P ↔ ∀ f, rootChildBag k f ∈ P := by
  simp [RootChildrenSingleton, rootChildBag]

/-- Merging two bags that are not root-child singleton bags preserves the
`RootChildrenSingleton` invariant. -/
theorem rootChildrenSingleton_merge_of_not_rootChildBag {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A B : Finset (BonnetDepresVertex k)}
    (hroot : RootChildrenSingleton P)
    (hAnot : ∀ f : Fin (bonnetDepresApexCount k) → Bool, A ≠ rootChildBag k f)
    (hBnot : ∀ f : Fin (bonnetDepresApexCount k) → Bool, B ≠ rootChildBag k f) :
    RootChildrenSingleton
      (insert (A ∪ B) ((P.erase A).erase B)) := by
  intro f
  change rootChildBag k f ∈ insert (A ∪ B) ((P.erase A).erase B)
  rw [mem_merge_family_iff]
  right
  exact ⟨(rootChildrenSingleton_iff.mp hroot) f, (hAnot f).symm, (hBnot f).symm⟩

/-- The family of all singleton bags of root children. -/
def rootChildBags (k : ℕ) : Finset (Finset (BonnetDepresVertex k)) :=
  Finset.univ.image (rootChildBag k)

/-- Distinct apex-neighborhoods give distinct root-child singleton bags. -/
theorem rootChildBag_injective (k : ℕ) :
    Function.Injective (rootChildBag k) := by
  intro f g h
  apply rootChildWithNeighborhood_injective k
  exact Sum.inr.inj (Finset.singleton_inj.mp h)

@[simp] theorem card_rootChildBags (k : ℕ) :
    (rootChildBags k).card = bonnetDepresBranch k := by
  classical
  rw [rootChildBags, Finset.card_image_of_injective]
  · simp [bonnetDepresBranch]
  · exact rootChildBag_injective k

theorem rootChildBags_subset_of_rootChildrenSingleton {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    (hroot : RootChildrenSingleton P) :
    rootChildBags k ⊆ P := by
  classical
  intro B hB
  rw [rootChildBags, Finset.mem_image] at hB
  rcases hB with ⟨f, _hf, rfl⟩
  exact (rootChildrenSingleton_iff.mp hroot) f

theorem one_lt_bonnetDepresBranch (k : ℕ) :
    1 < bonnetDepresBranch k := by
  have hpow : 2 ^ 0 < 2 ^ bonnetDepresApexCount k := by
    apply Nat.pow_lt_pow_right
    · omega
    · unfold bonnetDepresApexCount
      omega
  simpa [bonnetDepresBranch] using hpow

/-- A bag family with at most one part cannot keep all root children as
singleton bags. -/
theorem not_rootChildrenSingleton_of_card_le_one {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    (hcard : P.card ≤ 1) :
    ¬ RootChildrenSingleton P := by
  intro hroot
  have hle : (rootChildBags k).card ≤ P.card :=
    Finset.card_le_card (rootChildBags_subset_of_rootChildrenSingleton hroot)
  rw [card_rootChildBags] at hle
  have hbranch := one_lt_bonnetDepresBranch k
  omega

/-- Singleton root-child bags whose labels have a prescribed bit at an apex. -/
def apexBitRootChildBags {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) (b : Bool) :
    Finset (Finset (BonnetDepresVertex k)) :=
  Finset.univ.image fun f : ApexBitFiber x b =>
    ({Sum.inr (rootChildWithNeighborhood k f.1)} :
      Finset (BonnetDepresVertex k))

/-- The root-child singleton bags with a prescribed apex bit are all distinct. -/
theorem card_apexBitRootChildBags {k : ℕ}
    (x : Fin (bonnetDepresApexCount k)) (b : Bool) :
    (apexBitRootChildBags x b).card =
      2 ^ (bonnetDepresApexCount k - 1) := by
  classical
  rw [apexBitRootChildBags, Finset.card_image_of_injective]
  · simp [card_apexBitFiber x b]
  · intro f g h
    apply Subtype.ext
    apply rootChildWithNeighborhood_injective k
    exact Sum.inr.inj (Finset.singleton_inj.mp h)

@[simp] theorem rootChildrenSingleton_singletonBags (k : ℕ) :
    RootChildrenSingleton
      (TrigraphState.singletonBags (BonnetDepresVertex k)) := by
  intro f
  exact Finset.mem_image.mpr ⟨Sum.inr (rootChildWithNeighborhood k f), by simp, rfl⟩

/-- The singleton root-child bags separating two distinct apex vertices are all
distinct. -/
theorem card_separatingRootChildBags {k : ℕ}
    {x y : Fin (bonnetDepresApexCount k)} (hxy : x ≠ y) :
    (separatingRootChildBags x y).card =
      2 ^ (bonnetDepresApexCount k - 2) := by
  classical
  rw [separatingRootChildBags, Finset.card_image_of_injective]
  · simp [card_separatingApexBits hxy]
  · intro f g h
    apply Subtype.ext
    apply rootChildWithNeighborhood_injective k
    exact Sum.inr.inj (Finset.singleton_inj.mp h)

@[simp] theorem apexAdj_child_labelOfNeighborhood {k : ℕ}
    (x : Fin (bonnetDepresApexCount k))
    (parent : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : parent.1.val < bonnetDepresDepth k)
    (f : Fin (bonnetDepresApexCount k) → Bool) :
    bonnetDepresApexAdj x
        (FullTreeNode.child parent hlevel (labelOfNeighborhood f)) ↔
      f x = true := by
  simpa using
    (bonnetDepresApexAdj_child x parent hlevel (labelOfNeighborhood f))

/-- The child of `u` whose apex neighborhood is exactly `{y}`. -/
def childWithSingletonApexNeighborhood {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k)
    (y : Fin (bonnetDepresApexCount k)) :
    FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
  FullTreeNode.child u hlevel
    (labelOfNeighborhood (singletonApexNeighborhood y))

@[simp] theorem apexAdj_childWithSingletonApexNeighborhood {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k)
    (x y : Fin (bonnetDepresApexCount k)) :
    bonnetDepresApexAdj x
        (childWithSingletonApexNeighborhood u hlevel y) ↔
      x = y := by
  rw [childWithSingletonApexNeighborhood, apexAdj_child_labelOfNeighborhood]
  simp [singletonApexNeighborhood]

/-- The children of an internal full-tree node. -/
def childSet {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :=
  Finset.univ.image (FullTreeNode.child u hlevel)

/-- The graph vertices corresponding to the children of an internal tree node. -/
def childVertexSet {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    Finset (BonnetDepresVertex k) :=
  (childSet u hlevel).image Sum.inr

@[simp] theorem mem_childSet {k : ℕ}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k} :
    w ∈ childSet u hlevel ↔
      ∃ label : Fin (bonnetDepresBranch k),
        FullTreeNode.child u hlevel label = w := by
  classical
  simp [childSet, eq_comm]

/-- Membership in a child set fixes the child's level. -/
theorem level_eq_succ_of_mem_childSet {k : ℕ}
    {u c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hc : c ∈ childSet u hlevel) :
    c.1.val = u.1.val + 1 := by
  rcases mem_childSet.mp hc with ⟨label, rfl⟩
  simp [FullTreeNode.child]

/-- A child-set member is also a descendant of its parent. -/
theorem isAncestor_of_mem_childSet {k : ℕ}
    {u c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hc : c ∈ childSet u hlevel) :
    IsTreeAncestor u c := by
  rcases mem_childSet.mp hc with ⟨label, rfl⟩
  exact isTreeAncestor_child u hlevel label

/-- Distinct siblings cannot both be ancestors of the same tree node. -/
theorem not_isTreeAncestor_of_distinct_siblings {k : ℕ}
    {u c₁ c₂ w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hc₁ : c₁ ∈ childSet u hlevel)
    (hc₂ : c₂ ∈ childSet u hlevel)
    (hcne : c₁ ≠ c₂)
    (h₁ : IsTreeAncestor c₁ w)
    (h₂ : IsTreeAncestor c₂ w) :
    False := by
  apply hcne
  exact eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq h₁ h₂
    ((level_eq_succ_of_mem_childSet hc₁).trans
      (level_eq_succ_of_mem_childSet hc₂).symm)

/-- Descendants of `q` whose tree vertices lie in the bag `A`. -/
noncomputable def descendantsInBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k))
    (q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) := by
  classical
  exact Finset.univ.filter fun z =>
    IsTreeAncestor q z ∧ (Sum.inr z : BonnetDepresVertex k) ∈ A

@[simp] theorem mem_descendantsInBag {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q z : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)} :
    z ∈ descendantsInBag A q ↔
      IsTreeAncestor q z ∧ (Sum.inr z : BonnetDepresVertex k) ∈ A := by
  classical
  simp [descendantsInBag]

theorem descendantsInBag_nonempty_of_mem {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q z : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hqz : IsTreeAncestor q z)
    (hzA : (Sum.inr z : BonnetDepresVertex k) ∈ A) :
    (descendantsInBag A q).Nonempty := by
  exact ⟨z, by rw [mem_descendantsInBag]; exact ⟨hqz, hzA⟩⟩

/-- `x` lies on the tree path from an ancestor `q` down to a descendant `z`.
Endpoints are included. -/
def OnTreePath {branch depth : ℕ}
    (q z x : FullTreeNode branch depth) : Prop :=
  IsTreeAncestor q x ∧ IsTreeAncestor x z

/-- Descendants of `q` in `B` whose whole path from `q` avoids the previously
chosen bags `F`.  This is the formal version of the `Q_i` path condition in
Claim 19. -/
noncomputable def availableDescendantsInBag {k : ℕ}
    (F : Finset (Finset (BonnetDepresVertex k)))
    (B : Finset (BonnetDepresVertex k))
    (q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) := by
  classical
  exact Finset.univ.filter fun z =>
    IsTreeAncestor q z ∧ (Sum.inr z : BonnetDepresVertex k) ∈ B ∧
      ∀ ⦃D⦄, D ∈ F → ∀ ⦃x⦄, OnTreePath q z x →
        (Sum.inr x : BonnetDepresVertex k) ∉ D

@[simp] theorem mem_availableDescendantsInBag {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q z : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)} :
    z ∈ availableDescendantsInBag F B q ↔
      IsTreeAncestor q z ∧ (Sum.inr z : BonnetDepresVertex k) ∈ B ∧
        ∀ ⦃D⦄, D ∈ F → ∀ ⦃x⦄, OnTreePath q z x →
          (Sum.inr x : BonnetDepresVertex k) ∉ D := by
  classical
  simp [availableDescendantsInBag]

theorem availableDescendantsInBag_nonempty_of_mem {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q z : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hqz : IsTreeAncestor q z)
    (hzB : (Sum.inr z : BonnetDepresVertex k) ∈ B)
    (havoid :
      ∀ ⦃D⦄, D ∈ F → ∀ ⦃x⦄, OnTreePath q z x →
        (Sum.inr x : BonnetDepresVertex k) ∉ D) :
    (availableDescendantsInBag F B q).Nonempty := by
  exact ⟨z, by rw [mem_availableDescendantsInBag]; exact ⟨hqz, hzB, havoid⟩⟩

/-- The highest, i.e. minimum-level, currently available descendant. -/
noncomputable def highestAvailableDescendantInBag {k : ℕ}
    (F : Finset (Finset (BonnetDepresVertex k)))
    (B : Finset (BonnetDepresVertex k))
    (q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (h : (availableDescendantsInBag F B q).Nonempty) :
    FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
  Classical.choose
    (Finset.exists_min_image (availableDescendantsInBag F B q) (fun z => z.1.val) h)

theorem highestAvailableDescendantInBag_spec {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (availableDescendantsInBag F B q).Nonempty) :
    highestAvailableDescendantInBag F B q h ∈ availableDescendantsInBag F B q ∧
      ∀ z ∈ availableDescendantsInBag F B q,
        (highestAvailableDescendantInBag F B q h).1.val ≤ z.1.val :=
  Classical.choose_spec
    (Finset.exists_min_image (availableDescendantsInBag F B q) (fun z => z.1.val) h)

theorem highestAvailableDescendantInBag_isAncestor {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (availableDescendantsInBag F B q).Nonempty) :
    IsTreeAncestor q (highestAvailableDescendantInBag F B q h) := by
  exact (mem_availableDescendantsInBag.mp
    (highestAvailableDescendantInBag_spec h).1).1

theorem highestAvailableDescendantInBag_mem_bag {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (availableDescendantsInBag F B q).Nonempty) :
    (Sum.inr (highestAvailableDescendantInBag F B q h) : BonnetDepresVertex k) ∈ B := by
  exact (mem_availableDescendantsInBag.mp
    (highestAvailableDescendantInBag_spec h).1).2.1

theorem highestAvailableDescendantInBag_path_avoids {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (availableDescendantsInBag F B q).Nonempty) :
    ∀ ⦃D⦄, D ∈ F → ∀ ⦃x⦄,
      OnTreePath q (highestAvailableDescendantInBag F B q h) x →
        (Sum.inr x : BonnetDepresVertex k) ∉ D := by
  exact (mem_availableDescendantsInBag.mp
    (highestAvailableDescendantInBag_spec h).1).2.2

theorem parent_notMem_bag_of_highestAvailableDescendant {k : ℕ}
    {F : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {q p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {h : (availableDescendantsInBag F B q).Nonempty}
    (hp : FullTreeNode.IsParent p (highestAvailableDescendantInBag F B q h))
    (hstrict : q.1.val < (highestAvailableDescendantInBag F B q h).1.val) :
    (Sum.inr p : BonnetDepresVertex k) ∉ B := by
  intro hpB
  have hqp : IsTreeAncestor q p :=
    isTreeAncestor_parent_of_strict_descendant
      (highestAvailableDescendantInBag_isAncestor h) hp hstrict
  have hpPath :
      OnTreePath q (highestAvailableDescendantInBag F B q h) p := by
    exact ⟨hqp, isTreeAncestor_of_isParent hp⟩
  have hpAvail : p ∈ availableDescendantsInBag F B q := by
    rw [mem_availableDescendantsInBag]
    refine ⟨hqp, hpB, ?_⟩
    intro D hD x hx
    exact highestAvailableDescendantInBag_path_avoids h hD
      ⟨hx.1, isTreeAncestor_trans hx.2 (isTreeAncestor_of_isParent hp)⟩
  have hmin := (highestAvailableDescendantInBag_spec h).2 p hpAvail
  have hpLevel : (highestAvailableDescendantInBag F B q h).1.val = p.1.val + 1 :=
    FullTreeNode.isParent_level hp
  omega

/-- The highest, i.e. minimum-level, descendant of `q` whose vertex lies in
`A`, assuming such a descendant exists. -/
noncomputable def highestDescendantInBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k))
    (q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (h : (descendantsInBag A q).Nonempty) :
    FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
  Classical.choose
    (Finset.exists_min_image (descendantsInBag A q) (fun z => z.1.val) h)

theorem highestDescendantInBag_spec {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (descendantsInBag A q).Nonempty) :
    highestDescendantInBag A q h ∈ descendantsInBag A q ∧
      ∀ z ∈ descendantsInBag A q,
        (highestDescendantInBag A q h).1.val ≤ z.1.val :=
  Classical.choose_spec
    (Finset.exists_min_image (descendantsInBag A q) (fun z => z.1.val) h)

theorem highestDescendantInBag_isAncestor {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (descendantsInBag A q).Nonempty) :
    IsTreeAncestor q (highestDescendantInBag A q h) := by
  exact (mem_descendantsInBag.mp (highestDescendantInBag_spec h).1).1

theorem highestDescendantInBag_mem_bag {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (h : (descendantsInBag A q).Nonempty) :
    (Sum.inr (highestDescendantInBag A q h) : BonnetDepresVertex k) ∈ A := by
  exact (mem_descendantsInBag.mp (highestDescendantInBag_spec h).1).2

/-- The parent of a strict highest descendant in a bag. -/
noncomputable def highestParentInBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k))
    (q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (h : (descendantsInBag A q).Nonempty)
    (hstrict : q.1.val < (highestDescendantInBag A q h).1.val) :
    FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
  FullTreeNode.parent (highestDescendantInBag A q h) (by omega)

theorem highestParentInBag_isParent {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {h : (descendantsInBag A q).Nonempty}
    {hstrict : q.1.val < (highestDescendantInBag A q h).1.val} :
    FullTreeNode.IsParent (highestParentInBag A q h hstrict)
      (highestDescendantInBag A q h) := by
  exact FullTreeNode.parent_isParent
    (highestDescendantInBag A q h) (by omega)

theorem highestParentInBag_isAncestor {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {h : (descendantsInBag A q).Nonempty}
    {hstrict : q.1.val < (highestDescendantInBag A q h).1.val} :
    IsTreeAncestor q (highestParentInBag A q h hstrict) :=
  isTreeAncestor_parent_of_strict_descendant
    (highestDescendantInBag_isAncestor h)
    highestParentInBag_isParent hstrict

theorem highestParentInBag_level_lt_highestDescendant {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {h : (descendantsInBag A q).Nonempty}
    {hstrict : q.1.val < (highestDescendantInBag A q h).1.val} :
    (highestParentInBag A q h hstrict).1.val <
      (highestDescendantInBag A q h).1.val := by
  have hlevel :=
    FullTreeNode.isParent_level
      (highestParentInBag_isParent (A := A) (q := q) (h := h) (hstrict := hstrict))
  omega

/-- The parent of a strict highest descendant cannot already lie in the bag;
otherwise it would be a higher descendant in that bag. -/
theorem parent_notMem_bag_of_highestDescendant {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {q p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {h : (descendantsInBag A q).Nonempty}
    (hp : FullTreeNode.IsParent p (highestDescendantInBag A q h))
    (hstrict : q.1.val < (highestDescendantInBag A q h).1.val) :
    (Sum.inr p : BonnetDepresVertex k) ∉ A := by
  intro hpA
  have hqp : IsTreeAncestor q p :=
    isTreeAncestor_parent_of_strict_descendant
      (highestDescendantInBag_isAncestor h) hp hstrict
  have hpCandidate : p ∈ descendantsInBag A q := by
    rw [mem_descendantsInBag]
    exact ⟨hqp, hpA⟩
  have hmin := (highestDescendantInBag_spec h).2 p hpCandidate
  have hpLevel : (highestDescendantInBag A q h).1.val = p.1.val + 1 :=
    FullTreeNode.isParent_level hp
  omega

@[simp] theorem card_childSet {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    (childSet u hlevel).card = bonnetDepresBranch k := by
  classical
  rw [childSet, Finset.card_image_of_injective]
  · simp
  · exact child_injective_label u hlevel

@[simp] theorem card_childVertexSet {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    (childVertexSet u hlevel).card = bonnetDepresBranch k := by
  classical
  rw [childVertexSet, Finset.card_image_of_injective]
  · exact card_childSet u hlevel
  · intro a b h
    exact Sum.inr.inj h

/-- Distinct children of one tree node differ on adjacency to at least one apex. -/
theorem exists_apexAdj_disagree_of_distinct_children {k : ℕ}
    {u c₁ c₂ : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hc₁ : c₁ ∈ childSet u hlevel)
    (hc₂ : c₂ ∈ childSet u hlevel)
    (hcne : c₁ ≠ c₂) :
    ∃ x : Fin (bonnetDepresApexCount k),
      (bonnetDepresApexAdj x c₁ ∧ ¬ bonnetDepresApexAdj x c₂) ∨
        (bonnetDepresApexAdj x c₂ ∧ ¬ bonnetDepresApexAdj x c₁) := by
  rcases mem_childSet.mp hc₁ with ⟨label₁, rfl⟩
  rcases mem_childSet.mp hc₂ with ⟨label₂, rfl⟩
  have hlabel_ne : label₁ ≠ label₂ := by
    intro hlabel
    exact hcne (by simp [hlabel])
  rcases exists_bit_ne_of_fin_pow_ne
      (n := bonnetDepresApexCount k) (a := label₁) (b := label₂)
      (by simpa [bonnetDepresBranch] using hlabel_ne) with
    ⟨x, hxbit⟩
  by_cases h₁ : label₁.val.testBit x.val = true
  · have h₂ : label₂.val.testBit x.val = false := by
      cases h₂bit : label₂.val.testBit x.val <;> simp [h₁, h₂bit] at hxbit ⊢
    refine ⟨x, Or.inl ⟨?_, ?_⟩⟩
    · rw [bonnetDepresApexAdj_child x u hlevel label₁]
      exact h₁
    · intro hAdj
      rw [bonnetDepresApexAdj_child x u hlevel label₂] at hAdj
      simp [h₂] at hAdj
  · have h₁f : label₁.val.testBit x.val = false := by
      cases h₁bit : label₁.val.testBit x.val
      · rfl
      · exact (h₁ h₁bit).elim
    have h₂ : label₂.val.testBit x.val = true := by
      cases h₂bit : label₂.val.testBit x.val <;> simp [h₁f, h₂bit] at hxbit ⊢
    refine ⟨x, Or.inr ⟨?_, ?_⟩⟩
    · rw [bonnetDepresApexAdj_child x u hlevel label₂]
      exact h₂
    · intro hAdj
      rw [bonnetDepresApexAdj_child x u hlevel label₁] at hAdj
      simp [h₁f] at hAdj

/-- If a bag contains two tree vertices that disagree on an apex, then it is
red-adjacent to the singleton bag of that apex. -/
theorem partitionRedAdj_of_apexAdj_disagree_in_bag {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    {c₁ c₂ : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hc₁A : (Sum.inr c₁ : BonnetDepresVertex k) ∈ A)
    (hc₂A : (Sum.inr c₂ : BonnetDepresVertex k) ∈ A)
    (hadj₁ : bonnetDepresApexAdj x c₁)
    (hnot₂ : ¬ bonnetDepresApexAdj x c₂) :
    partitionRedAdj (bonnetDepresGraph k) A
      ({Sum.inl x} : Finset (BonnetDepresVertex k)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro hAeq
    have hc₁Singleton :
        (Sum.inr c₁ : BonnetDepresVertex k) ∈
          ({Sum.inl x} : Finset (BonnetDepresVertex k)) := by
      rw [hAeq] at hc₁A
      exact hc₁A
    simp at hc₁Singleton
  · intro hhom
    rcases hhom with hcomp | hemp
    · have hGraph :
          (bonnetDepresGraph k).Adj
            (Sum.inr c₂ : BonnetDepresVertex k) (Sum.inl x) :=
        hcomp hc₂A (by simp)
      have hAdj : bonnetDepresApexAdj x c₂ := by
        simpa [bonnetDepresGraph] using hGraph
      exact hnot₂ hAdj
    · have hGraph :
          (bonnetDepresGraph k).Adj
            (Sum.inr c₁ : BonnetDepresVertex k) (Sum.inl x) := by
        simpa [bonnetDepresGraph] using hadj₁
      exact hemp hc₁A (by simp) hGraph

/-- Two distinct children of one node in the same bag force some apex singleton
to be red-adjacent to that bag. -/
theorem exists_apex_partitionRedAdj_of_distinct_children_in_bag {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {u c₁ c₂ : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hc₁child : c₁ ∈ childSet u hlevel)
    (hc₂child : c₂ ∈ childSet u hlevel)
    (hcne : c₁ ≠ c₂)
    (hc₁A : (Sum.inr c₁ : BonnetDepresVertex k) ∈ A)
    (hc₂A : (Sum.inr c₂ : BonnetDepresVertex k) ∈ A) :
    ∃ x : Fin (bonnetDepresApexCount k),
      partitionRedAdj (bonnetDepresGraph k) A
        ({Sum.inl x} : Finset (BonnetDepresVertex k)) := by
  rcases exists_apexAdj_disagree_of_distinct_children
      hc₁child hc₂child hcne with
    ⟨x, hdisagree | hdisagree⟩
  · exact ⟨x,
      partitionRedAdj_of_apexAdj_disagree_in_bag
        hc₁A hc₂A hdisagree.1 hdisagree.2⟩
  · exact ⟨x,
      partitionRedAdj_of_apexAdj_disagree_in_bag
        hc₂A hc₁A hdisagree.1 hdisagree.2⟩

/-- Apex coordinates on which a set of siblings realizes both adjacency values. -/
noncomputable def childApexVariationSet {k : ℕ}
    (S : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))) :
    Finset (Fin (bonnetDepresApexCount k)) := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ c₁ ∈ S, ∃ c₂ ∈ S,
      (bonnetDepresApexAdj x c₁ ∧ ¬ bonnetDepresApexAdj x c₂) ∨
        (bonnetDepresApexAdj x c₂ ∧ ¬ bonnetDepresApexAdj x c₁)

/-- A sibling set is encoded injectively by its values on the coordinates where
the set actually varies. -/
theorem card_le_pow_childApexVariationSet_card {k : ℕ}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    {S : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hS : S ⊆ childSet u hlevel) :
    S.card ≤ 2 ^ (childApexVariationSet S).card := by
  classical
  let code :
      {c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) // c ∈ S} →
        ({x : Fin (bonnetDepresApexCount k) // x ∈ childApexVariationSet S} → Bool) :=
    fun c x => decide (bonnetDepresApexAdj x.1 c.1)
  have hcode_inj : Function.Injective code := by
    intro c₁ c₂ hcode
    by_contra hne
    have hc₁child : c₁.1 ∈ childSet u hlevel := hS c₁.2
    have hc₂child : c₂.1 ∈ childSet u hlevel := hS c₂.2
    rcases exists_apexAdj_disagree_of_distinct_children
        hc₁child hc₂child (by intro h; exact hne (Subtype.ext h)) with
      ⟨x, hdisagree | hdisagree⟩
    · have hx :
          x ∈ childApexVariationSet S := by
        rw [childApexVariationSet, Finset.mem_filter]
        exact ⟨by simp, c₁.1, c₁.2, c₂.1, c₂.2, Or.inl hdisagree⟩
      have hbit := congrFun hcode ⟨x, hx⟩
      simp [code, hdisagree.1, hdisagree.2] at hbit
    · have hx :
          x ∈ childApexVariationSet S := by
        rw [childApexVariationSet, Finset.mem_filter]
        exact ⟨by simp, c₁.1, c₁.2, c₂.1, c₂.2, Or.inr hdisagree⟩
      have hbit := congrFun hcode ⟨x, hx⟩
      simp [code, hdisagree.1, hdisagree.2] at hbit
  calc
    S.card = Fintype.card
        {c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) // c ∈ S} := by
      simp
    _ ≤ Fintype.card
        ({x : Fin (bonnetDepresApexCount k) // x ∈ childApexVariationSet S} → Bool) :=
      Fintype.card_le_of_injective code hcode_inj
    _ = 2 ^ (childApexVariationSet S).card := by
      rw [Fintype.card_fun]
      simp [Fintype.card_bool]

/-- A set of at least `2^(k+1)` siblings varies on at least `k+1` apex
coordinates. -/
theorem le_childApexVariationSet_card_of_many_children {k : ℕ}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    {S : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hS : S ⊆ childSet u hlevel)
    (hmany : 2 ^ (k + 1) ≤ S.card) :
    k + 1 ≤ (childApexVariationSet S).card := by
  have hpow :
      2 ^ (k + 1) ≤ 2 ^ (childApexVariationSet S).card := by
    exact hmany.trans (card_le_pow_childApexVariationSet_card hS)
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow

/-- A tree node is not one of its own children. -/
theorem parent_notMem_childVertexSet {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    (Sum.inr u : BonnetDepresVertex k) ∉ childVertexSet u hlevel := by
  classical
  intro hmem
  rw [childVertexSet, Finset.mem_image] at hmem
  rcases hmem with ⟨c, hc, hcu⟩
  have hc_eq : c = u := Sum.inr.inj hcu
  rcases mem_childSet.mp hc with ⟨label, rfl⟩
  have hlevel_eq :
      (FullTreeNode.child u hlevel label).1.val = u.1.val := by
    exact congrArg (fun z => z.1.val) hc_eq
  simp [FullTreeNode.child] at hlevel_eq

/-- Adding the singleton parent vertex to a bag does not change its intersection
with the child set of that parent. -/
theorem singleton_parent_union_inter_childVertexSet {k : ℕ}
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k)
    (B : Finset (BonnetDepresVertex k)) :
    (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B) ∩
        childVertexSet u hlevel =
      B ∩ childVertexSet u hlevel := by
  classical
  ext v
  rw [Finset.mem_inter, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hv | hv, hvchild⟩
    · rw [Finset.mem_singleton] at hv
      subst v
      exact (parent_notMem_childVertexSet u hlevel hvchild).elim
    · exact ⟨hv, hvchild⟩
  · rintro ⟨hvB, hvchild⟩
    exact ⟨Or.inr hvB, hvchild⟩

/-- Children of `u` whose graph vertices lie in a specified bag. -/
noncomputable def childrenInBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k))
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) := by
  classical
  exact (childSet u hlevel).filter fun c => (Sum.inr c : BonnetDepresVertex k) ∈ A

@[simp] theorem mem_childrenInBag {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {u c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k} :
    c ∈ childrenInBag A u hlevel ↔
      c ∈ childSet u hlevel ∧ (Sum.inr c : BonnetDepresVertex k) ∈ A := by
  classical
  simp [childrenInBag]

/-- Counting children in a bag agrees with counting child vertices in that bag. -/
theorem card_childrenInBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k))
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    (childrenInBag A u hlevel).card =
      (A ∩ childVertexSet u hlevel).card := by
  classical
  have himage :
      (childrenInBag A u hlevel).image
          (Sum.inr : _ → BonnetDepresVertex k) =
        A ∩ childVertexSet u hlevel := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_image] at hv
      rcases hv with ⟨c, hc, rfl⟩
      rw [Finset.mem_inter]
      exact ⟨(mem_childrenInBag.mp hc).2,
        by
          rw [childVertexSet, Finset.mem_image]
          exact ⟨c, (mem_childrenInBag.mp hc).1, rfl⟩⟩
    · intro hv
      rw [Finset.mem_inter] at hv
      rw [childVertexSet, Finset.mem_image] at hv
      rcases hv with ⟨hvA, c, hc, rfl⟩
      rw [Finset.mem_image]
      exact ⟨c, mem_childrenInBag.mpr ⟨hc, hvA⟩, rfl⟩
  rw [← himage, Finset.card_image_of_injective]
  intro a b h
  exact Sum.inr.inj h

/-- Children of `u` that are adjacent to `w` in the full tree. -/
noncomputable def childAdjSet {k : ℕ}
    (u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) := by
  classical
  exact (childSet u hlevel).filter
    fun c =>
      (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w c

/-- A tree vertex distinct from `u` is adjacent to at most one child of `u`. -/
theorem card_childAdjSet_le_one {k : ℕ}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : u.1.val < bonnetDepresDepth k) (hwu : w ≠ u) :
    (childAdjSet u w hlevel).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have ha' :
      a ∈ (childSet u hlevel).filter
        (fun c =>
          (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w c) := by
    simpa [childAdjSet] using ha
  have hb' :
      b ∈ (childSet u hlevel).filter
        (fun c =>
          (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w c) := by
    simpa [childAdjSet] using hb
  rw [Finset.mem_filter] at ha' hb'
  rcases ha' with ⟨ha_child, ha_adj⟩
  rcases hb' with ⟨hb_child, hb_adj⟩
  rcases mem_childSet.mp ha_child with ⟨la, rfl⟩
  rcases mem_childSet.mp hb_child with ⟨lb, rfl⟩
  have hua :
      FullTreeNode.IsParent u (FullTreeNode.child u hlevel la) :=
    FullTreeNode.isParent_child u hlevel la
  have hub :
      FullTreeNode.IsParent u (FullTreeNode.child u hlevel lb) :=
    FullTreeNode.isParent_child u hlevel lb
  have hpa :
      FullTreeNode.IsParent (FullTreeNode.child u hlevel la) w := by
    rcases ha_adj with h | h
    · have hwu_eq : w = u := FullTreeNode.isParent_unique h hua
      exact (hwu hwu_eq).elim
    · exact h
  have hpb :
      FullTreeNode.IsParent (FullTreeNode.child u hlevel lb) w := by
    rcases hb_adj with h | h
    · have hwu_eq : w = u := FullTreeNode.isParent_unique h hub
      exact (hwu hwu_eq).elim
    · exact h
  exact FullTreeNode.isParent_unique hpa hpb

/-- Children of `u` that are not adjacent to `w`, viewed as vertices of the
Bonnet--Déprés graph. -/
noncomputable def childNonAdjVertexSet {k : ℕ}
    (u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) :
    Finset (BonnetDepresVertex k) :=
  childVertexSet u hlevel \ (childAdjSet u w hlevel).image Sum.inr

/-- Membership in the non-adjacent child set is exactly child membership plus
non-adjacency to the witness vertex. -/
theorem mem_childNonAdjVertexSet {k : ℕ}
    {u w c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : u.1.val < bonnetDepresDepth k) :
    (Sum.inr c : BonnetDepresVertex k) ∈ childNonAdjVertexSet u w hlevel ↔
      c ∈ childSet u hlevel ∧
        ¬ (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w c := by
  classical
  constructor
  · intro hv
    rw [childNonAdjVertexSet, Finset.mem_sdiff] at hv
    rcases hv with ⟨hchildv, hnotbad⟩
    rw [childVertexSet, Finset.mem_image] at hchildv
    rcases hchildv with ⟨c', hc', hc'eq⟩
    have hc_eq : c' = c := Sum.inr.inj hc'eq
    subst c'
    refine ⟨hc', ?_⟩
    intro hadj
    apply hnotbad
    rw [Finset.mem_image]
    refine ⟨c, ?_, rfl⟩
    have hfilter :
        c ∈ (childSet u hlevel).filter
          (fun z =>
            (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w z) := by
      rw [Finset.mem_filter]
      exact ⟨hc', hadj⟩
    simpa [childAdjSet] using hfilter
  · rintro ⟨hcchild, hnotadj⟩
    rw [childNonAdjVertexSet, Finset.mem_sdiff]
    constructor
    · rw [childVertexSet, Finset.mem_image]
      exact ⟨c, hcchild, rfl⟩
    · intro hbad
      rw [Finset.mem_image] at hbad
      rcases hbad with ⟨c', hc', hc'eq⟩
      have hc_eq : c' = c := Sum.inr.inj hc'eq
      subst c'
      have hfilter :
          c ∈ (childSet u hlevel).filter
            (fun z =>
              (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w z) := by
        simpa [childAdjSet] using hc'
      rw [Finset.mem_filter] at hfilter
      exact hnotadj hfilter.2

/-- All but at most one child of `u` are non-adjacent to a fixed tree vertex
`w ≠ u`. -/
theorem card_childNonAdjVertexSet_ge {k : ℕ}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : u.1.val < bonnetDepresDepth k) (hwu : w ≠ u) :
    bonnetDepresBranch k - 1 ≤ (childNonAdjVertexSet u w hlevel).card := by
  classical
  have hsubset :
      (childAdjSet u w hlevel).image Sum.inr ⊆ childVertexSet u hlevel := by
    intro v hv
    rw [Finset.mem_image] at hv
    rcases hv with ⟨c, hc, rfl⟩
    have hc_child : c ∈ childSet u hlevel := by
      have hc' :
          c ∈ (childSet u hlevel).filter
            (fun z =>
              (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w z) := by
        simpa [childAdjSet] using hc
      rw [Finset.mem_filter] at hc'
      exact hc'.1
    rw [childVertexSet, Finset.mem_image]
    exact ⟨c, hc_child, rfl⟩
  have hcard :
      (childNonAdjVertexSet u w hlevel).card =
        (childVertexSet u hlevel).card -
          ((childAdjSet u w hlevel).image
            (Sum.inr : _ → BonnetDepresVertex k)).card := by
    rw [childNonAdjVertexSet, Finset.card_sdiff_of_subset hsubset]
  have hbad :
      ((childAdjSet u w hlevel).image (Sum.inr : _ → BonnetDepresVertex k)).card ≤ 1 := by
    rw [Finset.card_image_of_injective]
    · exact card_childAdjSet_le_one hlevel hwu
    · intro a b h
      exact Sum.inr.inj h
  rw [hcard, card_childVertexSet]
  omega

/-- `P(v,H)` from the paper, with an explicit threshold: at least `m`
children of `u` lie in one current part. -/
def HasManyChildrenInPart {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k)))
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) (m : ℕ) : Prop :=
  ∃ A ∈ P, m ≤ (A ∩ childVertexSet u hlevel).card

/-- A node has many children that themselves satisfy `HasManyChildrenInPart`.
This is the formal Claim-16 conclusion. -/
def HasManyPChildren {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k)))
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hlevel : u.1.val < bonnetDepresDepth k) (m : ℕ) : Prop :=
  ∃ S : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
    S ⊆ childSet u hlevel ∧ m ≤ S.card ∧
      ∀ ⦃c⦄, c ∈ S →
        ∃ hc : c.1.val < bonnetDepresDepth k,
          HasManyChildrenInPart P c hc m

/-- The threshold used for property `P` in the specialized lower-bound proof. -/
def manyChildrenThreshold (k : ℕ) : ℕ :=
  2 ^ (k + 1)

theorem two_le_manyChildrenThreshold (k : ℕ) :
    2 ≤ manyChildrenThreshold k := by
  unfold manyChildrenThreshold
  have hpow : 2 ^ 1 ≤ 2 ^ (k + 1) := by
    apply Nat.pow_le_pow_right
    · omega
    · omega
  simpa using hpow

theorem manyChildrenThreshold_pos (k : ℕ) :
    0 < manyChildrenThreshold k := by
  exact (Nat.zero_lt_two.trans_le (two_le_manyChildrenThreshold k))

/-- The number of side branches forced into a single large bag in the final
pigeonhole step of the lower-bound proof. -/
def manySideBranchesThreshold (k : ℕ) : ℕ :=
  2 ^ ((k + 1) * (2 + 2 ^ (k + 2) * (manyChildrenThreshold k + 1)))

/-- The number of non-singleton internal-tree parts that contradicts the
large-bag red-degree upper bound. -/
def manyInternalBagsThreshold (k : ℕ) : ℕ :=
  1 + 2 ^ (k + 2) * (manyChildrenThreshold k + 1)

/-- The depth of the Bonnet--Déprés tree is tuned to pigeonhole the
Claim-18 side branches among at most `2^(k+2)` large bags. -/
theorem depth_sub_two_eq_largeBagBound_mul_manySideBranchesThreshold (k : ℕ) :
    bonnetDepresDepth k - 2 =
      2 ^ (k + 2) * manySideBranchesThreshold k := by
  simp [bonnetDepresDepth, manySideBranchesThreshold, manyChildrenThreshold]

theorem manySideBranchesThreshold_eq_manyChildrenThreshold_pow (k : ℕ) :
    manySideBranchesThreshold k =
      (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k + 1) := by
  rw [manySideBranchesThreshold, manyChildrenThreshold, manyInternalBagsThreshold]
  rw [pow_mul]
  congr 1
  simp [manyChildrenThreshold]
  omega

theorem redBound_mul_manyChildrenThreshold_pow_lt_succ {k d r : ℕ}
    (hd : d ≤ 2 ^ k) :
    d * (manyChildrenThreshold k) ^ r <
      (manyChildrenThreshold k) ^ (r + 1) := by
  have hd_lt : d < manyChildrenThreshold k := by
    unfold manyChildrenThreshold
    have hpow : 2 ^ k < 2 ^ (k + 1) := by
      exact Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega : k < k + 1)
    exact lt_of_le_of_lt hd hpow
  have hpos : 0 < (manyChildrenThreshold k) ^ r :=
    pow_pos (manyChildrenThreshold_pos k) r
  calc
    d * (manyChildrenThreshold k) ^ r
        < manyChildrenThreshold k * (manyChildrenThreshold k) ^ r :=
          Nat.mul_lt_mul_of_pos_right hd_lt hpos
    _ = (manyChildrenThreshold k) ^ (r + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]

/-- A bag is large when it contains at least the threshold number of children of
one internal tree node.  This is the set `B` from the paper, phrased at the
partition level. -/
def IsLargeChildBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k)) : Prop :=
  ∃ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
    ∃ hlevel : u.1.val < bonnetDepresDepth k,
      manyChildrenThreshold k ≤ (A ∩ childVertexSet u hlevel).card

/-- The family of large child bags in a partition. -/
noncomputable def largeChildBags {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k))) :
    Finset (Finset (BonnetDepresVertex k)) := by
  classical
  exact P.filter IsLargeChildBag

@[simp] theorem mem_largeChildBags {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)} :
    A ∈ largeChildBags P ↔ A ∈ P ∧ IsLargeChildBag A := by
  classical
  simp [largeChildBags]

/-- A witness to property `P` is exactly a member of the large-child-bag family. -/
theorem exists_largeChildBag_of_hasManyChildrenInPart {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hP : HasManyChildrenInPart P u hlevel (manyChildrenThreshold k)) :
    ∃ A ∈ largeChildBags P,
      manyChildrenThreshold k ≤ (A ∩ childVertexSet u hlevel).card := by
  classical
  rcases hP with ⟨A, hA, hmany⟩
  refine ⟨A, ?_, hmany⟩
  rw [mem_largeChildBags]
  exact ⟨hA, u, hlevel, hmany⟩

/-- A large child-count witness contains at least one actual child vertex. -/
theorem exists_child_mem_bag_of_manyChildren {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hmany : manyChildrenThreshold k ≤ (A ∩ childVertexSet u hlevel).card) :
    ∃ c ∈ childSet u hlevel, (Sum.inr c : BonnetDepresVertex k) ∈ A := by
  classical
  have hpos : 0 < (A ∩ childVertexSet u hlevel).card :=
    (manyChildrenThreshold_pos k).trans_le hmany
  rcases Finset.card_pos.mp hpos with ⟨z, hz⟩
  rw [Finset.mem_inter] at hz
  rw [childVertexSet, Finset.mem_image] at hz
  rcases hz.2 with ⟨c, hc, rfl⟩
  exact ⟨c, hc, hz.1⟩

/-- The apex coordinates whose singleton bags are red-adjacent to `A`. -/
noncomputable def apexRedCoordinatesOfBag {k : ℕ}
    (A : Finset (BonnetDepresVertex k)) :
    Finset (Fin (bonnetDepresApexCount k)) := by
  classical
  exact Finset.univ.filter fun x =>
    partitionRedAdj (bonnetDepresGraph k) A
      ({Sum.inl x} : Finset (BonnetDepresVertex k))

/-- Large bags that are red-adjacent to a fixed apex singleton. -/
noncomputable def largeChildBagsRedAdjacentToApex {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k)))
    (x : Fin (bonnetDepresApexCount k)) :
    Finset (Finset (BonnetDepresVertex k)) := by
  classical
  exact (largeChildBags P).filter fun A =>
    partitionRedAdj (bonnetDepresGraph k) A
      ({Sum.inl x} : Finset (BonnetDepresVertex k))

/-- Incidences between large child bags and apex coordinates witnessing red
adjacency. -/
noncomputable def largeChildBagApexIncidences {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k))) :
    Finset (Finset (BonnetDepresVertex k) × Fin (bonnetDepresApexCount k)) := by
  classical
  exact ((largeChildBags P).product Finset.univ).filter fun pair =>
    partitionRedAdj (bonnetDepresGraph k) pair.1
      ({Sum.inl pair.2} : Finset (BonnetDepresVertex k))

/-- A large child bag is red-adjacent to at least `k+1` apex singleton bags:
`2^(k+1)` distinct sibling labels need at least `k+1` varying apex bits. -/
theorem le_card_apexRedCoordinatesOfBag_of_isLargeChildBag {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    (hlarge : IsLargeChildBag A) :
    k + 1 ≤ (apexRedCoordinatesOfBag A).card := by
  classical
  rcases hlarge with ⟨u, hlevel, hmany⟩
  let S := childrenInBag A u hlevel
  have hSsubset : S ⊆ childSet u hlevel := by
    intro c hc
    exact (mem_childrenInBag.mp hc).1
  have hSA :
      ∀ ⦃c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)⦄,
        c ∈ S → (Sum.inr c : BonnetDepresVertex k) ∈ A := by
    intro c hc
    exact (mem_childrenInBag.mp hc).2
  have hmanyS : 2 ^ (k + 1) ≤ S.card := by
    simpa [S, manyChildrenThreshold, card_childrenInBag] using hmany
  have hvarLower :
      k + 1 ≤ (childApexVariationSet S).card :=
    le_childApexVariationSet_card_of_many_children hSsubset hmanyS
  have hvarSubset :
      childApexVariationSet S ⊆ apexRedCoordinatesOfBag A := by
    intro x hx
    rw [apexRedCoordinatesOfBag, Finset.mem_filter]
    refine ⟨by simp, ?_⟩
    rw [childApexVariationSet, Finset.mem_filter] at hx
    rcases hx.2 with ⟨c₁, hc₁, c₂, hc₂, hdisagree | hdisagree⟩
    · exact partitionRedAdj_of_apexAdj_disagree_in_bag
        (hSA hc₁) (hSA hc₂) hdisagree.1 hdisagree.2
    · exact partitionRedAdj_of_apexAdj_disagree_in_bag
        (hSA hc₂) (hSA hc₁) hdisagree.1 hdisagree.2
  exact hvarLower.trans (Finset.card_le_card hvarSubset)

/-- Fuelled form of the paper's property `Q`.

At a preleaf it is just property `P`; otherwise two distinct children must
satisfy `Q` at one lower fuel.  The public `QProperty` below supplies enough
fuel from the node height. -/
def QPropertyAtFuel {k : ℕ} :
    ℕ →
      Finset (Finset (BonnetDepresVertex k)) →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) → Prop
  | 0, _P, _u => False
  | fuel + 1, P, u =>
      (IsPreleaf u ∧
        ∃ hlevel : IsInternal u,
          HasManyChildrenInPart P u hlevel (manyChildrenThreshold k)) ∨
      (¬ IsPreleaf u ∧
        ∃ hlevel : IsInternal u,
          ∃ c₁ ∈ childSet u hlevel, ∃ c₂ ∈ childSet u hlevel,
            c₁ ≠ c₂ ∧ QPropertyAtFuel fuel P c₁ ∧ QPropertyAtFuel fuel P c₂)

/-- The paper's property `Q`, with fuel equal to the remaining tree height. -/
def QProperty {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k)))
    (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) : Prop :=
  QPropertyAtFuel (bonnetDepresDepth k - u.1.val) P u

/-- Property `P` is monotone under one bag contraction. -/
theorem hasManyChildrenInPart_mono_of_isBagContraction {k m : ℕ}
    {P Q : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hPQ : IsBagContraction P Q)
    (hP : HasManyChildrenInPart P u hlevel m) :
    HasManyChildrenInPart Q u hlevel m := by
  classical
  rcases hP with ⟨C, hC, hcard⟩
  rcases hPQ with ⟨A, hA, B, hB, hAB, rfl⟩
  by_cases hCA : C = A
  · refine ⟨A ∪ B, ?_, ?_⟩
    · exact Finset.mem_insert_self _ _
    · have hsubset :
          C ∩ childVertexSet u hlevel ⊆
            (A ∪ B) ∩ childVertexSet u hlevel := by
        intro v hv
        rw [Finset.mem_inter] at hv ⊢
        exact ⟨Finset.mem_union_left _ (by simpa [hCA] using hv.1), hv.2⟩
      exact hcard.trans (Finset.card_le_card hsubset)
  · by_cases hCB : C = B
    · refine ⟨A ∪ B, ?_, ?_⟩
      · exact Finset.mem_insert_self _ _
      · have hsubset :
            C ∩ childVertexSet u hlevel ⊆
              (A ∪ B) ∩ childVertexSet u hlevel := by
          intro v hv
          rw [Finset.mem_inter] at hv ⊢
          exact ⟨Finset.mem_union_right _ (by simpa [hCB] using hv.1), hv.2⟩
        exact hcard.trans (Finset.card_le_card hsubset)
    · refine ⟨C, ?_, hcard⟩
      rw [mem_merge_family_iff]
      exact Or.inr ⟨hC, hCA, hCB⟩

/-- Fuelled `Q` is monotone under one bag contraction. -/
theorem qPropertyAtFuel_mono_of_isBagContraction {k : ℕ}
    {P Q : Finset (Finset (BonnetDepresVertex k))}
    (hPQ : IsBagContraction P Q) :
    ∀ fuel : ℕ,
      ∀ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        QPropertyAtFuel fuel P u → QPropertyAtFuel fuel Q u := by
  intro fuel
  induction fuel with
  | zero =>
      intro u h
      exact h.elim
  | succ fuel ih =>
      intro u hq
      rcases hq with ⟨hpre, hP⟩ | ⟨hnotpre, hchildren⟩
      · left
        rcases hP with ⟨hlevel, hP⟩
        exact ⟨hpre, hlevel,
          hasManyChildrenInPart_mono_of_isBagContraction hPQ hP⟩
      · right
        rcases hchildren with ⟨hlevel, c₁, hc₁, c₂, hc₂, hcne, hq₁, hq₂⟩
        exact ⟨hnotpre, hlevel, c₁, hc₁, c₂, hc₂, hcne,
          ih c₁ hq₁, ih c₂ hq₂⟩

/-- Property `Q` is monotone under one bag contraction. -/
theorem qProperty_mono_of_isBagContraction {k : ℕ}
    {P Q : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hPQ : IsBagContraction P Q)
    (hQ : QProperty P u) :
    QProperty Q u :=
  qPropertyAtFuel_mono_of_isBagContraction hPQ
    (bonnetDepresDepth k - u.1.val) u hQ

/-- A fuelled `Q` witness contains a preleaf node satisfying property `P`. -/
theorem exists_preleaf_hasManyChildrenInPart_of_qPropertyAtFuel {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))} :
    ∀ fuel : ℕ,
      ∀ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        QPropertyAtFuel fuel P u →
          ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            ∃ hlevel : IsInternal v,
              IsPreleaf v ∧
                HasManyChildrenInPart P v hlevel (manyChildrenThreshold k) := by
  intro fuel
  induction fuel with
  | zero =>
      intro u hq
      exact hq.elim
  | succ fuel ih =>
      intro u hq
      rcases hq with ⟨hpre, hP⟩ | ⟨_hnotpre, hchildren⟩
      · rcases hP with ⟨hlevel, hP⟩
        exact ⟨u, hlevel, hpre, hP⟩
      · rcases hchildren with ⟨_hlevel, c₁, _hc₁, _c₂, _hc₂, _hcne, hq₁, _hq₂⟩
        exact ih c₁ hq₁

/-- Descendant-carrying version of
`exists_preleaf_hasManyChildrenInPart_of_qPropertyAtFuel`. -/
theorem exists_preleaf_descendant_hasManyChildrenInPart_of_qPropertyAtFuel {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))} :
    ∀ fuel : ℕ,
      ∀ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        QPropertyAtFuel fuel P u →
          ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            IsTreeAncestor u v ∧
              IsPreleaf v ∧
                ∃ hlevel : IsInternal v,
                  HasManyChildrenInPart P v hlevel (manyChildrenThreshold k) := by
  intro fuel
  induction fuel with
  | zero =>
      intro u hq
      exact hq.elim
  | succ fuel ih =>
      intro u hq
      rcases hq with ⟨hpre, hP⟩ | ⟨_hnotpre, hchildren⟩
      · rcases hP with ⟨hlevel, hP⟩
        exact ⟨u, isTreeAncestor_refl u, hpre, hlevel, hP⟩
      · rcases hchildren with ⟨hlevel, c₁, hc₁, _c₂, _hc₂, _hcne, hq₁, _hq₂⟩
        rcases ih c₁ hq₁ with ⟨v, hcv, hpre, hvlevel, hP⟩
        exact ⟨v, isTreeAncestor_trans (isAncestor_of_mem_childSet hc₁) hcv,
          hpre, hvlevel, hP⟩

/-- A `Q` witness contains a preleaf node satisfying property `P`. -/
theorem exists_preleaf_hasManyChildrenInPart_of_qProperty {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ : QProperty P u) :
    ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
      ∃ hlevel : IsInternal v,
        IsPreleaf v ∧
          HasManyChildrenInPart P v hlevel (manyChildrenThreshold k) :=
  exists_preleaf_hasManyChildrenInPart_of_qPropertyAtFuel
    (bonnetDepresDepth k - u.1.val) u hQ

/-- A `Q` witness contains a descendant preleaf satisfying property `P`. -/
theorem exists_preleaf_descendant_hasManyChildrenInPart_of_qProperty {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ : QProperty P u) :
    ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
      IsTreeAncestor u v ∧
        IsPreleaf v ∧
          ∃ hlevel : IsInternal v,
            HasManyChildrenInPart P v hlevel (manyChildrenThreshold k) :=
  exists_preleaf_descendant_hasManyChildrenInPart_of_qPropertyAtFuel
    (bonnetDepresDepth k - u.1.val) u hQ

/-- A singleton-bag partition cannot contain two children of the same parent in a
single part, hence cannot satisfy property `P` at threshold at least two. -/
theorem not_hasManyChildrenInPart_singletonBags {k m : ℕ}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hm : 2 ≤ m) :
    ¬ HasManyChildrenInPart
      (TrigraphState.singletonBags (BonnetDepresVertex k)) u hlevel m := by
  classical
  rintro ⟨A, hA, hcard⟩
  rcases Finset.mem_image.mp hA with ⟨v, _hv, rfl⟩
  have hle :
      (({v} : Finset (BonnetDepresVertex k)) ∩ childVertexSet u hlevel).card ≤ 1 := by
    calc
      (({v} : Finset (BonnetDepresVertex k)) ∩ childVertexSet u hlevel).card
          ≤ ({v} : Finset (BonnetDepresVertex k)).card := by
        exact Finset.card_le_card (by intro z hz; exact (Finset.mem_inter.mp hz).1)
      _ = 1 := by simp
  omega

/-- No root child satisfies `Q` in the initial singleton-bag state. -/
theorem not_rootChildQAt_singletonBags {k : ℕ} :
    ¬ ∃ f : Fin (bonnetDepresApexCount k) → Bool,
      QProperty (TrigraphState.singletonBags (BonnetDepresVertex k))
        (rootChildWithNeighborhood k f) := by
  rintro ⟨f, hQ⟩
  rcases exists_preleaf_hasManyChildrenInPart_of_qProperty hQ with
    ⟨v, hlevel, _hpre, hP⟩
  exact not_hasManyChildrenInPart_singletonBags (two_le_manyChildrenThreshold k) hP

/-- At a preleaf, property `P` immediately gives property `Q`. -/
theorem qProperty_of_hasManyChildrenInPart_preleaf {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hpre : IsPreleaf u)
    (hlevel : IsInternal u)
    (hP : HasManyChildrenInPart P u hlevel (manyChildrenThreshold k)) :
    QProperty P u := by
  unfold QProperty
  have hfuel : bonnetDepresDepth k - u.1.val = 1 := by
    unfold IsPreleaf at hpre
    omega
  rw [hfuel]
  left
  exact ⟨hpre, hlevel, hP⟩

/-- Membership in a child set gives the corresponding tree-parent relation. -/
theorem isParent_of_mem_childSet {k : ℕ}
    {u c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hc : c ∈ childSet u hlevel) :
    FullTreeNode.IsParent u c := by
  rcases mem_childSet.mp hc with ⟨label, rfl⟩
  exact FullTreeNode.isParent_child u hlevel label

/-- Non-preleaf constructor for property `Q`. -/
theorem qProperty_of_two_child_qProperties {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {u c₁ c₂ : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hnonpreleaf : IsNonPreleafInternal u)
    (hc₁ : c₁ ∈ childSet u hlevel)
    (hc₂ : c₂ ∈ childSet u hlevel)
    (hcne : c₁ ≠ c₂)
    (hq₁ : QProperty P c₁)
    (hq₂ : QProperty P c₂) :
    QProperty P u := by
  unfold QProperty at hq₁ hq₂ ⊢
  have hnonpreleaf_raw : u.1.val + 1 < bonnetDepresDepth k := by
    simpa [IsNonPreleafInternal] using hnonpreleaf
  have hnotpre : ¬ IsPreleaf u := by
    intro hpre
    unfold IsPreleaf at hpre
    omega
  have hfuel :
      bonnetDepresDepth k - u.1.val =
        (bonnetDepresDepth k - (u.1.val + 1)) + 1 := by
    omega
  have hc₁level := level_eq_succ_of_mem_childSet hc₁
  have hc₂level := level_eq_succ_of_mem_childSet hc₂
  have hfuel₁ :
      bonnetDepresDepth k - c₁.1.val =
        bonnetDepresDepth k - (u.1.val + 1) := by
    rw [hc₁level]
  have hfuel₂ :
      bonnetDepresDepth k - c₂.1.val =
        bonnetDepresDepth k - (u.1.val + 1) := by
    rw [hc₂level]
  rw [hfuel]
  right
  refine ⟨hnotpre, hlevel, c₁, hc₁, c₂, hc₂, hcne, ?_, ?_⟩
  · simpa [hfuel₁] using hq₁
  · simpa [hfuel₂] using hq₂

/-- Non-preleaf destructor for property `Q`. -/
theorem exists_two_child_qProperties_of_qProperty_nonpreleaf {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hnonpreleaf : IsNonPreleafInternal u)
    (hQ : QProperty P u) :
    ∃ hlevel : IsInternal u,
      ∃ c₁ ∈ childSet u hlevel, ∃ c₂ ∈ childSet u hlevel,
        c₁ ≠ c₂ ∧ QProperty P c₁ ∧ QProperty P c₂ := by
  unfold QProperty at hQ
  have hnotpre : ¬ IsPreleaf u := by
    intro hpre
    unfold IsNonPreleafInternal at hnonpreleaf
    unfold IsPreleaf at hpre
    omega
  have hfuel :
      bonnetDepresDepth k - u.1.val =
        (bonnetDepresDepth k - (u.1.val + 1)) + 1 := by
    unfold IsNonPreleafInternal at hnonpreleaf
    omega
  rw [hfuel] at hQ
  rcases hQ with hpre | hchildren
  · exact (hnotpre hpre.1).elim
  · rcases hchildren with
      ⟨_hnotpre, hlevel, c₁, hc₁, c₂, hc₂, hcne, hq₁, hq₂⟩
    refine ⟨hlevel, c₁, hc₁, c₂, hc₂, hcne, ?_, ?_⟩
    · have hc₁level := level_eq_succ_of_mem_childSet hc₁
      simpa [QProperty, hc₁level] using hq₁
    · have hc₂level := level_eq_succ_of_mem_childSet hc₂
      simpa [QProperty, hc₂level] using hq₂

/-- The arithmetic gap used in the Claim-14 pigeonhole step. -/
theorem manyChildren_product_lt_branch_sub_one (k : ℕ) :
    (2 ^ k + 1) * (manyChildrenThreshold k - 1) <
      bonnetDepresBranch k - 1 := by
  have hfactor : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
    rw [pow_succ]
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    omega
  have hthreshold : manyChildrenThreshold k - 1 < 2 ^ (k + 1) := by
    unfold manyChildrenThreshold
    have hpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
    omega
  have hprod :
      (2 ^ k + 1) * (manyChildrenThreshold k - 1) <
        2 ^ (k + 1) * 2 ^ (k + 1) := by
    have hprod_le :
        (2 ^ k + 1) * (manyChildrenThreshold k - 1) ≤
          2 ^ (k + 1) * (manyChildrenThreshold k - 1) :=
      Nat.mul_le_mul_right _ hfactor
    have hprod_lt :
        2 ^ (k + 1) * (manyChildrenThreshold k - 1) <
          2 ^ (k + 1) * 2 ^ (k + 1) :=
      Nat.mul_lt_mul_of_pos_left hthreshold (Nat.two_pow_pos (k + 1))
    exact hprod_le.trans_lt hprod_lt
  have hpowmul :
      2 ^ (k + 1) * 2 ^ (k + 1) = 2 ^ (2 * k + 2) := by
    rw [← pow_add]
    congr 1
    omega
  have htail :
      2 ^ (2 * k + 2) < bonnetDepresBranch k - 1 := by
    unfold bonnetDepresBranch bonnetDepresApexCount
    have hone : 1 < 2 ^ (2 * k + 2) := by
      have hpow : 2 ^ 0 < 2 ^ (2 * k + 2) := by
        apply Nat.pow_lt_pow_right
        · omega
        · omega
      simpa only [pow_zero] using hpow
    have hexp : 2 * k + 3 = 2 * k + 2 + 1 := by omega
    have htarget : 2 ^ (2 * k + 2) + 1 < 2 ^ (2 * k + 3) := by
      have hright : 2 ^ (2 * k + 3) = 2 ^ (2 * k + 2) * 2 := by
        rw [hexp, pow_succ]
      rw [hright, mul_two]
      omega
    exact Nat.lt_sub_iff_add_lt.mpr htarget
  have hprod' :
      (2 ^ k + 1) * (manyChildrenThreshold k - 1) <
        2 ^ (2 * k + 2) := by
    simpa [hpowmul] using hprod
  exact hprod'.trans htail

/-- If a bag contains two tree vertices `u,w`, and another bag contains a tree
vertex adjacent to `u` but not adjacent to `w`, then the two bags are
red-adjacent. -/
theorem partitionRedAdj_of_tree_edge_tree_nonedge {k : ℕ}
    {A B : Finset (BonnetDepresVertex k)}
    {u w c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hAB : A ≠ B)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hwA : (Sum.inr w : BonnetDepresVertex k) ∈ A)
    (hcB : (Sum.inr c : BonnetDepresVertex k) ∈ B)
    (huc :
      (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj u c)
    (hwc :
      ¬ (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w c) :
    partitionRedAdj (bonnetDepresGraph k) A B := by
  refine ⟨hAB, ?_⟩
  intro hhom
  rcases hhom with hcomp | hemp
  · have hwcGraph :
        (bonnetDepresGraph k).Adj
          (Sum.inr w : BonnetDepresVertex k) (Sum.inr c) :=
      hcomp hwA hcB
    exact hwc (by simpa [bonnetDepresGraph] using hwcGraph)
  · have hucGraph :
        (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k) (Sum.inr c) := by
      simpa [bonnetDepresGraph] using huc
    exact hemp huA hcB hucGraph

/-- A child of `u` non-adjacent to another tree vertex `w` forces red adjacency
from a bag containing `u,w` to any different bag containing that child. -/
theorem partitionRedAdj_of_parent_child_nonadj_witness {k : ℕ}
    {A B : Finset (BonnetDepresVertex k)}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : u.1.val < bonnetDepresDepth k)
    {label : Fin (bonnetDepresBranch k)}
    (hAB : A ≠ B)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hwA : (Sum.inr w : BonnetDepresVertex k) ∈ A)
    (hcB :
      (Sum.inr (FullTreeNode.child u hlevel label) : BonnetDepresVertex k) ∈ B)
    (hwc :
      ¬ (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj
        w (FullTreeNode.child u hlevel label)) :
    partitionRedAdj (bonnetDepresGraph k) A B :=
  partitionRedAdj_of_tree_edge_tree_nonedge hAB huA hwA hcB
    (Or.inl (FullTreeNode.isParent_child u hlevel label)) hwc

/-- The bag `A` together with all red-neighbor bags of `A` in a partition. -/
noncomputable def redOrSelfBags {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k)))
    (A : Finset (BonnetDepresVertex k)) :
    Finset (Finset (BonnetDepresVertex k)) := by
  classical
  exact insert A (P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B)

/-- The union of the bag `A` and all its red-neighbor bags. -/
noncomputable def redOrSelfUnion {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k)))
    (A : Finset (BonnetDepresVertex k)) :
    Finset (BonnetDepresVertex k) :=
  (redOrSelfBags P A).biUnion id

/-- Red-degree control bounds the number of bags in `redOrSelfBags`. -/
theorem card_redOrSelfBags_le {k d : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P) :
    (redOrSelfBags P A).card ≤ d + 1 := by
  classical
  have hneighbors :
      (P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B).card ≤ d :=
    hred hA
  calc
    (redOrSelfBags P A).card
        ≤ (P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B).card + 1 := by
          simpa [redOrSelfBags] using
            Finset.card_insert_le A
              (P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B)
    _ ≤ d + 1 := by omega

/-- `redOrSelfBags` really is a subfamily of the ambient partition when `A` is
itself a part. -/
theorem redOrSelfBags_subset_partition {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    (hA : A ∈ P) :
    redOrSelfBags P A ⊆ P := by
  classical
  intro B hB
  rw [redOrSelfBags, Finset.mem_insert, Finset.mem_filter] at hB
  rcases hB with hBA | hB
  · simpa [hBA]
  · exact hB.1

/-- Non-adjacent children are, in particular, children of the parent. -/
theorem childNonAdjVertexSet_subset_childVertexSet {k : ℕ}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : u.1.val < bonnetDepresDepth k) :
    childNonAdjVertexSet u w hlevel ⊆ childVertexSet u hlevel := by
  classical
  intro v hv
  have hv_sdiff :
      v ∈ childVertexSet u hlevel \
        (childAdjSet u w hlevel).image (Sum.inr : _ → BonnetDepresVertex k) := by
    simpa [childNonAdjVertexSet] using hv
  rw [Finset.mem_sdiff] at hv_sdiff
  exact hv_sdiff.1

/-- If every selected bag contains at most `m` relevant vertices, their union
contains at most `number of bags * m` relevant vertices. -/
theorem card_inter_redOrSelfUnion_le_mul {k m : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {X : Finset (BonnetDepresVertex k)}
    (hsmall : ∀ ⦃B⦄, B ∈ redOrSelfBags P A → (B ∩ X).card ≤ m) :
    (redOrSelfUnion P A ∩ X).card ≤ (redOrSelfBags P A).card * m := by
  classical
  rw [redOrSelfUnion, Finset.biUnion_inter]
  calc
    ((redOrSelfBags P A).biUnion fun B => B ∩ X).card
        ≤ ∑ B ∈ redOrSelfBags P A, (B ∩ X).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ B ∈ redOrSelfBags P A, m := by
      exact Finset.sum_le_sum fun B hB => hsmall hB
    _ = (redOrSelfBags P A).card * m := by
      simp [Finset.sum_const, Nat.mul_comm]

/-- Every non-adjacent child of `u` is in `A` or in a red-neighbor bag of `A`,
provided `A` contains both `u` and the witness tree vertex `w`. -/
theorem childNonAdjVertexSet_subset_redOrSelfUnion {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hpart : IsBagPartition P)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hwA : (Sum.inr w : BonnetDepresVertex k) ∈ A)
    (hlevel : u.1.val < bonnetDepresDepth k) :
    childNonAdjVertexSet u w hlevel ⊆ redOrSelfUnion P A := by
  classical
  intro v hv
  rw [redOrSelfUnion, Finset.mem_biUnion]
  have hv_child : v ∈ childVertexSet u hlevel := by
    have hv_sdiff :
        v ∈ childVertexSet u hlevel \
          (childAdjSet u w hlevel).image (Sum.inr : _ → BonnetDepresVertex k) := by
      simpa [childNonAdjVertexSet] using hv
    rw [Finset.mem_sdiff] at hv_sdiff
    exact hv_sdiff.1
  rw [childVertexSet, Finset.mem_image] at hv_child
  rcases hv_child with ⟨c, hc_child, rfl⟩
  have hnonadj :
      ¬ (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj w c :=
    (mem_childNonAdjVertexSet (k := k) (u := u) (w := w) (c := c) hlevel).mp hv |>.2
  rcases hpart.2.2 (Sum.inr c : BonnetDepresVertex k) with ⟨B, hB, hcB⟩
  by_cases hBA : B = A
  · refine ⟨A, ?_, ?_⟩
    · simp [redOrSelfBags]
    · simpa [hBA] using hcB
  · refine ⟨B, ?_, hcB⟩
    rw [redOrSelfBags, Finset.mem_insert, Finset.mem_filter]
    right
    refine ⟨hB, ?_⟩
    rcases mem_childSet.mp hc_child with ⟨label, rfl⟩
    exact partitionRedAdj_of_parent_child_nonadj_witness hlevel
      (by intro hAB; exact hBA hAB.symm) huA hwA hcB hnonadj

/-- Claim-14 core: under red-degree at most `2^k`, a part containing two
distinct tree vertices forces many children of the first one into a single part.

The proof follows the paper's counting argument.  A second tree vertex `w` in
the same part is non-adjacent to all but one child of `u`; every such child lies
either in the same part or in a red-neighbor part.  Since there are at most
`2^k + 1` such parts and the branching factor is much larger than
`(2^k + 1) * (2^(k+1)-1)`, one part contains at least `2^(k+1)` children. -/
theorem hasManyChildrenInPart_of_two_tree_vertices_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hwA : (Sum.inr w : BonnetDepresVertex k) ∈ A)
    (hwu : w ≠ u)
    (hlevel : u.1.val < bonnetDepresDepth k) :
    HasManyChildrenInPart P u hlevel (manyChildrenThreshold k) := by
  classical
  by_contra hnot
  let X : Finset (BonnetDepresVertex k) := childNonAdjVertexSet u w hlevel
  have hthreshold_pos : 0 < manyChildrenThreshold k := by
    unfold manyChildrenThreshold
    exact Nat.two_pow_pos (k + 1)
  have hsmallP :
      ∀ ⦃B : Finset (BonnetDepresVertex k)⦄, B ∈ P →
        (B ∩ childVertexSet u hlevel).card ≤ manyChildrenThreshold k - 1 := by
    intro B hB
    have hlt : (B ∩ childVertexSet u hlevel).card < manyChildrenThreshold k := by
      exact Nat.lt_of_not_ge fun hlarge => hnot ⟨B, hB, hlarge⟩
    omega
  have hsmall :
      ∀ ⦃B : Finset (BonnetDepresVertex k)⦄, B ∈ redOrSelfBags P A →
        (B ∩ X).card ≤ manyChildrenThreshold k - 1 := by
    intro B hB
    have hBP : B ∈ P := redOrSelfBags_subset_partition hA hB
    have hchildSmall := hsmallP hBP
    have hsubset : B ∩ X ⊆ B ∩ childVertexSet u hlevel := by
      intro v hv
      rw [Finset.mem_inter] at hv ⊢
      exact ⟨hv.1, childNonAdjVertexSet_subset_childVertexSet hlevel hv.2⟩
    exact (Finset.card_le_card hsubset).trans hchildSmall
  have hcover : X ⊆ redOrSelfUnion P A := by
    simpa [X] using
      childNonAdjVertexSet_subset_redOrSelfUnion
        (P := P) (A := A) (u := u) (w := w) hpart huA hwA hlevel
  have hXeq : redOrSelfUnion P A ∩ X = X := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_inter] at hv
      exact hv.2
    · intro hv
      rw [Finset.mem_inter]
      exact ⟨hcover hv, hv⟩
  have hupper₁ :
      X.card ≤ (redOrSelfBags P A).card * (manyChildrenThreshold k - 1) := by
    rw [← hXeq]
    exact card_inter_redOrSelfUnion_le_mul hsmall
  have hupper₂ :
      X.card ≤ (d + 1) * (manyChildrenThreshold k - 1) := by
    exact hupper₁.trans
      (Nat.mul_le_mul_right _ (card_redOrSelfBags_le hred hA))
  have hupper :
      X.card ≤ (2 ^ k + 1) * (manyChildrenThreshold k - 1) := by
    exact hupper₂.trans (Nat.mul_le_mul_right _ (by omega))
  have hlower :
      bonnetDepresBranch k - 1 ≤ X.card := by
    simpa [X] using card_childNonAdjVertexSet_ge hlevel hwu
  have hgap := manyChildren_product_lt_branch_sub_one k
  omega

/-- If a different part contains many children of `u`, then a part containing
`u` and a distinct tree vertex `w` is red-adjacent to it. -/
theorem partitionRedAdj_of_many_children_and_two_tree_vertices
    {k : ℕ} {A C : Finset (BonnetDepresVertex k)}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hAC : A ≠ C)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hwA : (Sum.inr w : BonnetDepresVertex k) ∈ A)
    (hwu : w ≠ u)
    (hlevel : u.1.val < bonnetDepresDepth k)
    (hmany : manyChildrenThreshold k ≤ (C ∩ childVertexSet u hlevel).card) :
    partitionRedAdj (bonnetDepresGraph k) A C := by
  classical
  have htwo : 2 ≤ (C ∩ childVertexSet u hlevel).card :=
    (two_le_manyChildrenThreshold k).trans hmany
  have hbadCard :
      ((childAdjSet u w hlevel).image
        (Sum.inr : _ → BonnetDepresVertex k)).card ≤ 1 := by
    rw [Finset.card_image_of_injective]
    · exact card_childAdjSet_le_one hlevel hwu
    · intro a b hab
      exact Sum.inr.inj hab
  have hexists :
      ∃ z,
        z ∈ C ∩ childVertexSet u hlevel ∧
          z ∉ (childAdjSet u w hlevel).image
            (Sum.inr : _ → BonnetDepresVertex k) := by
    by_contra hnone
    have hsubset :
        C ∩ childVertexSet u hlevel ⊆
          (childAdjSet u w hlevel).image
            (Sum.inr : _ → BonnetDepresVertex k) := by
      intro z hz
      by_contra hznot
      exact hnone ⟨z, hz, hznot⟩
    have hcard_le_one :
        (C ∩ childVertexSet u hlevel).card ≤ 1 :=
      (Finset.card_le_card hsubset).trans hbadCard
    omega
  rcases hexists with ⟨z, hz, hznotAdjImage⟩
  rw [Finset.mem_inter] at hz
  rw [childVertexSet, Finset.mem_image] at hz
  rcases hz.2 with ⟨c, hc_child, rfl⟩
  have hnonadj :
      ¬ (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj
        w c := by
    intro hadj
    have hcAdj : c ∈ childAdjSet u w hlevel := by
      rw [childAdjSet, Finset.mem_filter]
      exact ⟨hc_child, hadj⟩
    exact hznotAdjImage (by
      rw [Finset.mem_image]
      exact ⟨c, hcAdj, rfl⟩)
  rcases mem_childSet.mp hc_child with ⟨label, rfl⟩
  exact partitionRedAdj_of_parent_child_nonadj_witness
    hlevel hAC huA hwA hz.1 hnonadj

/-- If one bag contains strict descendants of two incomparable side branches
and another bag contains the parent of one selected descendant, then the two
bags are red-adjacent. -/
theorem partitionRedAdj_of_antichain_descendant_parent_parts
    {k : ℕ} {B C : Finset (BonnetDepresVertex k)}
    {a b za zb p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hBC : B ≠ C)
    (hanti : ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (haza : IsTreeAncestor a za)
    (hbzb : IsTreeAncestor b zb)
    (hpza : FullTreeNode.IsParent p za)
    (ha_strict : a.1.val < za.1.val)
    (hzaB : (Sum.inr za : BonnetDepresVertex k) ∈ B)
    (hzbB : (Sum.inr zb : BonnetDepresVertex k) ∈ B)
    (hpC : (Sum.inr p : BonnetDepresVertex k) ∈ C) :
    partitionRedAdj (bonnetDepresGraph k) C B := by
  apply partitionRedAdj_symm
  refine partitionRedAdj_of_tree_edge_tree_nonedge
    (k := k) (A := B) (B := C) (u := za) (w := zb) (c := p)
    hBC hzaB hzbB hpC ?_ ?_
  · exact Or.inr hpza
  · intro hAdj
    exact not_tree_adj_parent_descendant_of_antichain
      hanti haza hbzb hpza ha_strict
      ((FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).symm hAdj)

/-- Family form of the previous red-adjacency lemma: when `B` contains selected
descendants of more than one branch in an antichain, the part containing the
parent of any strict selected descendant is red-adjacent to `B`. -/
theorem partitionRedAdj_of_antichain_family_parent_part
    {k : ℕ}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B C : Finset (BonnetDepresVertex k)}
    {a p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (haR : a ∈ R)
    (hRcard : 1 < R.card)
    (hanti :
      ∀ ⦃x⦄, x ∈ R → ∀ ⦃y⦄, y ∈ R → x ≠ y →
        ¬ IsTreeAncestor x y ∧ ¬ IsTreeAncestor y x)
    (zOf :
      ∀ r : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        r ∈ R → FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hdesc :
      ∀ r hr, IsTreeAncestor r (zOf r hr))
    (hBz :
      ∀ r hr, (Sum.inr (zOf r hr) : BonnetDepresVertex k) ∈ B)
    (hpza : FullTreeNode.IsParent p (zOf a haR))
    (ha_strict : a.1.val < (zOf a haR).1.val)
    (hBC : B ≠ C)
    (hpC : (Sum.inr p : BonnetDepresVertex k) ∈ C) :
    partitionRedAdj (bonnetDepresGraph k) C B := by
  classical
  rcases Finset.one_lt_card.mp hRcard with ⟨x, hx, y, hy, hxy⟩
  obtain ⟨b, hbR, hba⟩ : ∃ b ∈ R, b ≠ a := by
    by_cases hxa : x = a
    · exact ⟨y, hy, by
        intro hya
        exact hxy (hxa.trans hya.symm)⟩
    · exact ⟨x, hx, hxa⟩
  exact partitionRedAdj_of_antichain_descendant_parent_parts
    (k := k) (B := B) (C := C) (a := a) (b := b)
    (za := zOf a haR) (zb := zOf b hbR) (p := p)
    hBC (hanti haR hbR (fun hab => hba hab.symm)) (hdesc a haR) (hdesc b hbR)
    hpza ha_strict (hBz a haR) (hBz b hbR) hpC

/-- Ranked family form of the red-adjacency step.  Unlike
`partitionRedAdj_of_antichain_family_parent_part`, this version does not assume
that the selected descendant of `a` is strict; the pairwise level distinction
rules out the sibling obstruction in that boundary case. -/
theorem partitionRedAdj_of_ranked_antichain_family_parent_part
    {k : ℕ}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B C : Finset (BonnetDepresVertex k)}
    {a p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (haR : a ∈ R)
    (hRcard : 1 < R.card)
    (hanti :
      ∀ ⦃x⦄, x ∈ R → ∀ ⦃y⦄, y ∈ R → x ≠ y →
        ¬ IsTreeAncestor x y ∧ ¬ IsTreeAncestor y x)
    (hlevel_ne :
      ∀ ⦃x⦄, x ∈ R → ∀ ⦃y⦄, y ∈ R → x ≠ y → x.1.val ≠ y.1.val)
    (zOf :
      ∀ r : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        r ∈ R → FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))
    (hdesc :
      ∀ r hr, IsTreeAncestor r (zOf r hr))
    (hBz :
      ∀ r hr, (Sum.inr (zOf r hr) : BonnetDepresVertex k) ∈ B)
    (hpza : FullTreeNode.IsParent p (zOf a haR))
    (hBC : B ≠ C)
    (hpC : (Sum.inr p : BonnetDepresVertex k) ∈ C) :
    partitionRedAdj (bonnetDepresGraph k) C B := by
  classical
  rcases Finset.one_lt_card.mp hRcard with ⟨x, hx, y, hy, hxy⟩
  obtain ⟨b, hbR, hba⟩ : ∃ b ∈ R, b ≠ a := by
    by_cases hxa : x = a
    · exact ⟨y, hy, by
        intro hya
        exact hxy (hxa.trans hya.symm)⟩
    · exact ⟨x, hx, hxa⟩
  apply partitionRedAdj_symm
  refine partitionRedAdj_of_tree_edge_tree_nonedge
    (k := k) (A := B) (B := C) (u := zOf a haR) (w := zOf b hbR) (c := p)
    hBC (hBz a haR) (hBz b hbR) hpC ?_ ?_
  · exact Or.inr hpza
  · intro hAdj
    exact not_tree_adj_parent_descendant_of_ranked_antichain
      (hanti haR hbR (fun hab => hba hab.symm))
      (hlevel_ne haR hbR (fun hab => hba hab.symm))
      (hdesc a haR) (hdesc b hbR) hpza
      ((FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).symm hAdj)

/-- A child whose label separates two apex vertices is red-adjacent to any bag
containing both apices. -/
theorem partitionRedAdj_of_apex_pair_child_disagree {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {parent : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : parent.1.val < bonnetDepresDepth k)
    {label : Fin (bonnetDepresBranch k)}
    {x y : Fin (bonnetDepresApexCount k)}
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hyA : (Sum.inl y : BonnetDepresVertex k) ∈ A)
    (hx : label.val.testBit x.val = true)
    (hy : label.val.testBit y.val = false) :
    partitionRedAdj (bonnetDepresGraph k) A
      {Sum.inr (FullTreeNode.child parent hlevel label)} := by
  classical
  refine ⟨?_, ?_⟩
  · intro hAeq
    simp [hAeq] at hxA
  · intro hhom
    rcases hhom with hcomp | hemp
    · have hyAdj :
        (bonnetDepresGraph k).Adj
          (Sum.inl y : BonnetDepresVertex k)
          (Sum.inr (FullTreeNode.child parent hlevel label)) :=
        hcomp hyA (by simp)
      have hyAdj' :
          bonnetDepresApexAdj y
            (FullTreeNode.child parent hlevel label) := by
        simpa [bonnetDepresGraph] using hyAdj
      rw [bonnetDepresApexAdj_child y parent hlevel label] at hyAdj'
      simp [hy] at hyAdj'
    · have hxAdj :
          bonnetDepresApexAdj x
            (FullTreeNode.child parent hlevel label) := by
        rw [bonnetDepresApexAdj_child x parent hlevel label]
        exact hx
      have hxGraph :
          (bonnetDepresGraph k).Adj
            (Sum.inl x : BonnetDepresVertex k)
            (Sum.inr (FullTreeNode.child parent hlevel label)) := by
        simpa [bonnetDepresGraph] using hxAdj
      exact hemp hxA (by simp) hxGraph

/-- A prescribed apex-neighborhood child separating two apex vertices is
red-adjacent to any bag containing both apices. -/
theorem partitionRedAdj_of_apex_pair_child_neighborhood_disagree {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {parent : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : parent.1.val < bonnetDepresDepth k)
    {x y : Fin (bonnetDepresApexCount k)}
    {f : Fin (bonnetDepresApexCount k) → Bool}
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hyA : (Sum.inl y : BonnetDepresVertex k) ∈ A)
    (hx : f x = true) (hy : f y = false) :
    partitionRedAdj (bonnetDepresGraph k) A
      {Sum.inr (FullTreeNode.child parent hlevel (labelOfNeighborhood f))} := by
  exact partitionRedAdj_of_apex_pair_child_disagree
    (k := k) (A := A) (parent := parent) hlevel hxA hyA
    (by simp [hx]) (by simp [hy])

/-- Every root child separating two apex vertices is red-adjacent to a bag that
contains both apices. -/
theorem partitionRedAdj_of_apex_pair_separatingRootChild {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {x y : Fin (bonnetDepresApexCount k)}
    (f : SeparatingApexBits x y)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hyA : (Sum.inl y : BonnetDepresVertex k) ∈ A) :
    partitionRedAdj (bonnetDepresGraph k) A
      {Sum.inr (rootChildWithNeighborhood k f.1)} := by
  simpa [rootChildWithNeighborhood] using
    partitionRedAdj_of_apex_pair_child_neighborhood_disagree
      (k := k) (A := A)
      (parent := FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
      (root_level_lt_depth k)
      (x := x) (y := y) (f := f.1) hxA hyA f.2.1 f.2.2

/-- If all root children separating two apices remain singleton bags in a
partition, then a bag containing both apices has at least `2^(|X|-2)` red
neighbors. -/
theorem pow_apexCount_sub_two_le_of_apex_pair_redDegreeAtMost
    {k : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {x y : Fin (bonnetDepresApexCount k)}
    {d : ℕ}
    (hxy : x ≠ y)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : SeparatingApexBits x y,
        ({Sum.inr (rootChildWithNeighborhood k f.1)} :
          Finset (BonnetDepresVertex k)) ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hyA : (Sum.inl y : BonnetDepresVertex k) ∈ A) :
    2 ^ (bonnetDepresApexCount k - 2) ≤ d := by
  classical
  have hsubset :
      separatingRootChildBags x y ⊆
        P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B := by
    intro B hB
    rw [separatingRootChildBags, Finset.mem_image] at hB
    rcases hB with ⟨f, _hf, rfl⟩
    simp [hchildren f,
      partitionRedAdj_of_apex_pair_separatingRootChild f hxA hyA]
  have hcard := Finset.card_le_card hsubset
  rw [card_separatingRootChildBags hxy] at hcard
  exact hcard.trans (hred hA)

/-- In the specialized construction, the root-child family separating two
apices is already larger than `2^k`. -/
theorem pow_k_lt_pow_apexCount_sub_two (k : ℕ) :
    2 ^ k < 2 ^ (bonnetDepresApexCount k - 2) := by
  apply Nat.pow_lt_pow_right
  · omega
  · unfold bonnetDepresApexCount
    omega

/-- The half-root-child family is also larger than `2^k`. -/
theorem pow_k_lt_pow_apexCount_sub_one (k : ℕ) :
    2 ^ k < 2 ^ (bonnetDepresApexCount k - 1) := by
  apply Nat.pow_lt_pow_right
  · omega
  · unfold bonnetDepresApexCount
    omega

/-- Even after deleting one root child from a half-family, the remaining family
is larger than `2^k`. -/
theorem pow_k_lt_pow_apexCount_sub_one_sub_one (k : ℕ) :
    2 ^ k < 2 ^ (bonnetDepresApexCount k - 1) - 1 := by
  have hstep : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
    rw [pow_succ]
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    omega
  have hpow : 2 ^ (k + 1) < 2 ^ (bonnetDepresApexCount k - 1) := by
    apply Nat.pow_lt_pow_right
    · omega
    · unfold bonnetDepresApexCount
      omega
  omega

/-- Claim-11 core: while all root children remain singleton bags, no
`2^k`-bounded partition can have a bag containing two distinct apex vertices. -/
theorem false_of_apex_pair_of_root_children_singleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {x y : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hxy : x ≠ y)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : SeparatingApexBits x y,
        ({Sum.inr (rootChildWithNeighborhood k f.1)} :
          Finset (BonnetDepresVertex k)) ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hyA : (Sum.inl y : BonnetDepresVertex k) ∈ A) :
    False := by
  have hlarge :
      2 ^ (bonnetDepresApexCount k - 2) ≤ d :=
    pow_apexCount_sub_two_le_of_apex_pair_redDegreeAtMost
      hxy hred hA hchildren hxA hyA
  have hlt := pow_k_lt_pow_apexCount_sub_two k
  omega

/-- A streamlined form of the Claim-11 core using the named
`RootChildrenSingleton` condition. -/
theorem false_of_apex_pair_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {x y : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hxy : x ≠ y)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hyA : (Sum.inl y : BonnetDepresVertex k) ∈ A) :
    False :=
  false_of_apex_pair_of_root_children_singleton_of_redDegreeAtMost
    hd hxy hred hA (fun f => hroot f.1) hxA hyA

/-- If a bag contains an apex vertex and a tree vertex, then any child whose
apex-neighborhood disagrees with the tree vertex on that apex witnesses
non-homogeneity. -/
theorem partitionRedAdj_of_apex_tree_child_disagree {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {u parent : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : parent.1.val < bonnetDepresDepth k)
    {label : Fin (bonnetDepresBranch k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hlabel : label.val.testBit x.val = true)
    (hu :
      ¬ (bonnetDepresGraph k).Adj
        (Sum.inr u : BonnetDepresVertex k)
        (Sum.inr (FullTreeNode.child parent hlevel label))) :
    partitionRedAdj (bonnetDepresGraph k) A
      {Sum.inr (FullTreeNode.child parent hlevel label)} := by
  classical
  refine ⟨?_, ?_⟩
  · intro hAeq
    simp [hAeq] at hxA
  · intro hhom
    rcases hhom with hcomp | hemp
    · have huAdj :
        (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k)
          (Sum.inr (FullTreeNode.child parent hlevel label)) :=
        hcomp huA (by simp)
      exact hu huAdj
    · have hxAdj :
          bonnetDepresApexAdj x
            (FullTreeNode.child parent hlevel label) := by
        rw [bonnetDepresApexAdj_child x parent hlevel label]
        exact hlabel
      have hxGraph :
          (bonnetDepresGraph k).Adj
            (Sum.inl x : BonnetDepresVertex k)
            (Sum.inr (FullTreeNode.child parent hlevel label)) := by
        simpa [bonnetDepresGraph] using hxAdj
      exact hemp hxA (by simp) hxGraph

/-- The complementary mixed apex/tree witness: if the tree vertex is adjacent
to a child while the apex is not, the two bags are non-homogeneous. -/
theorem partitionRedAdj_of_tree_apex_child_disagree {k : ℕ}
    {A : Finset (BonnetDepresVertex k)}
    {u parent : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : parent.1.val < bonnetDepresDepth k)
    {label : Fin (bonnetDepresBranch k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hlabel : label.val.testBit x.val = false)
    (hu :
      (bonnetDepresGraph k).Adj
        (Sum.inr u : BonnetDepresVertex k)
        (Sum.inr (FullTreeNode.child parent hlevel label))) :
    partitionRedAdj (bonnetDepresGraph k) A
      {Sum.inr (FullTreeNode.child parent hlevel label)} := by
  classical
  refine ⟨?_, ?_⟩
  · intro hAeq
    simp [hAeq] at hxA
  · intro hhom
    have hxNotAdj :
        ¬ (bonnetDepresGraph k).Adj
          (Sum.inl x : BonnetDepresVertex k)
          (Sum.inr (FullTreeNode.child parent hlevel label)) := by
      intro hxGraph
      have hxAdj :
          bonnetDepresApexAdj x
            (FullTreeNode.child parent hlevel label) := by
        simpa [bonnetDepresGraph] using hxGraph
      rw [bonnetDepresApexAdj_child x parent hlevel label] at hxAdj
      simp [hlabel] at hxAdj
    rcases hhom with hcomp | hemp
    · exact hxNotAdj (hcomp hxA (by simp))
    · exact hemp huA (by simp) hu

/-- If all root children with `x`-bit `true` are singleton bags and all of
them are non-adjacent to a tree vertex in `A`, then `A` has at least half of
the root children as red neighbors. -/
theorem pow_apexCount_sub_one_le_of_apex_tree_nonadj_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : ApexBitFiber x true,
        ({Sum.inr (rootChildWithNeighborhood k f.1)} :
          Finset (BonnetDepresVertex k)) ∈ P)
    (hnotAdj :
      ∀ f : ApexBitFiber x true,
        ¬ (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k)
          (Sum.inr (rootChildWithNeighborhood k f.1)))
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    2 ^ (bonnetDepresApexCount k - 1) ≤ d := by
  classical
  have hsubset :
      apexBitRootChildBags x true ⊆
        P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B := by
    intro B hB
    rw [apexBitRootChildBags, Finset.mem_image] at hB
    rcases hB with ⟨f, _hf, rfl⟩
    have hredChild :
        partitionRedAdj (bonnetDepresGraph k) A
          {Sum.inr (rootChildWithNeighborhood k f.1)} := by
      simpa [rootChildWithNeighborhood] using
        partitionRedAdj_of_apex_tree_child_disagree
          (k := k) (A := A)
          (u := u)
          (parent := FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
          (root_level_lt_depth k)
          (label := labelOfNeighborhood f.1)
          (x := x) hxA huA (by simpa using f.2) (by simpa [rootChildWithNeighborhood] using hnotAdj f)
    simp [hchildren f, hredChild]
  have hcard := Finset.card_le_card hsubset
  rw [card_apexBitRootChildBags x true] at hcard
  exact hcard.trans (hred hA)

/-- The dual half-root-child bound, when the tree vertex is adjacent to every
root child with `x`-bit `false`. -/
theorem pow_apexCount_sub_one_le_of_apex_tree_adj_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : ApexBitFiber x false,
        ({Sum.inr (rootChildWithNeighborhood k f.1)} :
          Finset (BonnetDepresVertex k)) ∈ P)
    (hadj :
      ∀ f : ApexBitFiber x false,
        (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k)
          (Sum.inr (rootChildWithNeighborhood k f.1)))
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    2 ^ (bonnetDepresApexCount k - 1) ≤ d := by
  classical
  have hsubset :
      apexBitRootChildBags x false ⊆
        P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B := by
    intro B hB
    rw [apexBitRootChildBags, Finset.mem_image] at hB
    rcases hB with ⟨f, _hf, rfl⟩
    have hredChild :
        partitionRedAdj (bonnetDepresGraph k) A
          {Sum.inr (rootChildWithNeighborhood k f.1)} := by
      simpa [rootChildWithNeighborhood] using
        partitionRedAdj_of_tree_apex_child_disagree
          (k := k) (A := A)
          (u := u)
          (parent := FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
          (root_level_lt_depth k)
          (label := labelOfNeighborhood f.1)
          (x := x) hxA huA (by simpa using f.2) (by simpa [rootChildWithNeighborhood] using hadj f)
    simp [hchildren f, hredChild]
  have hcard := Finset.card_le_card hsubset
  rw [card_apexBitRootChildBags x false] at hcard
  exact hcard.trans (hred hA)

/-- Contradiction form of the non-adjacent half-root-child bound. -/
theorem false_of_apex_tree_nonadj_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : ApexBitFiber x true,
        ({Sum.inr (rootChildWithNeighborhood k f.1)} :
          Finset (BonnetDepresVertex k)) ∈ P)
    (hnotAdj :
      ∀ f : ApexBitFiber x true,
        ¬ (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k)
          (Sum.inr (rootChildWithNeighborhood k f.1)))
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    False := by
  have hlarge :
      2 ^ (bonnetDepresApexCount k - 1) ≤ d :=
    pow_apexCount_sub_one_le_of_apex_tree_nonadj_redDegreeAtMost
      hred hA hchildren hnotAdj hxA huA
  have hlt := pow_k_lt_pow_apexCount_sub_one k
  omega

/-- Contradiction form of the adjacent half-root-child bound. -/
theorem false_of_apex_tree_adj_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : ApexBitFiber x false,
        ({Sum.inr (rootChildWithNeighborhood k f.1)} :
          Finset (BonnetDepresVertex k)) ∈ P)
    (hadj :
      ∀ f : ApexBitFiber x false,
        (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k)
          (Sum.inr (rootChildWithNeighborhood k f.1)))
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    False := by
  have hlarge :
      2 ^ (bonnetDepresApexCount k - 1) ≤ d :=
    pow_apexCount_sub_one_le_of_apex_tree_adj_redDegreeAtMost
      hred hA hchildren hadj hxA huA
  have hlt := pow_k_lt_pow_apexCount_sub_one k
  omega

/-- If a bag contains an apex and a root child, and all other root children with
that apex bit remain singleton bags, then the bag has too many red neighbors. -/
theorem false_of_apex_rootChild_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    {f₀ : Fin (bonnetDepresApexCount k) → Bool}
    (hd : d ≤ 2 ^ k)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hchildren :
      ∀ f : ApexBitFiber x true,
        rootChildBag k f.1 ≠ rootChildBag k f₀ →
          rootChildBag k f.1 ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr (rootChildWithNeighborhood k f₀) : BonnetDepresVertex k) ∈ A) :
    False := by
  classical
  have hsubset :
      (apexBitRootChildBags x true).erase (rootChildBag k f₀) ⊆
        P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B := by
    intro B hB
    rcases Finset.mem_erase.mp hB with ⟨hBne, hBmem⟩
    rw [apexBitRootChildBags, Finset.mem_image] at hBmem
    rcases hBmem with ⟨f, _hf, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨hchildren f hBne, ?_⟩
    have hnotAdj :
        ¬ (bonnetDepresGraph k).Adj
          (Sum.inr (rootChildWithNeighborhood k f₀) : BonnetDepresVertex k)
          (Sum.inr (rootChildWithNeighborhood k f.1)) := by
      have hzero : (rootChildWithNeighborhood k f₀).1.val ≠ 0 := by
        simp
      have htwo : (rootChildWithNeighborhood k f₀).1.val ≠ 2 := by
        simp
      exact not_adj_rootChildWithNeighborhood_of_level_ne_zero_ne_two
        k hzero htwo f.1
    simpa [rootChildBag, rootChildWithNeighborhood] using
      partitionRedAdj_of_apex_tree_child_disagree
        (k := k) (A := A)
        (u := rootChildWithNeighborhood k f₀)
        (parent := FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
        (root_level_lt_depth k)
        (label := labelOfNeighborhood f.1)
        (x := x) hxA huA (by simpa using f.2) hnotAdj
  have hcard_subset := Finset.card_le_card hsubset
  have hlarge :
      2 ^ (bonnetDepresApexCount k - 1) - 1 ≤ d := by
    calc
      2 ^ (bonnetDepresApexCount k - 1) - 1
          ≤ ((apexBitRootChildBags x true).erase (rootChildBag k f₀)).card := by
            simpa [card_apexBitRootChildBags x true] using
              (Finset.pred_card_le_card_erase
                (s := apexBitRootChildBags x true) (a := rootChildBag k f₀))
      _ ≤ (P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B).card :=
            hcard_subset
      _ ≤ d := hred hA
  have hlt := pow_k_lt_pow_apexCount_sub_one_sub_one k
  omega

/-- A contraction that merges a root-child singleton bag with a bag containing
an apex immediately violates the red-degree bound. -/
theorem false_of_merge_rootChildBag_with_apex
    {k d : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    {f₀ : Fin (bonnetDepresApexCount k) → Bool}
    (hd : d ≤ 2 ^ k)
    (hrootP : RootChildrenSingleton P)
    (hredQ : PartitionRedDegreeAtMost (bonnetDepresGraph k) Q d)
    (hxB : (Sum.inl x : BonnetDepresVertex k) ∈ B)
    (hQ :
      Q = insert (rootChildBag k f₀ ∪ B)
        ((P.erase (rootChildBag k f₀)).erase B)) :
    False := by
  classical
  let A : Finset (BonnetDepresVertex k) := rootChildBag k f₀ ∪ B
  have hA : A ∈ Q := by
    rw [hQ]
    exact Finset.mem_insert_self _ _
  have hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A := by
    simp [A, hxB]
  have huA :
      (Sum.inr (rootChildWithNeighborhood k f₀) : BonnetDepresVertex k) ∈ A := by
    simp [A, rootChildBag]
  have hchildren :
      ∀ f : ApexBitFiber x true,
        rootChildBag k f.1 ≠ rootChildBag k f₀ →
          rootChildBag k f.1 ∈ Q := by
    intro f hfne
    rw [hQ, mem_merge_family_iff]
    right
    refine ⟨(rootChildrenSingleton_iff.mp hrootP) f.1, hfne, ?_⟩
    intro hEq
    have hxRoot : (Sum.inl x : BonnetDepresVertex k) ∈ rootChildBag k f.1 := by
      simpa [hEq] using hxB
    simp [rootChildBag] at hxRoot
  exact false_of_apex_rootChild_of_redDegreeAtMost
    (k := k) (d := d) (P := Q) (A := A) (x := x) (f₀ := f₀)
    hd hredQ hA hchildren hxA huA

/-- Symmetric version of `false_of_merge_rootChildBag_with_apex`. -/
theorem false_of_merge_apex_with_rootChildBag
    {k d : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    {f₀ : Fin (bonnetDepresApexCount k) → Bool}
    (hd : d ≤ 2 ^ k)
    (hrootP : RootChildrenSingleton P)
    (hredQ : PartitionRedDegreeAtMost (bonnetDepresGraph k) Q d)
    (hxB : (Sum.inl x : BonnetDepresVertex k) ∈ B)
    (hQ :
      Q = insert (B ∪ rootChildBag k f₀)
        ((P.erase B).erase (rootChildBag k f₀))) :
    False := by
  classical
  have hQ' :
      Q = insert (rootChildBag k f₀ ∪ B)
        ((P.erase (rootChildBag k f₀)).erase B) := by
    rw [hQ, Finset.union_comm]
    congr 1
    ext C
    by_cases hCr : C = rootChildBag k f₀
    · subst C
      by_cases hBr : B = rootChildBag k f₀
      · subst B
        simp
      · simp
    · by_cases hCB : C = B
      · subst C
        simp [hCr]
      · simp [hCr, hCB]
  exact false_of_merge_rootChildBag_with_apex
    (k := k) (d := d) (P := P) (Q := Q) (B := B) (x := x) (f₀ := f₀)
    hd hrootP hredQ hxB hQ'

/-- If `u` is a grandchild of the root, then among root children with `x`-bit
`true`, all but possibly the parent of `u` are non-adjacent to `u`.  Thus a bag
containing both `x` and `u` has at least `2^(|X|-1)-1` red neighbors. -/
theorem pow_apexCount_sub_one_sub_one_le_of_apex_grandchild_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hlevel : u.1.val = 2)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    2 ^ (bonnetDepresApexCount k - 1) - 1 ≤ d := by
  classical
  let hpos : 0 < u.1.val := by omega
  let parentBag : Finset (BonnetDepresVertex k) :=
    {Sum.inr (FullTreeNode.parent u hpos)}
  have hsubset :
      (apexBitRootChildBags x true).erase parentBag ⊆
        P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B := by
    intro B hB
    rcases Finset.mem_erase.mp hB with ⟨hBne, hBmem⟩
    rw [apexBitRootChildBags, Finset.mem_image] at hBmem
    rcases hBmem with ⟨f, _hf, rfl⟩
    have hnotAdj :
        ¬ (bonnetDepresGraph k).Adj
          (Sum.inr u : BonnetDepresVertex k)
          (Sum.inr (rootChildWithNeighborhood k f.1)) := by
      intro hadj
      have htree :
          (FullTreeNode.graph (bonnetDepresBranch k) (bonnetDepresDepth k)).Adj
            u (rootChildWithNeighborhood k f.1) := by
        simpa [bonnetDepresGraph] using hadj
      have hroot_le : (rootChildWithNeighborhood k f.1).1.val ≤ u.1.val := by
        rw [rootChildWithNeighborhood_level, hlevel]
        omega
      have hparent :
          FullTreeNode.IsParent (rootChildWithNeighborhood k f.1) u :=
        FullTreeNode.isParent_of_adj_of_level_le htree hroot_le
      have hparent_eq :
          rootChildWithNeighborhood k f.1 = FullTreeNode.parent u hpos :=
        FullTreeNode.isParent_unique hparent
          (FullTreeNode.parent_isParent u hpos)
      exact hBne (by simp [parentBag, hparent_eq])
    have hredChild :
        partitionRedAdj (bonnetDepresGraph k) A
          {Sum.inr (rootChildWithNeighborhood k f.1)} := by
      simpa [rootChildWithNeighborhood] using
        partitionRedAdj_of_apex_tree_child_disagree
          (k := k) (A := A)
          (u := u)
          (parent := FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
          (root_level_lt_depth k)
          (label := labelOfNeighborhood f.1)
          (x := x) hxA huA (by simpa using f.2)
          (by simpa [rootChildWithNeighborhood] using hnotAdj)
    simp [hroot f.1, hredChild]
  have hcard := Finset.card_le_card hsubset
  have hpred :
      2 ^ (bonnetDepresApexCount k - 1) - 1 ≤
        ((apexBitRootChildBags x true).erase parentBag).card := by
    rw [← card_apexBitRootChildBags x true]
    exact Finset.pred_card_le_card_erase
  exact hpred.trans (hcard.trans (hred hA))

/-- Claim-12 grandchild case: before root children are contracted, a
`2^k`-bounded partition cannot mix an apex with a level-`2` tree vertex. -/
theorem false_of_apex_grandchild_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hlevel : u.1.val = 2)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    False := by
  have hlarge :
      2 ^ (bonnetDepresApexCount k - 1) - 1 ≤ d :=
    pow_apexCount_sub_one_sub_one_le_of_apex_grandchild_redDegreeAtMost
      hlevel hroot hred hA hxA huA
  have hlt := pow_k_lt_pow_apexCount_sub_one_sub_one k
  omega

/-- Claim-12 root case: before root children are contracted, a `2^k`-bounded
partition cannot have a bag containing an apex and the tree root. -/
theorem false_of_apex_root_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (hrootA :
      (Sum.inr (FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k)) :
        BonnetDepresVertex k) ∈ A) :
    False :=
  false_of_apex_tree_adj_of_redDegreeAtMost
    (k := k) (d := d) (P := P) (A := A)
    (u := FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k))
    (x := x) hd hred hA (fun f => hroot f.1)
    (fun f => root_adj_rootChildWithNeighborhood k f.1) hxA hrootA

/-- Claim-12 non-root/non-grandchild case: before root children are contracted,
a `2^k`-bounded partition cannot mix an apex with a tree vertex whose level is
neither `0` nor `2`. -/
theorem false_of_apex_tree_level_ne_zero_ne_two_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hzero : u.1.val ≠ 0) (htwo : u.1.val ≠ 2)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    False :=
  false_of_apex_tree_nonadj_of_redDegreeAtMost
    (k := k) (d := d) (P := P) (A := A) (u := u) (x := x)
    hd hred hA (fun f => hroot f.1)
    (fun f => not_adj_rootChildWithNeighborhood_of_level_ne_zero_ne_two
      k hzero htwo f.1)
    hxA huA

/-- Claim 12 in consolidated form: before any root child is contracted, a
`2^k`-bounded partition has no part meeting both the apex set and the tree
side. -/
theorem false_of_apex_tree_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A) :
    False := by
  by_cases hzero : u.1.val = 0
  · have hu :
        u = FullTreeNode.root (bonnetDepresBranch k) (bonnetDepresDepth k) :=
      FullTreeNode.eq_root_of_level_zero hzero
    subst u
    exact false_of_apex_root_of_rootChildrenSingleton_of_redDegreeAtMost
      hd hroot hred hA hxA huA
  · by_cases hone : u.1.val = 1
    · rcases exists_rootChildWithNeighborhood_eq_of_level_one k hone with ⟨f, hf⟩
      have hsingleton :
          ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ P := by
        rw [← hf]
        exact hroot f
      by_cases hAeq : A = ({Sum.inr u} : Finset (BonnetDepresVertex k))
      · subst A
        simp at hxA
      · exact (Finset.disjoint_left.mp (hpart.2.1 hA hsingleton hAeq))
          huA (by simp)
    · by_cases htwo : u.1.val = 2
      · exact false_of_apex_grandchild_of_rootChildrenSingleton_of_redDegreeAtMost
          hd htwo hroot hred hA hxA huA
      · exact false_of_apex_tree_level_ne_zero_ne_two_of_rootChildrenSingleton_of_redDegreeAtMost
          hd hzero htwo hroot hred hA hxA huA

/-- Claim 13: in the same initial segment, every part meeting the apex set is
an apex singleton. -/
theorem eq_singleton_of_apex_mem_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A) :
    A = {Sum.inl x} := by
  classical
  ext z
  constructor
  · intro hzA
    cases z with
    | inl y =>
        by_cases hyx : y = x
        · subst y
          simp
        · exfalso
          exact false_of_apex_pair_of_rootChildrenSingleton_of_redDegreeAtMost
            (k := k) (d := d) (P := P) (A := A)
            (x := x) (y := y) hd (fun hxy => hyx hxy.symm)
            hroot hred hA hxA hzA
    | inr u =>
        exfalso
        exact false_of_apex_tree_of_rootChildrenSingleton_of_redDegreeAtMost
          (k := k) (d := d) (P := P) (A := A) (u := u) (x := x)
          hd hpart hroot hred hA hxA hzA
  · intro hz
    rw [Finset.mem_singleton] at hz
    subst z
    exact hxA

/-- Claim 13 specialized to an actual contraction-sequence state. -/
theorem ContractionSequence.eq_singleton_of_apex_mem_of_rootChildrenSingleton
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i ≤ S.stepCount)
    {A : Finset (BonnetDepresVertex k)}
    {x : Fin (bonnetDepresApexCount k)}
    (hd : d ≤ 2 ^ k)
    (hroot : RootChildrenSingleton (S.state i).bags)
    (hA : A ∈ (S.state i).bags)
    (hxA : (Sum.inl x : BonnetDepresVertex k) ∈ A) :
    A = {Sum.inl x} :=
  eq_singleton_of_apex_mem_of_rootChildrenSingleton_of_redDegreeAtMost
    (k := k) (d := d) (P := (S.state i).bags) (A := A) (x := x)
    hd (_root_.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
    hroot (_root_.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state S hi)
    hA hxA

/-- During the protected initial segment, every apex vertex is represented by its
singleton bag. -/
theorem apexSingleton_mem_of_rootChildrenSingleton_of_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (x : Fin (bonnetDepresApexCount k)) :
    ({Sum.inl x} : Finset (BonnetDepresVertex k)) ∈ P := by
  classical
  rcases hpart.2.2 (Sum.inl x : BonnetDepresVertex k) with ⟨A, hA, hxA⟩
  have hAeq :
      A = ({Sum.inl x} : Finset (BonnetDepresVertex k)) :=
    eq_singleton_of_apex_mem_of_rootChildrenSingleton_of_redDegreeAtMost
      (k := k) (d := d) (P := P) (A := A) (x := x)
      hd hpart hroot hred hA hxA
  simpa [hAeq] using hA

/-- Singleton apex bags are injectively indexed by the apex vertex. -/
theorem apexSingletonBag_injective (k : ℕ) :
    Function.Injective
      (fun x : Fin (bonnetDepresApexCount k) =>
        ({Sum.inl x} : Finset (BonnetDepresVertex k))) := by
  intro x y hxy
  exact Sum.inl.inj (Finset.singleton_inj.mp hxy)

/-- If a bag contains a set of tree vertices, then every apex coordinate on which
that set varies gives a red-neighbor apex singleton bag. -/
theorem childApexVariationSet_card_le_redDegreeAtMost
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {S : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (hSA :
      ∀ ⦃c : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)⦄,
        c ∈ S → (Sum.inr c : BonnetDepresVertex k) ∈ A) :
    (childApexVariationSet S).card ≤ d := by
  classical
  let apexBag : Fin (bonnetDepresApexCount k) → Finset (BonnetDepresVertex k) :=
    fun x => {Sum.inl x}
  let redApexBags : Finset (Finset (BonnetDepresVertex k)) :=
    (childApexVariationSet S).image apexBag
  let redNeighbors : Finset (Finset (BonnetDepresVertex k)) :=
    P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B
  have hsubset : redApexBags ⊆ redNeighbors := by
    intro B hB
    change B ∈ (childApexVariationSet S).image apexBag at hB
    rw [Finset.mem_image] at hB
    rcases hB with ⟨x, hxvar, rfl⟩
    change apexBag x ∈ P.filter fun B => partitionRedAdj (bonnetDepresGraph k) A B
    rw [Finset.mem_filter]
    refine ⟨apexSingleton_mem_of_rootChildrenSingleton_of_redDegreeAtMost
      (k := k) (d := d) (P := P) hd hpart hroot hred x, ?_⟩
    rw [childApexVariationSet, Finset.mem_filter] at hxvar
    rcases hxvar.2 with ⟨c₁, hc₁, c₂, hc₂, hdisagree | hdisagree⟩
    · exact partitionRedAdj_of_apexAdj_disagree_in_bag
        (hSA hc₁) (hSA hc₂) hdisagree.1 hdisagree.2
    · exact partitionRedAdj_of_apexAdj_disagree_in_bag
        (hSA hc₂) (hSA hc₁) hdisagree.1 hdisagree.2
  have hcard_image :
      redApexBags.card = (childApexVariationSet S).card := by
    change ((childApexVariationSet S).image apexBag).card =
      (childApexVariationSet S).card
    rw [Finset.card_image_of_injective]
    exact apexSingletonBag_injective k
  calc
    (childApexVariationSet S).card = redApexBags.card := hcard_image.symm
    _ ≤ redNeighbors.card := Finset.card_le_card hsubset
    _ ≤ d := hred hA

/-- For a fixed apex singleton, red-degree control bounds how many large bags are
red-adjacent to it. -/
theorem card_largeChildBags_redAdjacent_to_apex_le {k d : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (x : Fin (bonnetDepresApexCount k)) :
    (largeChildBagsRedAdjacentToApex P x).card ≤ d := by
  classical
  let X : Finset (BonnetDepresVertex k) := {Sum.inl x}
  have hX : X ∈ P :=
    apexSingleton_mem_of_rootChildrenSingleton_of_redDegreeAtMost
      (k := k) (d := d) (P := P) hd hpart hroot hred x
  have hsubset :
      largeChildBagsRedAdjacentToApex P x ⊆
        P.filter fun A => partitionRedAdj (bonnetDepresGraph k) X A := by
    intro A hA
    change A ∈ (largeChildBags P).filter
      (fun A => partitionRedAdj (bonnetDepresGraph k) A X) at hA
    rw [Finset.mem_filter] at hA ⊢
    exact ⟨(mem_largeChildBags.mp hA.1).1, partitionRedAdj_symm hA.2⟩
  exact (Finset.card_le_card hsubset).trans (hred hX)

/-- Counting incidences by large bags: every large bag contributes at least
`k+1` apex-red incidences. -/
theorem largeChildBags_card_mul_le_incidences_card {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))} :
    (largeChildBags P).card * (k + 1) ≤
      (largeChildBagApexIncidences P).card := by
  classical
  let L := largeChildBags P
  let fiber :
      Finset (BonnetDepresVertex k) →
        Finset (Finset (BonnetDepresVertex k) × Fin (bonnetDepresApexCount k)) :=
    fun A => (apexRedCoordinatesOfBag A).image fun x => (A, x)
  have hInc :
      largeChildBagApexIncidences P = L.biUnion fiber := by
    ext pair
    rcases pair with ⟨A, x⟩
    simp [largeChildBagApexIncidences, L, fiber, apexRedCoordinatesOfBag]
  have hdisj :
      ∀ ⦃A⦄, A ∈ L → ∀ ⦃B⦄, B ∈ L → A ≠ B →
        Disjoint (fiber A) (fiber B) := by
    intro A _hA B _hB hAB
    rw [Finset.disjoint_left]
    intro pair hpairA hpairB
    change pair ∈ (apexRedCoordinatesOfBag A).image (fun x => (A, x)) at hpairA
    change pair ∈ (apexRedCoordinatesOfBag B).image (fun x => (B, x)) at hpairB
    rw [Finset.mem_image] at hpairA hpairB
    rcases hpairA with ⟨x, _hx, rfl⟩
    rcases hpairB with ⟨y, _hy, hpair⟩
    exact hAB (Prod.ext_iff.mp hpair).1.symm
  have hfiber_card :
      ∀ ⦃A⦄, A ∈ L → (fiber A).card = (apexRedCoordinatesOfBag A).card := by
    intro A _hA
    change ((apexRedCoordinatesOfBag A).image (fun x => (A, x))).card =
      (apexRedCoordinatesOfBag A).card
    rw [Finset.card_image_of_injective]
    intro x y hxy
    exact (Prod.ext_iff.mp hxy).2
  calc
    L.card * (k + 1) = ∑ A ∈ L, (k + 1) := by
      simp [Finset.sum_const, Nat.mul_comm]
    _ ≤ ∑ A ∈ L, (fiber A).card := by
      refine Finset.sum_le_sum ?_
      intro A hA
      rw [hfiber_card hA]
      exact le_card_apexRedCoordinatesOfBag_of_isLargeChildBag
        (mem_largeChildBags.mp (by simpa [L] using hA)).2
    _ = (largeChildBagApexIncidences P).card := by
      rw [hInc, Finset.card_biUnion hdisj]

/-- Counting incidences by apex coordinates: each apex singleton has at most `d`
large red-neighbor bags. -/
theorem largeChildBagApexIncidences_card_le {k d : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d) :
    (largeChildBagApexIncidences P).card ≤ bonnetDepresApexCount k * d := by
  classical
  let fiber :
      Fin (bonnetDepresApexCount k) →
        Finset (Finset (BonnetDepresVertex k) × Fin (bonnetDepresApexCount k)) :=
    fun x => (largeChildBagsRedAdjacentToApex P x).image fun A => (A, x)
  have hInc :
      largeChildBagApexIncidences P = Finset.univ.biUnion fiber := by
    ext pair
    rcases pair with ⟨A, x⟩
    simp [largeChildBagApexIncidences, largeChildBagsRedAdjacentToApex, fiber]
  calc
    (largeChildBagApexIncidences P).card =
        (Finset.univ.biUnion fiber).card := by rw [hInc]
    _ ≤ ∑ x : Fin (bonnetDepresApexCount k), (fiber x).card := by
      exact Finset.card_biUnion_le
    _ = ∑ x : Fin (bonnetDepresApexCount k),
        (largeChildBagsRedAdjacentToApex P x).card := by
      refine Finset.sum_congr rfl ?_
      intro x _hx
      change ((largeChildBagsRedAdjacentToApex P x).image (fun A => (A, x))).card =
        (largeChildBagsRedAdjacentToApex P x).card
      rw [Finset.card_image_of_injective]
      intro A B hAB
      exact (Prod.ext_iff.mp hAB).1
    _ ≤ ∑ _x : Fin (bonnetDepresApexCount k), d := by
      refine Finset.sum_le_sum ?_
      intro x _hx
      exact card_largeChildBags_redAdjacent_to_apex_le hd hpart hroot hred x
    _ = bonnetDepresApexCount k * d := by
      simp [Finset.sum_const, Nat.mul_comm]

/-- The paper's coarse bound on `B`: under red-degree at most `2^k`, at most
`2^(k+2)` parts can contain many children of a single tree node. -/
theorem largeChildBags_card_le {k d : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d) :
    (largeChildBags P).card ≤ 2 ^ (k + 2) := by
  have hincLower :=
    largeChildBags_card_mul_le_incidences_card (k := k) (P := P)
  have hincUpper :=
    largeChildBagApexIncidences_card_le
      (k := k) (d := d) (P := P) hd hpart hroot hred
  have harith :
      bonnetDepresApexCount k * d ≤ (k + 1) * 2 ^ (k + 2) := by
    calc
      bonnetDepresApexCount k * d
          ≤ bonnetDepresApexCount k * 2 ^ k :=
        Nat.mul_le_mul_left _ hd
      _ ≤ (4 * (k + 1)) * 2 ^ k := by
        apply Nat.mul_le_mul_right
        unfold bonnetDepresApexCount
        omega
      _ = (k + 1) * 2 ^ (k + 2) := by
        rw [show k + 2 = 2 + k by omega, pow_add]
        change (4 * (k + 1)) * 2 ^ k = (k + 1) * (4 * 2 ^ k)
        rw [Nat.mul_comm 4 (k + 1), Nat.mul_assoc]
  have hmul :
      (largeChildBags P).card * (k + 1) ≤ (2 ^ (k + 2)) * (k + 1) := by
    calc
      (largeChildBags P).card * (k + 1)
          ≤ (largeChildBagApexIncidences P).card := hincLower
      _ ≤ bonnetDepresApexCount k * d := hincUpper
      _ ≤ (k + 1) * 2 ^ (k + 2) := harith
      _ = (2 ^ (k + 2)) * (k + 1) := by rw [Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_right hmul (Nat.succ_pos k)

/-- Claim 14 with the witness part retained: a non-singleton tree part has a
large child-bag witness in itself or among its red neighbors. -/
theorem exists_largeChildBag_in_redOrSelfBags_of_nonSingleton_tree_bag
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hnotSingleton : A ≠ {Sum.inr u})
    (hlevel : u.1.val < bonnetDepresDepth k) :
    ∃ C ∈ largeChildBags P,
      C ∈ redOrSelfBags P A ∧
        manyChildrenThreshold k ≤ (C ∩ childVertexSet u hlevel).card := by
  classical
  have hexists :
      ∃ z ∈ A, z ≠ (Sum.inr u : BonnetDepresVertex k) := by
    by_contra hnone
    apply hnotSingleton
    ext z
    constructor
    · intro hz
      have hz_eq : z = (Sum.inr u : BonnetDepresVertex k) := by
        by_contra hne
        exact hnone ⟨z, hz, hne⟩
      simp [hz_eq]
    · intro hz
      rw [Finset.mem_singleton] at hz
      simpa [hz] using huA
  rcases hexists with ⟨z, hzA, hzu⟩
  cases z with
  | inl x =>
      have hAeq :
          A = ({Sum.inl x} : Finset (BonnetDepresVertex k)) :=
        eq_singleton_of_apex_mem_of_rootChildrenSingleton_of_redDegreeAtMost
          hd hpart hroot hred hA hzA
      have huSingleton :
          (Sum.inr u : BonnetDepresVertex k) ∈
            ({Sum.inl x} : Finset (BonnetDepresVertex k)) := by
        rw [hAeq] at huA
        exact huA
      simp at huSingleton
  | inr w =>
      have hwu : w ≠ u := by
        intro hwu
        exact hzu (by simp [hwu])
      rcases hasManyChildrenInPart_of_two_tree_vertices_of_redDegreeAtMost
          (k := k) (d := d) (P := P) (A := A) (u := u) (w := w)
          hd hpart hred hA huA hzA hwu hlevel with
        ⟨C, hC, hmany⟩
      have hClarge : C ∈ largeChildBags P := by
        rw [mem_largeChildBags]
        exact ⟨hC, u, hlevel, hmany⟩
      have hCredOrSelf : C ∈ redOrSelfBags P A := by
        by_cases hCA : C = A
        · rw [hCA, redOrSelfBags]
          simp
        · rw [redOrSelfBags, Finset.mem_insert, Finset.mem_filter]
          right
          refine ⟨hC, ?_⟩
          exact partitionRedAdj_of_many_children_and_two_tree_vertices
            (k := k) (A := A) (C := C) (u := u) (w := w)
            (fun hAC => hCA hAC.symm) huA hzA hwu hlevel hmany
      exact ⟨C, hClarge, hCredOrSelf, hmany⟩

/-- Parts that contain an internal tree node and are not that node's singleton
bag.  These are the `B'`-type parts in the final lower-bound counting. -/
noncomputable def internalNonSingletonTreeBags {k : ℕ}
    (P : Finset (Finset (BonnetDepresVertex k))) :
    Finset (Finset (BonnetDepresVertex k)) := by
  classical
  exact P.filter fun A =>
    ∃ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
      IsInternal u ∧
        (Sum.inr u : BonnetDepresVertex k) ∈ A ∧
          A ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k))

@[simp] theorem mem_internalNonSingletonTreeBags {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)} :
    A ∈ internalNonSingletonTreeBags P ↔
      A ∈ P ∧
        ∃ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          IsInternal u ∧
            (Sum.inr u : BonnetDepresVertex k) ∈ A ∧
              A ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
  classical
  simp [internalNonSingletonTreeBags]

/-- A part containing an internal tree node and a distinct tree node belongs to
`internalNonSingletonTreeBags`. -/
theorem mem_internalNonSingletonTreeBags_of_two_tree_vertices {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hA : A ∈ P)
    (hlevel : IsInternal u)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hvA : (Sum.inr v : BonnetDepresVertex k) ∈ A)
    (huv : u ≠ v) :
    A ∈ internalNonSingletonTreeBags P := by
  rw [mem_internalNonSingletonTreeBags]
  refine ⟨hA, u, hlevel, huA, ?_⟩
  intro hsingleton
  have hvSingleton :
      (Sum.inr v : BonnetDepresVertex k) ∈
        ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
    simpa [hsingleton] using hvA
  rw [Finset.mem_singleton] at hvSingleton
  exact huv (Sum.inr.inj hvSingleton.symm)

/-- A non-singleton internal-tree bag is not any singleton tree-vertex bag. -/
theorem internalNonSingletonTreeBag_ne_singleton_tree {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    (hA : A ∈ internalNonSingletonTreeBags P)
    (p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    A ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
  rcases mem_internalNonSingletonTreeBags.mp hA with
    ⟨_hAP, u, _hlevel, huA, hnotSingleton⟩
  intro hAeq
  have hup : u = p := by
    have huSingleton :
        (Sum.inr u : BonnetDepresVertex k) ∈
          ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
      simpa [hAeq] using huA
    exact Sum.inr.inj (Finset.mem_singleton.mp huSingleton)
  exact hnotSingleton (by simpa [hup] using hAeq)

/-- A large child bag contains at least two vertices, so it cannot be a tree
singleton. -/
theorem largeChildBag_ne_singleton_tree {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    (hA : A ∈ largeChildBags P)
    (p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :
    A ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
  classical
  rcases (mem_largeChildBags.mp hA).2 with ⟨u, hlevel, hmany⟩
  have htwo : 1 < (A ∩ childVertexSet u hlevel).card := by
    have htwo' := two_le_manyChildrenThreshold k
    omega
  rcases Finset.one_lt_card.mp htwo with ⟨x, hx, y, hy, hxy⟩
  intro hsingleton
  have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
  have hyA : y ∈ A := (Finset.mem_inter.mp hy).1
  have hxSingleton : x ∈ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
    simpa [hsingleton] using hxA
  have hySingleton : y ∈ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
    simpa [hsingleton] using hyA
  rw [Finset.mem_singleton] at hxSingleton hySingleton
  exact hxy (hxSingleton.trans hySingleton.symm)

/-- Every non-singleton internal-tree part is itself a large bag or has a large
bag among its red neighbors. -/
theorem exists_largeChildBag_in_redOrSelfBags_of_internalNonSingletonTreeBag
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ internalNonSingletonTreeBags P) :
    ∃ C ∈ largeChildBags P, C ∈ redOrSelfBags P A := by
  rcases mem_internalNonSingletonTreeBags.mp hA with
    ⟨hAP, u, hlevel, huA, hnotSingleton⟩
  rcases exists_largeChildBag_in_redOrSelfBags_of_nonSingleton_tree_bag
      (k := k) (d := d) (P := P) (A := A) (u := u)
      hd hpart hroot hred hAP huA hnotSingleton hlevel with
    ⟨C, hC, hCredOrSelf, _hmany⟩
  exact ⟨C, hC, hCredOrSelf⟩

/-- Incidence count for the final lower-bound step: under bounded red degree,
there are at most `|B| * (d + 1)` non-singleton parts containing an internal tree
node, where `B` is the set of large child bags. -/
theorem internalNonSingletonTreeBags_card_le_largeChildBags_mul_succ
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d) :
    (internalNonSingletonTreeBags P).card ≤ (largeChildBags P).card * (d + 1) := by
  classical
  let I := internalNonSingletonTreeBags P
  let L := largeChildBags P
  let Ilarge := I.filter fun A => A ∈ L
  let Ismall := I.filter fun A => A ∉ L
  have hsplit : I.card = Ilarge.card + Ismall.card := by
    dsimp [Ilarge, Ismall]
    simpa [Nat.add_comm] using
      (Finset.card_filter_add_card_filter_not
        (s := I) (p := fun A => A ∈ L)).symm
  have hIlarge_card : Ilarge.card ≤ L.card := by
    exact Finset.card_le_card (by
      intro A hA
      exact (Finset.mem_filter.mp hA).2)
  have hIsmall_subset :
      Ismall ⊆ L.biUnion
        (fun C => P.filter fun A => partitionRedAdj (bonnetDepresGraph k) C A) := by
    intro A hA
    rw [Finset.mem_filter] at hA
    rcases hA with ⟨hAI, hAnotL⟩
    rcases exists_largeChildBag_in_redOrSelfBags_of_internalNonSingletonTreeBag
        (k := k) (d := d) (P := P) (A := A)
        hd hpart hroot hred (by simpa [I] using hAI) with
      ⟨C, hCL, hCredOrSelf⟩
    have hCA : C ≠ A := by
      intro h
      exact hAnotL (by simpa [L, h] using hCL)
    have hredCA : partitionRedAdj (bonnetDepresGraph k) C A := by
      rw [redOrSelfBags, Finset.mem_insert, Finset.mem_filter] at hCredOrSelf
      rcases hCredOrSelf with hCAeq | hredAC
      · exact False.elim (hCA hCAeq)
      · exact partitionRedAdj_symm hredAC.2
    rw [Finset.mem_biUnion]
    refine ⟨C, hCL, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hredCA⟩
    exact (mem_internalNonSingletonTreeBags.mp (by simpa [I] using hAI)).1
  have hIsmall_card : Ismall.card ≤ L.card * d := by
    calc
      Ismall.card
          ≤ (L.biUnion
              (fun C => P.filter fun A =>
                partitionRedAdj (bonnetDepresGraph k) C A)).card :=
        Finset.card_le_card hIsmall_subset
      _ ≤ ∑ C ∈ L, (P.filter fun A =>
          partitionRedAdj (bonnetDepresGraph k) C A).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _C ∈ L, d := by
        refine Finset.sum_le_sum ?_
        intro C hC
        exact hred (mem_largeChildBags.mp (by simpa [L] using hC)).1
      _ = L.card * d := by
        simp [Finset.sum_const, Nat.mul_comm]
  calc
    I.card = Ilarge.card + Ismall.card := hsplit
    _ ≤ L.card + L.card * d := Nat.add_le_add hIlarge_card hIsmall_card
    _ = L.card * (d + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]

/-- The chosen constants leave room beyond the red-degree upper bound for
non-singleton internal-tree parts. -/
theorem largeChildBags_mul_succ_lt_manyInternalBagsThreshold
    {k d Lcard : ℕ}
    (hLcard : Lcard ≤ 2 ^ (k + 2))
    (hd : d ≤ 2 ^ k) :
    Lcard * (d + 1) < manyInternalBagsThreshold k := by
  have hpow : 2 ^ k ≤ manyChildrenThreshold k := by
    unfold manyChildrenThreshold
    apply Nat.pow_le_pow_right
    · omega
    · omega
  have hupper :
      Lcard * (d + 1) ≤
        2 ^ (k + 2) * (manyChildrenThreshold k + 1) := by
    exact Nat.mul_le_mul hLcard (Nat.succ_le_succ (hd.trans hpow))
  unfold manyInternalBagsThreshold
  omega

/-- A state with red degree at most `2^k` cannot contain the final threshold
number of non-singleton internal-tree parts. -/
theorem false_of_many_internalNonSingletonTreeBags
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hmany : manyInternalBagsThreshold k ≤ (internalNonSingletonTreeBags P).card) :
    False := by
  have hupper :=
    internalNonSingletonTreeBags_card_le_largeChildBags_mul_succ
      (k := k) (d := d) (P := P) hd hpart hroot hred
  have hLcard :=
    largeChildBags_card_le (k := k) (d := d) (P := P) hd hpart hroot hred
  have hgap :=
    largeChildBags_mul_succ_lt_manyInternalBagsThreshold
      (k := k) (d := d) (Lcard := (largeChildBags P).card) hLcard hd
  omega

/-- Claim 14 in the form needed for contraction states: while root children are
singleton bags, any non-singleton bag containing a tree vertex with children
contains another tree vertex, hence has many children of the first vertex in one
part. -/
theorem hasManyChildrenInPart_of_nonSingleton_tree_bag_of_rootChildrenSingleton
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hA : A ∈ P)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hnotSingleton : A ≠ {Sum.inr u})
    (hlevel : u.1.val < bonnetDepresDepth k) :
    HasManyChildrenInPart P u hlevel (manyChildrenThreshold k) := by
  classical
  have hexists :
      ∃ z ∈ A, z ≠ (Sum.inr u : BonnetDepresVertex k) := by
    by_contra hnone
    apply hnotSingleton
    ext z
    constructor
    · intro hz
      have hz_eq : z = (Sum.inr u : BonnetDepresVertex k) := by
        by_contra hne
        exact hnone ⟨z, hz, hne⟩
      simp [hz_eq]
    · intro hz
      rw [Finset.mem_singleton] at hz
      simpa [hz] using huA
  rcases hexists with ⟨z, hzA, hzu⟩
  cases z with
  | inl x =>
      have hAeq :
          A = ({Sum.inl x} : Finset (BonnetDepresVertex k)) :=
        eq_singleton_of_apex_mem_of_rootChildrenSingleton_of_redDegreeAtMost
          hd hpart hroot hred hA hzA
      have huSingleton :
          (Sum.inr u : BonnetDepresVertex k) ∈
            ({Sum.inl x} : Finset (BonnetDepresVertex k)) := by
        rw [hAeq] at huA
        exact huA
      simp at huSingleton
  | inr w =>
      have hwu : w ≠ u := by
        intro hwu
        exact hzu (by simp [hwu])
      exact hasManyChildrenInPart_of_two_tree_vertices_of_redDegreeAtMost
        hd hpart hred hA huA hzA hwu hlevel

/-- Claim 16: if a non-preleaf internal node satisfies property `P`, then many
of its children also satisfy property `P`. -/
theorem hasManyPChildren_of_hasManyChildrenInPart_of_nonpreleaf
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hP : HasManyChildrenInPart P u hlevel (manyChildrenThreshold k))
    (hnonpreleaf : IsNonPreleafInternal u) :
    HasManyPChildren P u hlevel (manyChildrenThreshold k) := by
  classical
  have hnonpreleaf_raw : u.1.val + 1 < bonnetDepresDepth k := by
    simpa [IsNonPreleafInternal] using hnonpreleaf
  rcases hP with ⟨A, hA, hcardA⟩
  refine ⟨childrenInBag A u hlevel, ?_, ?_, ?_⟩
  · intro c hc
    exact (mem_childrenInBag.mp hc).1
  · rwa [card_childrenInBag]
  · intro c hc
    have hcdata := mem_childrenInBag.mp hc
    have hcLevel : c.1.val < bonnetDepresDepth k := by
      rcases mem_childSet.mp hcdata.1 with ⟨label, rfl⟩
      simp [FullTreeNode.child]
      omega
    have hthreshold_two : 2 ≤ manyChildrenThreshold k := by
      unfold manyChildrenThreshold
      have hpow : 2 ^ 1 ≤ 2 ^ (k + 1) := by
        apply Nat.pow_le_pow_right
        · omega
        · omega
      simpa using hpow
    have hnotSingleton :
        A ≠ ({Sum.inr c} : Finset (BonnetDepresVertex k)) := by
      intro hAeq
      have hcard_le_one :
          (A ∩ childVertexSet u hlevel).card ≤ 1 := by
        calc
          (A ∩ childVertexSet u hlevel).card ≤ A.card :=
            Finset.card_le_card (by intro v hv; rw [Finset.mem_inter] at hv; exact hv.1)
          _ = 1 := by simp [hAeq]
      omega
    exact ⟨hcLevel,
      hasManyChildrenInPart_of_nonSingleton_tree_bag_of_rootChildrenSingleton
        (k := k) (d := d) (P := P) (A := A) (u := c)
        hd hpart hroot hred hA hcdata.2 hnotSingleton hcLevel⟩

/-- Claim 17: for every internal tree node in a bounded state, property `P`
implies property `Q`. -/
theorem qProperty_of_hasManyChildrenInPart
    {k d : ℕ} {P : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hroot : RootChildrenSingleton P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : IsInternal u)
    (hP : HasManyChildrenInPart P u hlevel (manyChildrenThreshold k)) :
    QProperty P u := by
  classical
  let remaining
      (u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) : ℕ :=
    bonnetDepresDepth k - u.1.val
  have hmain :
      ∀ n : ℕ,
        ∀ u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          ∀ hlevel : IsInternal u, remaining u = n →
            HasManyChildrenInPart P u hlevel (manyChildrenThreshold k) →
              QProperty P u := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro u hlevel hn hP
        by_cases hpre : IsPreleaf u
        · exact qProperty_of_hasManyChildrenInPart_preleaf hpre hlevel hP
        · have hnonpreleaf : IsNonPreleafInternal u := by
            unfold IsPreleaf at hpre
            unfold IsInternal at hlevel
            unfold IsNonPreleafInternal
            omega
          have hchildren :
              HasManyPChildren P u hlevel (manyChildrenThreshold k) :=
            hasManyPChildren_of_hasManyChildrenInPart_of_nonpreleaf
              (k := k) (d := d) (P := P) (u := u) (hlevel := hlevel)
              hd hpart hroot hred hP hnonpreleaf
          rcases hchildren with ⟨S, hSsubset, hScard, hSprop⟩
          have htwo : 2 ≤ S.card :=
            (two_le_manyChildrenThreshold k).trans hScard
          have htwo_exists :
              ∃ c₁ ∈ S, ∃ c₂ ∈ S, c₁ ≠ c₂ := by
            by_contra hnone
            have hcard_le_one : S.card ≤ 1 := by
              rw [Finset.card_le_one_iff]
              intro a b ha hb
              by_contra hab
              exact hnone ⟨a, ha, b, hb, hab⟩
            omega
          rcases htwo_exists with ⟨c₁, hc₁S, c₂, hc₂S, hcne⟩
          rcases hSprop hc₁S with ⟨hc₁Level, hP₁⟩
          rcases hSprop hc₂S with ⟨hc₂Level, hP₂⟩
          have hc₁child : c₁ ∈ childSet u hlevel := hSsubset hc₁S
          have hc₂child : c₂ ∈ childSet u hlevel := hSsubset hc₂S
          have hc₁level_eq := level_eq_succ_of_mem_childSet hc₁child
          have hc₂level_eq := level_eq_succ_of_mem_childSet hc₂child
          have hc₁_lt : remaining c₁ < n := by
            unfold remaining
            rw [hc₁level_eq]
            unfold remaining at hn
            omega
          have hc₂_lt : remaining c₂ < n := by
            unfold remaining
            rw [hc₂level_eq]
            unfold remaining at hn
            omega
          have hq₁ : QProperty P c₁ :=
            ih (remaining c₁) hc₁_lt c₁ hc₁Level rfl hP₁
          have hq₂ : QProperty P c₂ :=
            ih (remaining c₂) hc₂_lt c₂ hc₂Level rfl hP₂
          exact qProperty_of_two_child_qProperties
            hnonpreleaf hc₁child hc₂child hcne hq₁ hq₂
  exact hmain (remaining u) u hlevel rfl hP

/-- If a contraction only merges the singleton `{u}` with another bag, then any
large child intersection present after the contraction was already present
before it. -/
theorem hasManyChildrenInPart_of_merge_singleton_parent_backward
    {k m : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hB : B ∈ P)
    (hlevel : u.1.val < bonnetDepresDepth k)
    (hQ :
      Q = insert (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B)
        ((P.erase ({Sum.inr u} : Finset (BonnetDepresVertex k))).erase B))
    (hmany : HasManyChildrenInPart Q u hlevel m) :
    HasManyChildrenInPart P u hlevel m := by
  classical
  rcases hmany with ⟨C, hC, hcard⟩
  subst Q
  rw [mem_merge_family_iff] at hC
  rcases hC with hmerge | ⟨hCP, _hCneParent, _hCneB⟩
  · refine ⟨B, hB, ?_⟩
    have hcard' := hcard
    rw [hmerge] at hcard'
    change m ≤
      ((({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B) ∩
        childVertexSet u hlevel).card at hcard'
    rwa [singleton_parent_union_inter_childVertexSet u hlevel B] at hcard'
  · exact ⟨C, hCP, hcard⟩

/-- Symmetric form of `hasManyChildrenInPart_of_merge_singleton_parent_backward`
for a merged bag written as `B ∪ {u}`. -/
theorem hasManyChildrenInPart_of_merge_singleton_parent_backward'
    {k m : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hB : B ∈ P)
    (hlevel : u.1.val < bonnetDepresDepth k)
    (hQ :
      Q = insert (B ∪ ({Sum.inr u} : Finset (BonnetDepresVertex k)))
        ((P.erase B).erase ({Sum.inr u} : Finset (BonnetDepresVertex k))))
    (hmany : HasManyChildrenInPart Q u hlevel m) :
    HasManyChildrenInPart P u hlevel m := by
  classical
  have hQ' :
      Q = insert (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B)
        ((P.erase ({Sum.inr u} : Finset (BonnetDepresVertex k))).erase B) := by
    rw [hQ, Finset.union_comm]
    congr 1
    ext C
    by_cases hCu : C = ({Sum.inr u} : Finset (BonnetDepresVertex k))
    · subst C
      by_cases hBu : B = ({Sum.inr u} : Finset (BonnetDepresVertex k))
      · subst B
        simp
      · simp
    · by_cases hCB : C = B
      · subst C
        simp [hCu]
      · simp [hCu, hCB]
  exact hasManyChildrenInPart_of_merge_singleton_parent_backward hB hlevel hQ' hmany

/-- Claim-15 single-step form.  If `Q` is obtained from `P` by merging the
singleton `{u}` with a different bag `B`, and the next partition still satisfies
the root-child singleton hypotheses, then `u` already has property `P` in `P`. -/
theorem hasManyChildrenInPart_before_merge_singleton_parent
    {k d : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hpartP : IsBagPartition P)
    (hpartQ : IsBagPartition Q)
    (hrootQ : RootChildrenSingleton Q)
    (hredQ : PartitionRedDegreeAtMost (bonnetDepresGraph k) Q d)
    (hsingleP : ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ P)
    (hB : B ∈ P)
    (hBne : B ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)))
    (hlevel : u.1.val < bonnetDepresDepth k)
    (hQ :
      Q = insert (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B)
        ((P.erase ({Sum.inr u} : Finset (BonnetDepresVertex k))).erase B)) :
    HasManyChildrenInPart P u hlevel (manyChildrenThreshold k) := by
  classical
  let A : Finset (BonnetDepresVertex k) :=
    ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B
  have hA : A ∈ Q := by
    rw [hQ]
    exact Finset.mem_insert_self _ _
  have huA : (Sum.inr u : BonnetDepresVertex k) ∈ A := by
    simp [A]
  have hnotSingleton : A ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
    intro hAeq
    rcases hpartP.1 hB with ⟨b, hbB⟩
    have hbA : b ∈ A := by
      simp [A, hbB]
    have hbSingleton : b ∈ ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
      simpa [hAeq] using hbA
    have hbNotSingleton :
        b ∉ ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
      exact (Finset.disjoint_left.mp
        (hpartP.2.1 hB hsingleP hBne)) hbB
    exact hbNotSingleton hbSingleton
  have hmanyQ :
      HasManyChildrenInPart Q u hlevel (manyChildrenThreshold k) :=
    hasManyChildrenInPart_of_nonSingleton_tree_bag_of_rootChildrenSingleton
      (k := k) (d := d) (P := Q) (A := A) (u := u)
      hd hpartQ hrootQ hredQ hA huA hnotSingleton hlevel
  exact hasManyChildrenInPart_of_merge_singleton_parent_backward hB hlevel hQ hmanyQ

/-- Variant of Claim 15 for a singleton tree vertex merged with a bag already
containing another tree vertex.  This version does not require the next state to
keep all root children singleton. -/
theorem hasManyChildrenInPart_before_merge_singleton_parent_with_tree_witness
    {k d : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hpartP : IsBagPartition P)
    (hpartQ : IsBagPartition Q)
    (hredQ : PartitionRedDegreeAtMost (bonnetDepresGraph k) Q d)
    (hsingleP : ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ P)
    (hB : B ∈ P)
    (hBne : B ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)))
    (hwB : (Sum.inr w : BonnetDepresVertex k) ∈ B)
    (hlevel : u.1.val < bonnetDepresDepth k)
    (hQ :
      Q = insert (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B)
        ((P.erase ({Sum.inr u} : Finset (BonnetDepresVertex k))).erase B)) :
    HasManyChildrenInPart P u hlevel (manyChildrenThreshold k) := by
  classical
  let A : Finset (BonnetDepresVertex k) :=
    ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B
  have hA : A ∈ Q := by
    rw [hQ]
    exact Finset.mem_insert_self _ _
  have huA : (Sum.inr u : BonnetDepresVertex k) ∈ A := by
    simp [A]
  have hwA : (Sum.inr w : BonnetDepresVertex k) ∈ A := by
    simp [A, hwB]
  have hwu : w ≠ u := by
    intro hwu
    subst w
    have hdis := hpartP.2.1 hB hsingleP hBne
    exact (Finset.disjoint_left.mp hdis) hwB (by simp)
  have hmanyQ :
      HasManyChildrenInPart Q u hlevel (manyChildrenThreshold k) :=
    hasManyChildrenInPart_of_two_tree_vertices_of_redDegreeAtMost
      (k := k) (d := d) (P := Q) (A := A) (u := u) (w := w)
      hd hpartQ hredQ hA huA hwA hwu hlevel
  exact hasManyChildrenInPart_of_merge_singleton_parent_backward hB hlevel hQ hmanyQ

/-- Symmetric version of
`hasManyChildrenInPart_before_merge_singleton_parent_with_tree_witness`. -/
theorem hasManyChildrenInPart_before_merge_tree_witness_with_singleton_parent
    {k d : ℕ} {P Q : Finset (Finset (BonnetDepresVertex k))}
    {B : Finset (BonnetDepresVertex k)}
    {u w : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hpartP : IsBagPartition P)
    (hpartQ : IsBagPartition Q)
    (hredQ : PartitionRedDegreeAtMost (bonnetDepresGraph k) Q d)
    (hsingleP : ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ P)
    (hB : B ∈ P)
    (hBne : B ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)))
    (hwB : (Sum.inr w : BonnetDepresVertex k) ∈ B)
    (hlevel : u.1.val < bonnetDepresDepth k)
    (hQ :
      Q = insert (B ∪ ({Sum.inr u} : Finset (BonnetDepresVertex k)))
        ((P.erase B).erase ({Sum.inr u} : Finset (BonnetDepresVertex k)))) :
    HasManyChildrenInPart P u hlevel (manyChildrenThreshold k) := by
  classical
  have hQ' :
      Q = insert (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B)
        ((P.erase ({Sum.inr u} : Finset (BonnetDepresVertex k))).erase B) := by
    rw [hQ, Finset.union_comm]
    congr 1
    ext C
    by_cases hCu : C = ({Sum.inr u} : Finset (BonnetDepresVertex k))
    · subst C
      by_cases hBu : B = ({Sum.inr u} : Finset (BonnetDepresVertex k))
      · subst B
        simp
      · simp
    · by_cases hCB : C = B
      · subst C
        simp [hCu]
      · simp [hCu, hCB]
  exact hasManyChildrenInPart_before_merge_singleton_parent_with_tree_witness
    (k := k) (d := d) (P := P) (Q := Q) (B := B) (u := u) (w := w)
    hd hpartP hpartQ hredQ hsingleP hB hBne hwB hlevel hQ'

/-- Claim 14 specialized to an actual contraction-sequence state. -/
theorem ContractionSequence.hasManyChildrenInPart_of_nonSingleton_tree_bag
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i ≤ S.stepCount)
    {A : Finset (BonnetDepresVertex k)}
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hd : d ≤ 2 ^ k)
    (hroot : RootChildrenSingleton (S.state i).bags)
    (hA : A ∈ (S.state i).bags)
    (huA : (Sum.inr u : BonnetDepresVertex k) ∈ A)
    (hnotSingleton : A ≠ {Sum.inr u})
    (hlevel : u.1.val < bonnetDepresDepth k) :
    HasManyChildrenInPart (S.state i).bags u hlevel (manyChildrenThreshold k) :=
  hasManyChildrenInPart_of_nonSingleton_tree_bag_of_rootChildrenSingleton
    (k := k) (d := d) (P := (S.state i).bags) (A := A) (u := u)
    hd (_root_.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
    hroot (_root_.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state S hi)
    hA huA hnotSingleton hlevel

/-- Claim 16 specialized to an actual contraction-sequence state. -/
theorem ContractionSequence.hasManyPChildren_of_hasManyChildrenInPart_of_nonpreleaf
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i ≤ S.stepCount)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : u.1.val < bonnetDepresDepth k}
    (hd : d ≤ 2 ^ k)
    (hroot : RootChildrenSingleton (S.state i).bags)
    (hP :
      HasManyChildrenInPart (S.state i).bags u hlevel (manyChildrenThreshold k))
    (hnonpreleaf : IsNonPreleafInternal u) :
    HasManyPChildren (S.state i).bags u hlevel (manyChildrenThreshold k) :=
  _root_.TwinWidth.SimpleGraph.BonnetDepres.hasManyPChildren_of_hasManyChildrenInPart_of_nonpreleaf
    (k := k) (d := d) (P := (S.state i).bags) (u := u) (hlevel := hlevel)
    hd (_root_.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
    hroot (_root_.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state S hi)
    hP hnonpreleaf

/-- Claim 17 specialized to an actual contraction-sequence state. -/
theorem ContractionSequence.qProperty_of_hasManyChildrenInPart
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i ≤ S.stepCount)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hd : d ≤ 2 ^ k)
    (hroot : RootChildrenSingleton (S.state i).bags)
    (hP :
      HasManyChildrenInPart (S.state i).bags u hlevel (manyChildrenThreshold k)) :
    QProperty (S.state i).bags u :=
  _root_.TwinWidth.SimpleGraph.BonnetDepres.qProperty_of_hasManyChildrenInPart
    (k := k) (d := d) (P := (S.state i).bags) (u := u) (hlevel := hlevel)
    hd (_root_.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
    hroot (_root_.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state S hi)
    hP

/-- Property `P` is monotone along one step of a contraction sequence. -/
theorem ContractionSequence.hasManyChildrenInPart_step
    {k d m : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i < S.stepCount)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hP :
      HasManyChildrenInPart (S.state i).bags u hlevel m) :
    HasManyChildrenInPart (S.state (i + 1)).bags u hlevel m :=
  hasManyChildrenInPart_mono_of_isBagContraction
    (_root_.TwinWidth.SimpleGraph.IsContractionStep.isBagContraction
      (S.step_contracts i hi)) hP

/-- Property `Q` is monotone along one step of a contraction sequence. -/
theorem ContractionSequence.qProperty_step
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i < S.stepCount)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ : QProperty (S.state i).bags u) :
    QProperty (S.state (i + 1)).bags u :=
  qProperty_mono_of_isBagContraction
    (_root_.TwinWidth.SimpleGraph.IsContractionStep.isBagContraction
      (S.step_contracts i hi)) hQ

/-- Property `P` is monotone along any later state of a contraction sequence. -/
theorem ContractionSequence.hasManyChildrenInPart_mono
    {k d m : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ S.stepCount)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {hlevel : IsInternal u}
    (hP :
      HasManyChildrenInPart (S.state i).bags u hlevel m) :
    HasManyChildrenInPart (S.state j).bags u hlevel m := by
  induction hij with
  | refl =>
      exact hP
  | @step n hij ih =>
      have hnle : n ≤ S.stepCount := Nat.le_trans (Nat.le_succ n) hj
      have hprev :
          HasManyChildrenInPart (S.state n).bags u hlevel m := ih hnle
      exact
        _root_.TwinWidth.SimpleGraph.BonnetDepres.ContractionSequence.hasManyChildrenInPart_step
          S (Nat.lt_of_succ_le hj) hprev

/-- Property `Q` is monotone along any later state of a contraction sequence. -/
theorem ContractionSequence.qProperty_mono
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ S.stepCount)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ : QProperty (S.state i).bags u) :
    QProperty (S.state j).bags u := by
  induction hij with
  | refl =>
      exact hQ
  | @step n hij ih =>
      have hnle : n ≤ S.stepCount := Nat.le_trans (Nat.le_succ n) hj
      have hprev : QProperty (S.state n).bags u := ih hnle
      exact
        _root_.TwinWidth.SimpleGraph.BonnetDepres.ContractionSequence.qProperty_step
          S (Nat.lt_of_succ_le hj) hprev

/-- At time zero, every root child is still a singleton bag. -/
theorem ContractionSequence.rootChildrenSingleton_zero
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    RootChildrenSingleton (S.state 0).bags := by
  have hbags :
      (S.state 0).bags = TrigraphState.singletonBags (BonnetDepresVertex k) :=
    S.starts.1
  simp [hbags, rootChildrenSingleton_singletonBags k]

/-- At the final state of a contraction sequence, not all root children can still
be singleton bags. -/
theorem ContractionSequence.not_rootChildrenSingleton_final
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ¬ RootChildrenSingleton (S.state S.stepCount).bags :=
  not_rootChildrenSingleton_of_card_le_one S.ends

/-- Some state of every contraction sequence has lost the root-child singleton
invariant: the final state is enough. -/
theorem ContractionSequence.exists_not_rootChildrenSingleton
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ∃ i : ℕ, ¬ RootChildrenSingleton (S.state i).bags :=
  ⟨S.stepCount, ContractionSequence.not_rootChildrenSingleton_final S⟩

/-- The first time at which not all root children are singleton bags. -/
noncomputable def ContractionSequence.firstRootChildrenNonSingletonIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) : ℕ := by
  classical
  exact Nat.find (ContractionSequence.exists_not_rootChildrenSingleton S)

theorem ContractionSequence.not_rootChildrenSingleton_first
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ¬ RootChildrenSingleton
      (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags := by
  classical
  unfold ContractionSequence.firstRootChildrenNonSingletonIndex
  exact Nat.find_spec (ContractionSequence.exists_not_rootChildrenSingleton S)

theorem ContractionSequence.rootChildrenSingleton_before_first
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    {i : ℕ} (hi : i < ContractionSequence.firstRootChildrenNonSingletonIndex S) :
    RootChildrenSingleton (S.state i).bags := by
  classical
  by_contra hnot
  unfold ContractionSequence.firstRootChildrenNonSingletonIndex at hi
  exact Nat.find_min (ContractionSequence.exists_not_rootChildrenSingleton S) hi hnot

theorem ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ContractionSequence.firstRootChildrenNonSingletonIndex S ≤ S.stepCount := by
  classical
  unfold ContractionSequence.firstRootChildrenNonSingletonIndex
  exact Nat.find_min' (ContractionSequence.exists_not_rootChildrenSingleton S)
    (ContractionSequence.not_rootChildrenSingleton_final S)

theorem ContractionSequence.firstRootChildrenNonSingletonIndex_pos
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    0 < ContractionSequence.firstRootChildrenNonSingletonIndex S := by
  by_contra hpos
  have hzero : ContractionSequence.firstRootChildrenNonSingletonIndex S = 0 := by omega
  have hnot := ContractionSequence.not_rootChildrenSingleton_first S
  have hroot := ContractionSequence.rootChildrenSingleton_zero S
  rw [hzero] at hnot
  exact hnot hroot

/-- The predecessor of the first failed root-child-singleton state still has
all root children singleton. -/
theorem ContractionSequence.rootChildrenSingleton_before_first_pred
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    RootChildrenSingleton
      (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags := by
  apply ContractionSequence.rootChildrenSingleton_before_first
  have hpos := ContractionSequence.firstRootChildrenNonSingletonIndex_pos S
  omega

/-- The predecessor of the first failed root-child-singleton state is a genuine
contraction step. -/
theorem ContractionSequence.first_pred_lt_stepCount
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 < S.stepCount := by
  have hpos := ContractionSequence.firstRootChildrenNonSingletonIndex_pos S
  have hle := ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
  omega

theorem ContractionSequence.first_pred_succ
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 + 1 =
      ContractionSequence.firstRootChildrenNonSingletonIndex S := by
  have hpos := ContractionSequence.firstRootChildrenNonSingletonIndex_pos S
  omega

/-- Claim-15 sequence form.  Before the first root-child contraction, if an
internal tree vertex is no longer a singleton part, then it already satisfied
property `P` at some earlier state. -/
theorem ContractionSequence.exists_hasManyChildrenInPart_before_of_not_tree_singleton
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {i : ℕ}
    (hi : i < ContractionSequence.firstRootChildrenNonSingletonIndex S)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : IsInternal u)
    (hnotSingleton :
      ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∉ (S.state i).bags) :
    ∃ j < i,
      HasManyChildrenInPart (S.state j).bags u hlevel (manyChildrenThreshold k) := by
  classical
  let U : Finset (BonnetDepresVertex k) := {Sum.inr u}
  have hex : ∃ t : ℕ, t ≤ i ∧ U ∉ (S.state t).bags :=
    ⟨i, le_rfl, by simpa [U] using hnotSingleton⟩
  let t := Nat.find hex
  have ht_spec : t ≤ i ∧ U ∉ (S.state t).bags := by
    simpa [t] using Nat.find_spec hex
  have hstart : U ∈ (S.state 0).bags := by
    rw [S.starts.1]
    exact Finset.mem_image.mpr ⟨Sum.inr u, by simp, by simp [U]⟩
  have ht_pos : 0 < t := by
    by_contra hnot
    have ht0 : t = 0 := by omega
    exact ht_spec.2 (by simpa [ht0] using hstart)
  let p := t - 1
  have hp_succ : p + 1 = t := by
    have := ht_pos
    omega
  have hp_lt_i : p < i := by
    have := ht_spec.1
    omega
  have hp_singleton : U ∈ (S.state p).bags := by
    by_contra hpnot
    have hp_lt_t : p < t := by
      have := ht_pos
      omega
    have hp_le_i : p ≤ i := le_of_lt hp_lt_i
    exact (Nat.find_min hex hp_lt_t) ⟨hp_le_i, hpnot⟩
  have hp_lt_step : p < S.stepCount := by
    have hfirst_le :=
      ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
    omega
  rcases S.step_contracts p hp_lt_step with
    ⟨A, hA, B, hB, hAB, hbags, _hredStep, _hblackStep⟩
  have hnext_not : U ∉ (S.state (p + 1)).bags := by
    simpa [hp_succ] using ht_spec.2
  have hside : A = U ∨ B = U := by
    by_contra hno
    have hAU : A ≠ U := by
      intro h
      exact hno (Or.inl h)
    have hBU : B ≠ U := by
      intro h
      exact hno (Or.inr h)
    have hmem_next : U ∈ (S.state (p + 1)).bags := by
      rw [hbags, mem_merge_family_iff]
      right
      exact ⟨hp_singleton, hAU.symm, hBU.symm⟩
    exact hnext_not hmem_next
  have hrootNext :
      RootChildrenSingleton (S.state (p + 1)).bags :=
    ContractionSequence.rootChildrenSingleton_before_first S (by omega)
  have hpartP : IsBagPartition (S.state p).bags :=
    _root_.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state p)
  have hpartQ : IsBagPartition (S.state (p + 1)).bags :=
    _root_.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state (p + 1))
  have hredQ :
      PartitionRedDegreeAtMost (bonnetDepresGraph k) (S.state (p + 1)).bags d :=
    _root_.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state
      S (by
        have hfirst_le :=
          ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
        omega)
  rcases hside with hAU | hBU
  · refine ⟨p, hp_lt_i, ?_⟩
    have hBne : B ≠ U := by
      intro hBU
      exact hAB (by rw [hAU, hBU])
    have hQ :
        (S.state (p + 1)).bags =
          insert (U ∪ B) (((S.state p).bags.erase U).erase B) := by
      simpa [U, hAU] using hbags
    exact hasManyChildrenInPart_before_merge_singleton_parent
      (k := k) (d := d) (P := (S.state p).bags)
      (Q := (S.state (p + 1)).bags) (B := B) (u := u)
      hd hpartP hpartQ hrootNext hredQ
      (by simpa [U] using hp_singleton) hB (by simpa [U] using hBne)
      hlevel hQ
  · refine ⟨p, hp_lt_i, ?_⟩
    have hAne : A ≠ U := by
      intro hAU
      exact hAB (by rw [hAU, hBU])
    have hQ :
        (S.state (p + 1)).bags =
          insert (U ∪ A) (((S.state p).bags.erase U).erase A) := by
      rw [hbags, hBU, Finset.union_comm]
      congr 1
      ext C
      by_cases hCU : C = U
      · subst C
        by_cases hAU' : A = U
        · subst A
          simp
        · simp
      · by_cases hCA : C = A
        · subst C
          simp [hCU]
        · simp [hCU, hCA]
    exact hasManyChildrenInPart_before_merge_singleton_parent
      (k := k) (d := d) (P := (S.state p).bags)
      (Q := (S.state (p + 1)).bags) (B := A) (u := u)
      hd hpartP hpartQ hrootNext hredQ
      (by simpa [U] using hp_singleton) hA (by simpa [U] using hAne)
      hlevel hQ

/-- In the first step where the root-child singleton invariant fails, one of the
two merged bags is a root-child singleton bag. -/
theorem ContractionSequence.exists_rootChildBag_in_first_failed_step
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) :
    ∃ A ∈ (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags,
      ∃ B ∈ (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags,
        A ≠ B ∧
          (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags =
            insert (A ∪ B)
              (((S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags.erase A).erase B) ∧
          ∃ f : Fin (bonnetDepresApexCount k) → Bool,
            A = rootChildBag k f ∨ B = rootChildBag k f := by
  classical
  let i := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
  have hi : i < S.stepCount := ContractionSequence.first_pred_lt_stepCount S
  have hisucc :
      i + 1 = ContractionSequence.firstRootChildrenNonSingletonIndex S := by
    simpa [i] using ContractionSequence.first_pred_succ S
  rcases S.step_contracts i hi with
    ⟨A, hA, B, hB, hAB, hbags, _hred, _hblack⟩
  refine ⟨A, hA, B, hB, hAB, ?_, ?_⟩
  · simpa [i, hisucc] using hbags
  · by_contra hno
    have hAnot : ∀ f : Fin (bonnetDepresApexCount k) → Bool, A ≠ rootChildBag k f := by
      intro f hAf
      exact hno ⟨f, Or.inl hAf⟩
    have hBnot : ∀ f : Fin (bonnetDepresApexCount k) → Bool, B ≠ rootChildBag k f := by
      intro f hBf
      exact hno ⟨f, Or.inr hBf⟩
    have hrootPrev :
        RootChildrenSingleton
          (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags :=
      ContractionSequence.rootChildrenSingleton_before_first_pred S
    have hrootNext :
        RootChildrenSingleton (S.state (i + 1)).bags := by
      rw [hbags]
      exact rootChildrenSingleton_merge_of_not_rootChildBag
        (by simpa [i] using hrootPrev) hAnot hBnot
    have hnotFirst := ContractionSequence.not_rootChildrenSingleton_first S
    rw [← hisucc] at hnotFirst
    exact hnotFirst hrootNext

/-- At the last state before the first contraction involving a root child, some
root child already satisfies property `P`. -/
theorem ContractionSequence.exists_rootChild_hasManyChildrenInPart_before_first
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ f : Fin (bonnetDepresApexCount k) → Bool,
      HasManyChildrenInPart
        (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags
        (rootChildWithNeighborhood k f)
        (rootChildWithNeighborhood_isInternal k f)
        (manyChildrenThreshold k) := by
  classical
  let i := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
  have hfirst_le :
      ContractionSequence.firstRootChildrenNonSingletonIndex S ≤ S.stepCount :=
    ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
  have hprevRoot :
      RootChildrenSingleton (S.state i).bags := by
    simpa [i] using ContractionSequence.rootChildrenSingleton_before_first_pred S
  have hpartPrev : IsBagPartition (S.state i).bags :=
    _root_.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i)
  have hpartFirst :
      IsBagPartition (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags :=
    _root_.TwinWidth.SimpleGraph.TrigraphState.isBagPartition
      (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S))
  have hredFirst :
      PartitionRedDegreeAtMost (bonnetDepresGraph k)
        (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags d :=
    _root_.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state
      S hfirst_le
  rcases ContractionSequence.exists_rootChildBag_in_first_failed_step S with
    ⟨A, hA, B, hB, hAB, hbags, hrootSide⟩
  rcases hrootSide with ⟨f₀, hAroot | hBroot⟩
  · let u := rootChildWithNeighborhood k f₀
    have hsingleP :
        ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ (S.state i).bags := by
      simpa [i, u, rootChildBag] using (by simpa [hAroot] using hA)
    have hBne : B ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
      intro hBroot'
      apply hAB
      rw [hAroot, hBroot']
      simp [u, rootChildBag]
    rcases hpartPrev.1 hB with ⟨z, hzB⟩
    cases z with
    | inl x =>
        exfalso
        have hQ :
            (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags =
              insert (rootChildBag k f₀ ∪ B)
                (((S.state i).bags.erase (rootChildBag k f₀)).erase B) := by
          simpa [i, hAroot] using hbags
        exact false_of_merge_rootChildBag_with_apex
          (k := k) (d := d) (P := (S.state i).bags)
          (Q := (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags)
          (B := B) (x := x) (f₀ := f₀)
          hd hprevRoot hredFirst hzB hQ
    | inr w =>
        refine ⟨f₀, ?_⟩
        have hQ :
            (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags =
              insert (({Sum.inr u} : Finset (BonnetDepresVertex k)) ∪ B)
                (((S.state i).bags.erase ({Sum.inr u} : Finset (BonnetDepresVertex k))).erase B) := by
          simpa [i, hAroot, u, rootChildBag] using hbags
        exact hasManyChildrenInPart_before_merge_singleton_parent_with_tree_witness
          (k := k) (d := d) (P := (S.state i).bags)
          (Q := (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags)
          (B := B) (u := u) (w := w)
          hd hpartPrev hpartFirst hredFirst hsingleP hB hBne hzB
          (rootChildWithNeighborhood_isInternal k f₀) hQ
  · let u := rootChildWithNeighborhood k f₀
    have hsingleP :
        ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ (S.state i).bags := by
      simpa [i, u, rootChildBag] using (by simpa [hBroot] using hB)
    have hAne : A ≠ ({Sum.inr u} : Finset (BonnetDepresVertex k)) := by
      intro hAroot'
      apply hAB
      rw [hAroot', hBroot]
      simp [u, rootChildBag]
    rcases hpartPrev.1 hA with ⟨z, hzA⟩
    cases z with
    | inl x =>
        exfalso
        have hQ :
            (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags =
              insert (A ∪ rootChildBag k f₀)
                (((S.state i).bags.erase A).erase (rootChildBag k f₀)) := by
          simpa [i, hBroot] using hbags
        exact false_of_merge_apex_with_rootChildBag
          (k := k) (d := d) (P := (S.state i).bags)
          (Q := (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags)
          (B := A) (x := x) (f₀ := f₀)
          hd hprevRoot hredFirst hzA hQ
    | inr w =>
        refine ⟨f₀, ?_⟩
        have hQ :
            (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags =
              insert (A ∪ ({Sum.inr u} : Finset (BonnetDepresVertex k)))
                (((S.state i).bags.erase A).erase ({Sum.inr u} : Finset (BonnetDepresVertex k))) := by
          simpa [i, hBroot, u, rootChildBag] using hbags
        exact hasManyChildrenInPart_before_merge_tree_witness_with_singleton_parent
          (k := k) (d := d) (P := (S.state i).bags)
          (Q := (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S)).bags)
          (B := A) (u := u) (w := w)
          hd hpartPrev hpartFirst hredFirst hsingleP hA hAne hzA
          (rootChildWithNeighborhood_isInternal k f₀) hQ

/-- At the last state before the first root-child contraction, some child of the
root satisfies property `Q`. -/
theorem ContractionSequence.exists_rootChild_qProperty_before_first
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ f : Fin (bonnetDepresApexCount k) → Bool,
      QProperty
        (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags
        (rootChildWithNeighborhood k f) := by
  classical
  let i := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
  have hi_le : i ≤ S.stepCount :=
    (ContractionSequence.first_pred_lt_stepCount S).le
  have hroot :
      RootChildrenSingleton (S.state i).bags := by
    simpa [i] using ContractionSequence.rootChildrenSingleton_before_first_pred S
  have hred :
      PartitionRedDegreeAtMost (bonnetDepresGraph k) (S.state i).bags d :=
    _root_.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state
      S hi_le
  rcases ContractionSequence.exists_rootChild_hasManyChildrenInPart_before_first
    S hd with ⟨f, hP⟩
  refine ⟨f, ?_⟩
  exact
    _root_.TwinWidth.SimpleGraph.BonnetDepres.qProperty_of_hasManyChildrenInPart
      (k := k) (d := d) (P := (S.state i).bags)
      (u := rootChildWithNeighborhood k f)
      (hlevel := rootChildWithNeighborhood_isInternal k f)
      hd (_root_.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
      hroot hred (by simpa [i] using hP)

/-- A state has a root child satisfying property `Q`. -/
def ContractionSequence.RootChildQAt {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d) (i : ℕ) : Prop :=
  ∃ f : Fin (bonnetDepresApexCount k) → Bool,
    QProperty (S.state i).bags (rootChildWithNeighborhood k f)

/-- The first state, before the first root-child contraction, in which a root
child satisfies `Q`. -/
noncomputable def ContractionSequence.firstRootChildQIndex {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) : ℕ :=
  by
    classical
    exact Nat.find (by
      let i := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
      rcases ContractionSequence.exists_rootChild_qProperty_before_first S hd with
        ⟨f, hQ⟩
      exact ⟨i, le_rfl, f, hQ⟩ :
        ∃ i : ℕ,
          i ≤ ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 ∧
            ContractionSequence.RootChildQAt S i)

theorem ContractionSequence.firstRootChildQIndex_le_before_first_pred {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ContractionSequence.firstRootChildQIndex S hd ≤
      ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 := by
  classical
  unfold ContractionSequence.firstRootChildQIndex
  exact (Nat.find_spec (by
    let i := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
    rcases ContractionSequence.exists_rootChild_qProperty_before_first S hd with
      ⟨f, hQ⟩
    exact ⟨i, le_rfl, f, hQ⟩ :
      ∃ i : ℕ,
        i ≤ ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 ∧
          ContractionSequence.RootChildQAt S i)).1

theorem ContractionSequence.rootChildQAt_firstRootChildQIndex {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ContractionSequence.RootChildQAt S
      (ContractionSequence.firstRootChildQIndex S hd) := by
  classical
  unfold ContractionSequence.firstRootChildQIndex
  exact (Nat.find_spec (by
    let i := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
    rcases ContractionSequence.exists_rootChild_qProperty_before_first S hd with
      ⟨f, hQ⟩
    exact ⟨i, le_rfl, f, hQ⟩ :
      ∃ i : ℕ,
        i ≤ ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 ∧
          ContractionSequence.RootChildQAt S i)).2

theorem ContractionSequence.not_rootChildQAt_before_firstRootChildQIndex {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {i : ℕ}
    (hi : i < ContractionSequence.firstRootChildQIndex S hd) :
    ¬ ContractionSequence.RootChildQAt S i := by
  classical
  intro hQ
  have hfirst_le :
      ContractionSequence.firstRootChildQIndex S hd ≤
        ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 :=
    ContractionSequence.firstRootChildQIndex_le_before_first_pred S hd
  have hi_bound :
      i ≤ ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 :=
    hi.le.trans hfirst_le
  unfold ContractionSequence.firstRootChildQIndex at hi
  exact (Nat.find_min (by
    let j := ContractionSequence.firstRootChildrenNonSingletonIndex S - 1
    rcases ContractionSequence.exists_rootChild_qProperty_before_first S hd with
      ⟨f, hQf⟩
    exact ⟨j, le_rfl, f, hQf⟩ :
      ∃ j : ℕ,
        j ≤ ContractionSequence.firstRootChildrenNonSingletonIndex S - 1 ∧
          ContractionSequence.RootChildQAt S j) hi) ⟨hi_bound, hQ⟩

/-- The first root-child-`Q` state is not the initial singleton-bag state. -/
theorem ContractionSequence.firstRootChildQIndex_pos {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    0 < ContractionSequence.firstRootChildQIndex S hd := by
  by_contra hnot
  have hzero : ContractionSequence.firstRootChildQIndex S hd = 0 := by omega
  have hQ :
      ContractionSequence.RootChildQAt S 0 := by
    simpa [hzero] using
      ContractionSequence.rootChildQAt_firstRootChildQIndex S hd
  rcases hQ with ⟨f, hQf⟩
  have hQsingleton :
      QProperty (TrigraphState.singletonBags (BonnetDepresVertex k))
        (rootChildWithNeighborhood k f) := by
    simpa [S.starts.1] using hQf
  exact not_rootChildQAt_singletonBags ⟨f, hQsingleton⟩

/-- If an internal node did not already have property `Q` immediately before the
first root-child-`Q` state, then its current part is still a singleton. -/
theorem ContractionSequence.treeVertex_singleton_of_not_qProperty_before_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hlevel : IsInternal u)
    (hnotPrev :
      ¬ QProperty
        (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags u) :
    ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈
      (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags := by
  classical
  by_contra hnotSingleton
  let i := ContractionSequence.firstRootChildQIndex S hd
  have hi_first : i < ContractionSequence.firstRootChildrenNonSingletonIndex S := by
    have hle := ContractionSequence.firstRootChildQIndex_le_before_first_pred S hd
    have hpos := ContractionSequence.firstRootChildrenNonSingletonIndex_pos S
    omega
  rcases ContractionSequence.exists_hasManyChildrenInPart_before_of_not_tree_singleton
      S hd hi_first hlevel (by simpa [i] using hnotSingleton) with
    ⟨j, hj_lt_i, hPj⟩
  have hi_pos : 0 < i := by
    simpa [i] using ContractionSequence.firstRootChildQIndex_pos S hd
  have hj_le_pred : j ≤ i - 1 := by omega
  have hpred_le_step : i - 1 ≤ S.stepCount := by
    have hfirst_le := ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
    omega
  have hPpred :
      HasManyChildrenInPart (S.state (i - 1)).bags u hlevel
        (manyChildrenThreshold k) :=
    _root_.TwinWidth.SimpleGraph.BonnetDepres.ContractionSequence.hasManyChildrenInPart_mono
      S hj_le_pred hpred_le_step hPj
  have hrootPred :
      RootChildrenSingleton (S.state (i - 1)).bags :=
    ContractionSequence.rootChildrenSingleton_before_first S (by omega)
  have hQpred :
      QProperty (S.state (i - 1)).bags u :=
    _root_.TwinWidth.SimpleGraph.BonnetDepres.ContractionSequence.qProperty_of_hasManyChildrenInPart
      S hpred_le_step hd hrootPred hPpred
  exact hnotPrev (by simpa [i] using hQpred)

/-- The first root-child-`Q` state still lies in the protected initial segment. -/
theorem ContractionSequence.rootChildrenSingleton_firstRootChildQIndex {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    RootChildrenSingleton
      (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags := by
  apply ContractionSequence.rootChildrenSingleton_before_first
  have hle :=
    ContractionSequence.firstRootChildQIndex_le_before_first_pred S hd
  have hpos := ContractionSequence.firstRootChildrenNonSingletonIndex_pos S
  omega

/-- At the first root-child-`Q` state, the witnessing root child has two
children satisfying `Q`. -/
theorem ContractionSequence.exists_two_child_qProperties_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ f : Fin (bonnetDepresApexCount k) → Bool,
      ∃ hlevel : IsInternal (rootChildWithNeighborhood k f),
        ∃ c₁ ∈ childSet (rootChildWithNeighborhood k f) hlevel,
          ∃ c₂ ∈ childSet (rootChildWithNeighborhood k f) hlevel,
            c₁ ≠ c₂ ∧
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags c₁ ∧
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags c₂ := by
  rcases ContractionSequence.rootChildQAt_firstRootChildQIndex S hd with
    ⟨f, hQ⟩
  rcases exists_two_child_qProperties_of_qProperty_nonpreleaf
      (rootChildWithNeighborhood_isNonPreleafInternal k f) hQ with
    ⟨hlevel, c₁, hc₁, c₂, hc₂, hcne, hQ₁, hQ₂⟩
  exact ⟨f, hlevel, c₁, hc₁, c₂, hc₂, hcne, hQ₁, hQ₂⟩

/-- At the first root-child-`Q` state, one child of the witnessing root child is
itself a new `Q` witness, while a distinct sibling already supplies the side
branch. -/
theorem ContractionSequence.exists_new_child_and_sibling_qProperty_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ f : Fin (bonnetDepresApexCount k) → Bool,
      ∃ hlevel : IsInternal (rootChildWithNeighborhood k f),
        ∃ v ∈ childSet (rootChildWithNeighborhood k f) hlevel,
          ∃ q ∈ childSet (rootChildWithNeighborhood k f) hlevel,
            v ≠ q ∧
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags v ∧
              ¬ QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags v ∧
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q ∧
              ({Sum.inr (rootChildWithNeighborhood k f)} :
                Finset (BonnetDepresVertex k)) ∈
                  (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  rcases ContractionSequence.exists_two_child_qProperties_firstRootChildQIndex S hd with
    ⟨f, hlevel, c₁, hc₁, c₂, hc₂, hcne, hQ₁, hQ₂⟩
  have hi_pos : 0 < i := by
    simpa [i] using ContractionSequence.firstRootChildQIndex_pos S hd
  have hnotBoth :
      ¬ (QProperty (S.state (i - 1)).bags c₁ ∧
        QProperty (S.state (i - 1)).bags c₂) := by
    rintro ⟨hQ₁prev, hQ₂prev⟩
    have hRootPrev :
        QProperty (S.state (i - 1)).bags (rootChildWithNeighborhood k f) :=
      qProperty_of_two_child_qProperties
        (rootChildWithNeighborhood_isNonPreleafInternal k f)
        hc₁ hc₂ hcne hQ₁prev hQ₂prev
    have hRootChildPrev : ContractionSequence.RootChildQAt S (i - 1) :=
      ⟨f, hRootPrev⟩
    exact
      (ContractionSequence.not_rootChildQAt_before_firstRootChildQIndex
        S hd (by omega : i - 1 < ContractionSequence.firstRootChildQIndex S hd))
        (by simpa [i] using hRootChildPrev)
  have hparentSingleton :
      ({Sum.inr (rootChildWithNeighborhood k f)} :
        Finset (BonnetDepresVertex k)) ∈ (S.state i).bags := by
    have hroot :=
      ContractionSequence.rootChildrenSingleton_firstRootChildQIndex S hd
    simpa [i] using hroot f
  by_cases hQ₁prev : QProperty (S.state (i - 1)).bags c₁
  · have hQ₂prev :
        ¬ QProperty (S.state (i - 1)).bags c₂ := by
      intro h
      exact hnotBoth ⟨hQ₁prev, h⟩
    refine ⟨f, hlevel, c₂, hc₂, c₁, hc₁, ?_, hQ₂, hQ₂prev, hQ₁, ?_⟩
    · exact hcne.symm
    · simpa [i] using hparentSingleton
  · refine ⟨f, hlevel, c₁, hc₁, c₂, hc₂, hcne, hQ₁, ?_, hQ₂, ?_⟩
    · simpa [i] using hQ₁prev
    · simpa [i] using hparentSingleton

/-- General first-state branching step: a non-preleaf internal node whose `Q`
appears for the first time at the first root-child-`Q` state has a new `Q` child
and a distinct `Q` sibling, and the node itself is still singleton. -/
theorem ContractionSequence.exists_new_child_and_sibling_qProperty_of_new_qProperty
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hnonpreleaf : IsNonPreleafInternal u)
    (hQ :
      QProperty (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags u)
    (hnotPrev :
      ¬ QProperty
        (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags u) :
    ∃ hlevel : IsInternal u,
      ∃ v ∈ childSet u hlevel,
        ∃ q ∈ childSet u hlevel,
          v ≠ q ∧
            QProperty
              (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags v ∧
            ¬ QProperty
              (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags v ∧
            QProperty
              (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q ∧
            ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈
              (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  rcases exists_two_child_qProperties_of_qProperty_nonpreleaf hnonpreleaf hQ with
    ⟨hlevel, c₁, hc₁, c₂, hc₂, hcne, hQ₁, hQ₂⟩
  have hnotBoth :
      ¬ (QProperty (S.state (i - 1)).bags c₁ ∧
        QProperty (S.state (i - 1)).bags c₂) := by
    rintro ⟨hQ₁prev, hQ₂prev⟩
    have hQprev :
        QProperty (S.state (i - 1)).bags u :=
      qProperty_of_two_child_qProperties hnonpreleaf hc₁ hc₂ hcne hQ₁prev hQ₂prev
    exact hnotPrev (by simpa [i] using hQprev)
  have hparentSingleton :
      ({Sum.inr u} : Finset (BonnetDepresVertex k)) ∈ (S.state i).bags := by
    exact
      ContractionSequence.treeVertex_singleton_of_not_qProperty_before_firstRootChildQIndex
        S hd (isNonPreleafInternal.isInternal hnonpreleaf) hnotPrev
  by_cases hQ₁prev : QProperty (S.state (i - 1)).bags c₁
  · have hQ₂prev :
        ¬ QProperty (S.state (i - 1)).bags c₂ := by
      intro h
      exact hnotBoth ⟨hQ₁prev, h⟩
    refine ⟨hlevel, c₂, hc₂, c₁, hc₁, ?_, hQ₂, ?_, hQ₁, ?_⟩
    · exact hcne.symm
    · simpa [i] using hQ₂prev
    · simpa [i] using hparentSingleton
  · refine ⟨hlevel, c₁, hc₁, c₂, hc₂, hcne, hQ₁, ?_, hQ₂, ?_⟩
    · simpa [i] using hQ₁prev
    · simpa [i] using hparentSingleton

/-- Claim-18 inductive core.  From a node whose `Q` first appears at the first
root-child-`Q` state, one can follow the newly appearing child and collect `n`
side branches satisfying `Q`; every collected side branch has a singleton parent
at that state. -/
theorem ContractionSequence.exists_sideBranchSet_of_new_qProperty
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ :
      QProperty (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags u)
    (hnotPrev :
      ¬ QProperty
        (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags u) :
    ∀ n : ℕ,
      n ≤ bonnetDepresDepth k - u.1.val - 1 →
        ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
          Qs.card = n ∧
            (∀ ⦃q⦄, q ∈ Qs →
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
            (∀ ⦃q⦄, q ∈ Qs →
              ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
                FullTreeNode.IsParent p q ∧
                  ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                    (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
            (∀ ⦃q⦄, q ∈ Qs → u.1.val < q.1.val) := by
  intro n
  induction n generalizing u with
  | zero =>
      intro _hn
      refine ⟨∅, by simp, ?_, ?_, ?_⟩
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
  | succ n ih =>
      intro hn
      have hnonpreleaf : IsNonPreleafInternal u := by
        unfold IsNonPreleafInternal
        omega
      rcases ContractionSequence.exists_new_child_and_sibling_qProperty_of_new_qProperty
          S hd hnonpreleaf hQ hnotPrev with
        ⟨hlevel, v, hvchild, q, hqchild, hvq, hQv, hnotPrevV, hQq, huSingleton⟩
      have hvLevel := level_eq_succ_of_mem_childSet hvchild
      have hqLevel := level_eq_succ_of_mem_childSet hqchild
      have hn_child : n ≤ bonnetDepresDepth k - v.1.val - 1 := by
        rw [hvLevel]
        omega
      rcases ih hQv hnotPrevV hn_child with
        ⟨Qs, hcard, hQmem, hparent, hlevel_gt⟩
      have hq_notMem : q ∉ Qs := by
        intro hqQs
        have hv_lt_qs := hlevel_gt hqQs
        rw [hqLevel, hvLevel] at hv_lt_qs
        omega
      refine ⟨insert q Qs, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hq_notMem, hcard]
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact hQq
        · exact hQmem hr
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact ⟨u, isParent_of_mem_childSet hqchild, huSingleton⟩
        · exact hparent hr
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · rw [hqLevel]
          omega
        · have hv_lt_r := hlevel_gt hr
          rw [hvLevel] at hv_lt_r
          omega

/-- Claim 18, without packaging the antichain relation: at the first
root-child-`Q` state there are `depth - 2` side-branch nodes satisfying `Q`,
each with a singleton parent. -/
theorem ContractionSequence.exists_sideBranchSet_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
      Qs.card = bonnetDepresDepth k - 2 ∧
        (∀ ⦃q⦄, q ∈ Qs →
          QProperty
            (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
        (∀ ⦃q⦄, q ∈ Qs →
          ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            FullTreeNode.IsParent p q ∧
              ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  rcases ContractionSequence.rootChildQAt_firstRootChildQIndex S hd with
    ⟨f, hQ⟩
  have hnotPrev :
      ¬ QProperty (S.state (i - 1)).bags (rootChildWithNeighborhood k f) := by
    intro hQprev
    have hRootChildPrev : ContractionSequence.RootChildQAt S (i - 1) :=
      ⟨f, hQprev⟩
    exact
      (ContractionSequence.not_rootChildQAt_before_firstRootChildQIndex
        S hd (by
          have hi_pos : 0 < i := by
            simpa [i] using ContractionSequence.firstRootChildQIndex_pos S hd
          omega : i - 1 < ContractionSequence.firstRootChildQIndex S hd))
        (by simpa [i] using hRootChildPrev)
  have hn :
      bonnetDepresDepth k - 2 ≤
        bonnetDepresDepth k - (rootChildWithNeighborhood k f).1.val - 1 := by
    rw [rootChildWithNeighborhood_level]
    have hdepth := two_lt_depth k
    omega
  rcases ContractionSequence.exists_sideBranchSet_of_new_qProperty
      S hd hQ (by simpa [i] using hnotPrev) (bonnetDepresDepth k - 2) hn with
    ⟨Qs, hcard, hQmem, hparent, _hlevel_gt⟩
  exact ⟨Qs, hcard, hQmem, hparent⟩

/-- Strengthened Claim-18 core: the collected side branches are descendants of
the starting node and form an ancestor-antichain. -/
theorem ContractionSequence.exists_antichain_sideBranchSet_of_new_qProperty
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ :
      QProperty (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags u)
    (hnotPrev :
      ¬ QProperty
        (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags u) :
    ∀ n : ℕ,
      n ≤ bonnetDepresDepth k - u.1.val - 1 →
        ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
          Qs.card = n ∧
            (∀ ⦃q⦄, q ∈ Qs →
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
            (∀ ⦃q⦄, q ∈ Qs →
              ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
                FullTreeNode.IsParent p q ∧
                  ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                    (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
            (∀ ⦃q⦄, q ∈ Qs → IsTreeAncestor u q) ∧
            (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
              ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) := by
  intro n
  induction n generalizing u with
  | zero =>
      intro _hn
      refine ⟨∅, by simp, ?_, ?_, ?_, ?_⟩
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · intro a ha
        simp at ha
  | succ n ih =>
      intro hn
      have hnonpreleaf : IsNonPreleafInternal u := by
        unfold IsNonPreleafInternal
        omega
      rcases ContractionSequence.exists_new_child_and_sibling_qProperty_of_new_qProperty
          S hd hnonpreleaf hQ hnotPrev with
        ⟨hlevel, v, hvchild, q, hqchild, hvq, hQv, hnotPrevV, hQq, huSingleton⟩
      have hvLevel := level_eq_succ_of_mem_childSet hvchild
      have hn_child : n ≤ bonnetDepresDepth k - v.1.val - 1 := by
        rw [hvLevel]
        omega
      rcases ih hQv hnotPrevV hn_child with
        ⟨Qs, hcard, hQmem, hparent, hdesc, hanti⟩
      have hq_notMem : q ∉ Qs := by
        intro hqQs
        exact not_isTreeAncestor_of_distinct_siblings
          hvchild hqchild hvq (hdesc hqQs) (isTreeAncestor_refl q)
      refine ⟨insert q Qs, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hq_notMem, hcard]
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact hQq
        · exact hQmem hr
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact ⟨u, isParent_of_mem_childSet hqchild, huSingleton⟩
        · exact hparent hr
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact isAncestor_of_mem_childSet hqchild
        · exact isTreeAncestor_trans (isAncestor_of_mem_childSet hvchild) (hdesc hr)
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with ha_eq | ha
        · rcases hb with hb_eq | hb
          · exact (hab (ha_eq.trans hb_eq.symm)).elim
          · constructor
            · intro hqb
              have hqb' : IsTreeAncestor q b := by
                simpa [ha_eq] using hqb
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq (hdesc hb) hqb'
            · intro hbq
              have hbq' : IsTreeAncestor b q := by
                simpa [ha_eq] using hbq
              have hvqAncestor : IsTreeAncestor v q :=
                isTreeAncestor_trans (hdesc hb) hbq'
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq hvqAncestor (isTreeAncestor_refl q)
        · rcases hb with hb_eq | hb
          · constructor
            · intro haq
              have haq' : IsTreeAncestor a q := by
                simpa [hb_eq] using haq
              have hvqAncestor : IsTreeAncestor v q :=
                isTreeAncestor_trans (hdesc ha) haq'
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq hvqAncestor (isTreeAncestor_refl q)
            · intro hqa
              have hqa' : IsTreeAncestor q a := by
                simpa [hb_eq] using hqa
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq (hdesc ha) hqa'
          · exact hanti ha hb hab

/-- Claim 18 with the ancestor-antichain property recorded explicitly. -/
theorem ContractionSequence.exists_antichain_sideBranchSet_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
      Qs.card = bonnetDepresDepth k - 2 ∧
        (∀ ⦃q⦄, q ∈ Qs →
          QProperty
            (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
        (∀ ⦃q⦄, q ∈ Qs →
          ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            FullTreeNode.IsParent p q ∧
              ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
        (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
          ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  rcases ContractionSequence.rootChildQAt_firstRootChildQIndex S hd with
    ⟨f, hQ⟩
  have hnotPrev :
      ¬ QProperty (S.state (i - 1)).bags (rootChildWithNeighborhood k f) := by
    intro hQprev
    have hRootChildPrev : ContractionSequence.RootChildQAt S (i - 1) :=
      ⟨f, hQprev⟩
    exact
      (ContractionSequence.not_rootChildQAt_before_firstRootChildQIndex
        S hd (by
          have hi_pos : 0 < i := by
            simpa [i] using ContractionSequence.firstRootChildQIndex_pos S hd
          omega : i - 1 < ContractionSequence.firstRootChildQIndex S hd))
        (by simpa [i] using hRootChildPrev)
  have hn :
      bonnetDepresDepth k - 2 ≤
        bonnetDepresDepth k - (rootChildWithNeighborhood k f).1.val - 1 := by
    rw [rootChildWithNeighborhood_level]
    have hdepth := two_lt_depth k
    omega
  rcases ContractionSequence.exists_antichain_sideBranchSet_of_new_qProperty
      S hd hQ (by simpa [i] using hnotPrev) (bonnetDepresDepth k - 2) hn with
    ⟨Qs, hcard, hQmem, hparent, _hdesc, hanti⟩
  exact ⟨Qs, hcard, hQmem, hparent, hanti⟩

/-- Strengthened Claim-18 core with the level ranking kept: collected side
branches are descendants of the starting node, form an ancestor-antichain, and
have pairwise distinct levels. -/
theorem ContractionSequence.exists_ranked_antichain_sideBranchSet_of_new_qProperty
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {u : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ :
      QProperty (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags u)
    (hnotPrev :
      ¬ QProperty
        (S.state (ContractionSequence.firstRootChildQIndex S hd - 1)).bags u) :
    ∀ n : ℕ,
      n ≤ bonnetDepresDepth k - u.1.val - 1 →
        ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
          Qs.card = n ∧
            (∀ ⦃q⦄, q ∈ Qs →
              QProperty
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
            (∀ ⦃q⦄, q ∈ Qs →
              ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
                FullTreeNode.IsParent p q ∧
                  ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                    (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
            (∀ ⦃q⦄, q ∈ Qs → IsTreeAncestor u q) ∧
            (∀ ⦃q⦄, q ∈ Qs → u.1.val < q.1.val) ∧
            (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
              ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) ∧
            (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
              a.1.val ≠ b.1.val) := by
  intro n
  induction n generalizing u with
  | zero =>
      intro _hn
      refine ⟨∅, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · intro a ha
        simp at ha
      · intro a ha
        simp at ha
  | succ n ih =>
      intro hn
      have hnonpreleaf : IsNonPreleafInternal u := by
        unfold IsNonPreleafInternal
        omega
      rcases ContractionSequence.exists_new_child_and_sibling_qProperty_of_new_qProperty
          S hd hnonpreleaf hQ hnotPrev with
        ⟨hlevel, v, hvchild, q, hqchild, hvq, hQv, hnotPrevV, hQq, huSingleton⟩
      have hvLevel := level_eq_succ_of_mem_childSet hvchild
      have hqLevel := level_eq_succ_of_mem_childSet hqchild
      have hn_child : n ≤ bonnetDepresDepth k - v.1.val - 1 := by
        rw [hvLevel]
        omega
      rcases ih hQv hnotPrevV hn_child with
        ⟨Qs, hcard, hQmem, hparent, hdesc, hlevel_gt, hanti, hlevel_ne⟩
      have hq_notMem : q ∉ Qs := by
        intro hqQs
        exact not_isTreeAncestor_of_distinct_siblings
          hvchild hqchild hvq (hdesc hqQs) (isTreeAncestor_refl q)
      refine ⟨insert q Qs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hq_notMem, hcard]
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact hQq
        · exact hQmem hr
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact ⟨u, isParent_of_mem_childSet hqchild, huSingleton⟩
        · exact hparent hr
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · exact isAncestor_of_mem_childSet hqchild
        · exact isTreeAncestor_trans (isAncestor_of_mem_childSet hvchild) (hdesc hr)
      · intro r hr
        rw [Finset.mem_insert] at hr
        rcases hr with rfl | hr
        · rw [hqLevel]
          omega
        · have hv_lt_r := hlevel_gt hr
          rw [hvLevel] at hv_lt_r
          omega
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with ha_eq | ha
        · rcases hb with hb_eq | hb
          · exact (hab (ha_eq.trans hb_eq.symm)).elim
          · constructor
            · intro hqb
              have hqb' : IsTreeAncestor q b := by
                simpa [ha_eq] using hqb
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq (hdesc hb) hqb'
            · intro hbq
              have hbq' : IsTreeAncestor b q := by
                simpa [ha_eq] using hbq
              have hvqAncestor : IsTreeAncestor v q :=
                isTreeAncestor_trans (hdesc hb) hbq'
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq hvqAncestor (isTreeAncestor_refl q)
        · rcases hb with hb_eq | hb
          · constructor
            · intro haq
              have haq' : IsTreeAncestor a q := by
                simpa [hb_eq] using haq
              have hvqAncestor : IsTreeAncestor v q :=
                isTreeAncestor_trans (hdesc ha) haq'
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq hvqAncestor (isTreeAncestor_refl q)
            · intro hqa
              have hqa' : IsTreeAncestor q a := by
                simpa [hb_eq] using hqa
              exact not_isTreeAncestor_of_distinct_siblings
                hvchild hqchild hvq (hdesc ha) hqa'
          · exact hanti ha hb hab
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with ha_eq | ha
        · rcases hb with hb_eq | hb
          · exact (hab (ha_eq.trans hb_eq.symm)).elim
          · intro hlevels
            have hv_lt_b := hlevel_gt hb
            have hq_eq_b : q.1.val = b.1.val := by
              simpa [ha_eq] using hlevels
            rw [← hq_eq_b, hqLevel, hvLevel] at hv_lt_b
            omega
        · rcases hb with hb_eq | hb
          · intro hlevels
            have hv_lt_a := hlevel_gt ha
            have ha_eq_q : a.1.val = q.1.val := by
              simpa [hb_eq] using hlevels
            rw [ha_eq_q, hqLevel, hvLevel] at hv_lt_a
            omega
          · exact hlevel_ne ha hb hab

/-- Claim 18 with level separation recorded explicitly. -/
theorem ContractionSequence.exists_ranked_antichain_sideBranchSet_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
      Qs.card = bonnetDepresDepth k - 2 ∧
        (∀ ⦃q⦄, q ∈ Qs →
          QProperty
            (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
        (∀ ⦃q⦄, q ∈ Qs →
          ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            FullTreeNode.IsParent p q ∧
              ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
        (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
          ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) ∧
        (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
          a.1.val ≠ b.1.val) := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  rcases ContractionSequence.rootChildQAt_firstRootChildQIndex S hd with
    ⟨f, hQ⟩
  have hnotPrev :
      ¬ QProperty (S.state (i - 1)).bags (rootChildWithNeighborhood k f) := by
    intro hQprev
    have hRootChildPrev : ContractionSequence.RootChildQAt S (i - 1) :=
      ⟨f, hQprev⟩
    exact
      (ContractionSequence.not_rootChildQAt_before_firstRootChildQIndex
        S hd (by
          have hi_pos : 0 < i := by
            simpa [i] using ContractionSequence.firstRootChildQIndex_pos S hd
          omega : i - 1 < ContractionSequence.firstRootChildQIndex S hd))
        (by simpa [i] using hRootChildPrev)
  have hn :
      bonnetDepresDepth k - 2 ≤
        bonnetDepresDepth k - (rootChildWithNeighborhood k f).1.val - 1 := by
    rw [rootChildWithNeighborhood_level]
    have hdepth := two_lt_depth k
    omega
  rcases ContractionSequence.exists_ranked_antichain_sideBranchSet_of_new_qProperty
      S hd hQ (by simpa [i] using hnotPrev) (bonnetDepresDepth k - 2) hn with
    ⟨Qs, hcard, hQmem, hparent, _hdesc, _hlevel_gt, hanti, hlevel_ne⟩
  exact ⟨Qs, hcard, hQmem, hparent, hanti, hlevel_ne⟩

/-- Every side-branch `Q` node at the first root-child-`Q` state has a
descendant preleaf whose `P` witness is a large child bag. -/
theorem ContractionSequence.exists_descendant_preleaf_largeChildBag_of_qProperty
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {q : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hQ :
      QProperty (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) :
    ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
      IsTreeAncestor q v ∧ IsPreleaf v ∧
        ∃ hlevel : IsInternal v,
          ∃ A ∈ largeChildBags
              (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags,
            manyChildrenThreshold k ≤ (A ∩ childVertexSet v hlevel).card := by
  rcases exists_preleaf_descendant_hasManyChildrenInPart_of_qProperty hQ with
    ⟨v, hqv, hpre, hlevel, hP⟩
  rcases exists_largeChildBag_of_hasManyChildrenInPart hP with
    ⟨A, hA, hmany⟩
  exact ⟨v, hqv, hpre, hlevel, A, hA, hmany⟩

/-- Side branches whose descendant preleaf uses the fixed large bag `A` as its
large child-bag witness. -/
noncomputable def sideBranchesWitnessedByLargeBag {k : ℕ}
    (Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)))
    (A : Finset (BonnetDepresVertex k)) :
    Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) := by
  classical
  exact Qs.filter fun q =>
    ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
      IsTreeAncestor q v ∧ IsPreleaf v ∧
        ∃ hlevel : IsInternal v,
          manyChildrenThreshold k ≤ (A ∩ childVertexSet v hlevel).card

/-- A side branch witnessed by a fixed large bag is one of the original side
branches. -/
theorem sideBranchesWitnessedByLargeBag_subset {k : ℕ}
    {Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {A : Finset (BonnetDepresVertex k)} :
    sideBranchesWitnessedByLargeBag Qs A ⊆ Qs := by
  classical
  intro q hq
  rw [sideBranchesWitnessedByLargeBag, Finset.mem_filter] at hq
  exact hq.1

/-- Descendant choices from an ancestor-antichain are injective. -/
theorem descendant_choice_injective_of_antichain {k : ℕ}
    {Qs R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hRsubset : R ⊆ Qs)
    (hanti :
      ∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    {vOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (vOf q)) :
    Function.Injective vOf := by
  intro a b hv
  by_contra hne
  have hab_ne : a.1 ≠ b.1 := by
    intro h
    exact hne (Subtype.ext h)
  have hbdesc : IsTreeAncestor b.1 (vOf a) := by
    simpa [hv] using hdesc b
  have hcomp :=
    isTreeAncestor_or_isTreeAncestor_of_common_descendant
      (hdesc a) hbdesc
  have hanti_ab := hanti (hRsubset a.2) (hRsubset b.2) hab_ne
  rcases hcomp with hab | hba
  · exact hanti_ab.1 hab
  · exact hanti_ab.2 hba

/-- Parents of strict descendant choices from an ancestor-antichain are
injective. -/
theorem parent_choice_injective_of_antichain {k : ℕ}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    {zOf pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q))
    (hparent : ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q))
    (hstrict : ∀ q : {q // q ∈ R}, q.1.1.val < (zOf q).1.val) :
    Function.Injective pOf := by
  intro a b hpEq
  by_contra hne
  have hab_ne : a.1 ≠ b.1 := by
    intro h
    exact hne (Subtype.ext h)
  have hap : IsTreeAncestor a.1 (pOf a) :=
    isTreeAncestor_parent_of_strict_descendant
      (hdesc a) (hparent a) (hstrict a)
  have hbp : IsTreeAncestor b.1 (pOf a) := by
    simpa [hpEq] using
      isTreeAncestor_parent_of_strict_descendant
        (hdesc b) (hparent b) (hstrict b)
  have hcomp :=
    isTreeAncestor_or_isTreeAncestor_of_common_descendant hap hbp
  have hanti_ab := hanti a.2 b.2 hab_ne
  rcases hcomp with hab | hba
  · exact hanti_ab.1 hab
  · exact hanti_ab.2 hba

/-- Parent choices remain injective for a ranked antichain even when a selected
descendant is allowed to be the side-branch node itself.  The only additional
case would be two siblings with the same parent, and the ranked-level invariant
rules that out. -/
theorem parent_choice_injective_of_ranked_antichain {k : ℕ}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hlevel_ne :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b → a.1.val ≠ b.1.val)
    {zOf pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q))
    (hparent : ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q)) :
    Function.Injective pOf := by
  intro a b hpEq
  by_contra hne
  have hab_ne : a.1 ≠ b.1 := by
    intro h
    exact hne (Subtype.ext h)
  have hanti_ab := hanti a.2 b.2 hab_ne
  have hlevel_ab := hlevel_ne a.2 b.2 hab_ne
  by_cases ha_strict : a.1.1.val < (zOf a).1.val
  · have hap : IsTreeAncestor a.1 (pOf a) :=
      isTreeAncestor_parent_of_strict_descendant
        (hdesc a) (hparent a) ha_strict
    by_cases hb_strict : b.1.1.val < (zOf b).1.val
    · have hbp : IsTreeAncestor b.1 (pOf a) := by
        simpa [hpEq] using
          isTreeAncestor_parent_of_strict_descendant
            (hdesc b) (hparent b) hb_strict
      rcases isTreeAncestor_or_isTreeAncestor_of_common_descendant hap hbp with
        hab | hba
      · exact hanti_ab.1 hab
      · exact hanti_ab.2 hba
    · have hb_level : b.1.1.val = (zOf b).1.val := by
        rcases hdesc b with ⟨hle, _⟩
        omega
      have hb_eq_z : b.1 = zOf b :=
        eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
          (hdesc b) (isTreeAncestor_refl (zOf b)) hb_level
      have hpb : FullTreeNode.IsParent (pOf a) b.1 := by
        simpa [hpEq, hb_eq_z] using hparent b
      have hab : IsTreeAncestor a.1 b.1 :=
        isTreeAncestor_trans hap (isTreeAncestor_of_isParent hpb)
      exact hanti_ab.1 hab
  · have ha_level : a.1.1.val = (zOf a).1.val := by
      rcases hdesc a with ⟨hle, _⟩
      omega
    have ha_eq_z : a.1 = zOf a :=
      eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
        (hdesc a) (isTreeAncestor_refl (zOf a)) ha_level
    have hpa : FullTreeNode.IsParent (pOf a) a.1 := by
      simpa [ha_eq_z] using hparent a
    by_cases hb_strict : b.1.1.val < (zOf b).1.val
    · have hbp : IsTreeAncestor b.1 (pOf a) := by
        simpa [hpEq] using
          isTreeAncestor_parent_of_strict_descendant
            (hdesc b) (hparent b) hb_strict
      have hba : IsTreeAncestor b.1 a.1 :=
        isTreeAncestor_trans hbp (isTreeAncestor_of_isParent hpa)
      exact hanti_ab.2 hba
    · have hb_level : b.1.1.val = (zOf b).1.val := by
        rcases hdesc b with ⟨hle, _⟩
        omega
      have hb_eq_z : b.1 = zOf b :=
        eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
          (hdesc b) (isTreeAncestor_refl (zOf b)) hb_level
      have hpb : FullTreeNode.IsParent (pOf a) b.1 := by
        simpa [hpEq, hb_eq_z] using hparent b
      have hpa_level := FullTreeNode.isParent_level hpa
      have hpb_level := FullTreeNode.isParent_level hpb
      exact hlevel_ab (by omega)

/-- The ancestor-antichain property passes to subsets. -/
theorem antichain_mono {k : ℕ}
    {R R' : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hsubset : R' ⊆ R)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) :
    ∀ ⦃a⦄, a ∈ R' → ∀ ⦃b⦄, b ∈ R' → a ≠ b →
      ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a := by
  intro a ha b hb hab
  exact hanti (hsubset ha) (hsubset hb) hab

/-- If one part contains the parent choices for at least two antichain branches,
then it is a non-singleton internal-tree part. -/
theorem mem_internalNonSingletonTreeBags_of_antichain_parent_family {k : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {C : Finset (BonnetDepresVertex k)}
    (hC : C ∈ P)
    (hRcard : 1 < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    {zOf pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    (hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q))
    (hparent : ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q))
    (hstrict : ∀ q : {q // q ∈ R}, q.1.1.val < (zOf q).1.val)
    (hpC : ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ C) :
    C ∈ internalNonSingletonTreeBags P := by
  classical
  rcases Finset.one_lt_card.mp hRcard with ⟨a, ha, b, hb, hab⟩
  let qa : {q // q ∈ R} := ⟨a, ha⟩
  let qb : {q // q ∈ R} := ⟨b, hb⟩
  have hinj : Function.Injective pOf :=
    parent_choice_injective_of_antichain
      (k := k) (R := R) hanti
      (zOf := zOf) (pOf := pOf) hdesc hparent hstrict
  have hp_ne : pOf qa ≠ pOf qb := by
    intro hp_eq
    exact hab (Subtype.ext_iff.mp (hinj hp_eq))
  exact mem_internalNonSingletonTreeBags_of_two_tree_vertices
    (k := k) (P := P) (A := C) (u := pOf qa) (v := pOf qb)
    hC (parent_level_lt_depth_of_isParent (hparent qa)) (hpC qa) (hpC qb) hp_ne

/-- One Claim-19 induction step, isolated from the bookkeeping that chooses the
current descendants.  The selected parents all lie outside the current bag `B`,
so red-degree pigeonholing finds one red-neighbor part containing many of them;
that part is a non-singleton internal-tree part. -/
theorem exists_internalNonSingletonTreeBag_of_antichain_step {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    {zOf pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {COf : {q // q ∈ R} → Finset (BonnetDepresVertex k)}
    (hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q))
    (hBz : ∀ q : {q // q ∈ R}, (Sum.inr (zOf q) : BonnetDepresVertex k) ∈ B)
    (hparent : ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q))
    (hstrict : ∀ q : {q // q ∈ R}, q.1.1.val < (zOf q).1.val)
    (hCOfP : ∀ q : {q // q ∈ R}, COf q ∈ P)
    (hpC : ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ COf q)
    (hCneB : ∀ q : {q // q ∈ R}, COf q ≠ B) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      n < (R.attach.filter fun q => COf q = C).card := by
  classical
  let redNeighbors := P.filter fun C => partitionRedAdj (bonnetDepresGraph k) B C
  have hmaps :
      ∀ q ∈ R.attach, COf q ∈ redNeighbors := by
    intro q _hq
    rw [Finset.mem_filter]
    refine ⟨hCOfP q, ?_⟩
    apply partitionRedAdj_symm
    exact partitionRedAdj_of_antichain_family_parent_part
      (k := k) (R := R) (B := B) (C := COf q) (a := q.1) (p := pOf q)
      q.2 hRone hanti
      (fun r hr => zOf ⟨r, hr⟩)
      (fun r hr => hdesc ⟨r, hr⟩)
      (fun r hr => hBz ⟨r, hr⟩)
      (hparent q) (hstrict q) (hCneB q).symm (hpC q)
  have hredCard : redNeighbors.card ≤ d := by
    simpa [redNeighbors] using hred hB
  have hpigeonMul :
      redNeighbors.card * n < R.attach.card := by
    have hle : redNeighbors.card * n ≤ d * n :=
      Nat.mul_le_mul_right _ hredCard
    exact hle.trans_lt (by simpa using hmul)
  rcases Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := R.attach) (t := redNeighbors) (f := COf) (n := n)
      hmaps hpigeonMul with
    ⟨C, hC, hfiber⟩
  let fiber := R.attach.filter fun q => COf q = C
  have hfiberOne : 1 < fiber.card := hn.trans_lt (by simpa [fiber] using hfiber)
  rcases Finset.one_lt_card.mp hfiberOne with
    ⟨qa, hqa, qb, hqb, hqab⟩
  have hqaC : COf qa = C := (Finset.mem_filter.mp hqa).2
  have hqbC : COf qb = C := (Finset.mem_filter.mp hqb).2
  have hinj : Function.Injective pOf :=
    parent_choice_injective_of_antichain
      (k := k) (R := R) hanti
      (zOf := zOf) (pOf := pOf) hdesc hparent hstrict
  have hp_ne : pOf qa ≠ pOf qb := by
    intro hp_eq
    exact hqab (hinj hp_eq)
  have hCP : C ∈ P := (Finset.mem_filter.mp hC).1
  have hCinternal : C ∈ internalNonSingletonTreeBags P :=
    mem_internalNonSingletonTreeBags_of_two_tree_vertices
      (k := k) (P := P) (A := C) (u := pOf qa) (v := pOf qb)
      hCP (parent_level_lt_depth_of_isParent (hparent qa))
      (by simpa [hqaC] using hpC qa)
      (by simpa [hqbC] using hpC qb)
      hp_ne
  exact ⟨C, hCinternal, by simpa [fiber] using hfiber⟩

/-- Avoiding version of the abstract Claim-19 step. -/
theorem exists_internalNonSingletonTreeBag_of_antichain_step_avoiding {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (F : Finset (Finset (BonnetDepresVertex k)))
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    {zOf pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)}
    {COf : {q // q ∈ R} → Finset (BonnetDepresVertex k)}
    (hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q))
    (hBz : ∀ q : {q // q ∈ R}, (Sum.inr (zOf q) : BonnetDepresVertex k) ∈ B)
    (hparent : ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q))
    (hstrict : ∀ q : {q // q ∈ R}, q.1.1.val < (zOf q).1.val)
    (hCOfP : ∀ q : {q // q ∈ R}, COf q ∈ P)
    (hpC : ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ COf q)
    (hCneB : ∀ q : {q // q ∈ R}, COf q ≠ B)
    (havoid : ∀ q : {q // q ∈ R}, COf q ∉ F) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      C ∉ F ∧ n < (R.attach.filter fun q => COf q = C).card := by
  rcases exists_internalNonSingletonTreeBag_of_antichain_step
      (k := k) (d := d) (n := n) (P := P) (R := R) (B := B)
      hB hred hRone hn hmul hanti
      (zOf := zOf) (pOf := pOf) (COf := COf)
      hdesc hBz hparent hstrict hCOfP hpC hCneB with
    ⟨C, hCinternal, hfiber⟩
  have hfiberNonempty :
      (R.attach.filter fun q => COf q = C).Nonempty := by
    rw [← Finset.card_pos]
    exact (Nat.zero_le n).trans_lt hfiber
  rcases hfiberNonempty with ⟨q, hq⟩
  have hqC : COf q = C := (Finset.mem_filter.mp hq).2
  have hCnotF : C ∉ F := by
    intro hCF
    exact havoid q (by simpa [hqC] using hCF)
  exact ⟨C, hCinternal, hCnotF, hfiber⟩

/-- Concrete highest-descendant form of one Claim-19 step. -/
theorem exists_internalNonSingletonTreeBag_of_highestDescendant_step {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (hpart : IsBagPartition P)
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hnonempty :
      ∀ q : {q // q ∈ R}, (descendantsInBag B q.1).Nonempty)
    (hstrict :
      ∀ q : {q // q ∈ R},
        q.1.1.val < (highestDescendantInBag B q.1 (hnonempty q)).1.val) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      ∃ Rsub : Finset {q // q ∈ R},
        n < Rsub.card ∧
          ∀ q ∈ Rsub,
            (Sum.inr
              (highestParentInBag B q.1 (hnonempty q) (hstrict q)) :
                BonnetDepresVertex k) ∈ C := by
  classical
  let zOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => highestDescendantInBag B q.1 (hnonempty q)
  let pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => highestParentInBag B q.1 (hnonempty q) (hstrict q)
  let COf : {q // q ∈ R} → Finset (BonnetDepresVertex k) :=
    fun q => Classical.choose (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))
  have hCOfP : ∀ q : {q // q ∈ R}, COf q ∈ P := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).1
  have hpC :
      ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ COf q := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).2
  have hCneB : ∀ q : {q // q ∈ R}, COf q ≠ B := by
    intro q hEq
    have hp_notMem :
        (Sum.inr (pOf q) : BonnetDepresVertex k) ∉ B := by
      dsimp [pOf]
      exact parent_notMem_bag_of_highestDescendant
        (A := B) (q := q.1) (h := hnonempty q)
        (hp := highestParentInBag_isParent) (hstrict q)
    exact hp_notMem (by simpa [hEq] using hpC q)
  rcases exists_internalNonSingletonTreeBag_of_antichain_step
      (k := k) (d := d) (n := n) (P := P) (R := R) (B := B)
      hB hred hRone hn hmul hanti
      (zOf := zOf) (pOf := pOf) (COf := COf)
      (by intro q; exact highestDescendantInBag_isAncestor (hnonempty q))
      (by intro q; exact highestDescendantInBag_mem_bag (hnonempty q))
      (by intro q; exact highestParentInBag_isParent)
      (by intro q; exact hstrict q)
      hCOfP hpC hCneB with
    ⟨C, hCinternal, hfiber⟩
  let Rsub := R.attach.filter fun q => COf q = C
  refine ⟨C, hCinternal, Rsub, by simpa [Rsub] using hfiber, ?_⟩
  intro q hq
  have hqC : COf q = C := (Finset.mem_filter.mp hq).2
  simpa [pOf, hqC] using hpC q

/-- Highest-descendant step with an explicit finite set of previously used bags
to avoid. -/
theorem exists_internalNonSingletonTreeBag_of_highestDescendant_step_avoiding
    {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (F : Finset (Finset (BonnetDepresVertex k)))
    (hpart : IsBagPartition P)
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hnonempty :
      ∀ q : {q // q ∈ R}, (descendantsInBag B q.1).Nonempty)
    (hstrict :
      ∀ q : {q // q ∈ R},
        q.1.1.val < (highestDescendantInBag B q.1 (hnonempty q)).1.val)
    (havoidParentParts :
      ∀ q : {q // q ∈ R},
        Classical.choose
          (hpart.2.2
            (Sum.inr
              (highestParentInBag B q.1 (hnonempty q) (hstrict q)) :
                BonnetDepresVertex k)) ∉ F) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      C ∉ F ∧
        ∃ Rsub : Finset {q // q ∈ R},
          n < Rsub.card ∧
            ∀ q ∈ Rsub,
              (Sum.inr
                (highestParentInBag B q.1 (hnonempty q) (hstrict q)) :
                  BonnetDepresVertex k) ∈ C := by
  classical
  let zOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => highestDescendantInBag B q.1 (hnonempty q)
  let pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => highestParentInBag B q.1 (hnonempty q) (hstrict q)
  let COf : {q // q ∈ R} → Finset (BonnetDepresVertex k) :=
    fun q => Classical.choose (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))
  have hCOfP : ∀ q : {q // q ∈ R}, COf q ∈ P := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).1
  have hpC :
      ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ COf q := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).2
  have hCneB : ∀ q : {q // q ∈ R}, COf q ≠ B := by
    intro q hEq
    have hp_notMem :
        (Sum.inr (pOf q) : BonnetDepresVertex k) ∉ B := by
      dsimp [pOf]
      exact parent_notMem_bag_of_highestDescendant
        (A := B) (q := q.1) (h := hnonempty q)
        (hp := highestParentInBag_isParent) (hstrict q)
    exact hp_notMem (by simpa [hEq] using hpC q)
  have havoid : ∀ q : {q // q ∈ R}, COf q ∉ F := by
    intro q
    simpa [COf, pOf] using havoidParentParts q
  rcases exists_internalNonSingletonTreeBag_of_antichain_step_avoiding
      (k := k) (d := d) (n := n) (P := P) (R := R) (B := B)
      F hB hred hRone hn hmul hanti
      (zOf := zOf) (pOf := pOf) (COf := COf)
      (by intro q; exact highestDescendantInBag_isAncestor (hnonempty q))
      (by intro q; exact highestDescendantInBag_mem_bag (hnonempty q))
      (by intro q; exact highestParentInBag_isParent)
      (by intro q; exact hstrict q)
      hCOfP hpC hCneB havoid with
    ⟨C, hCinternal, hCnotF, hfiber⟩
  let Rsub := R.attach.filter fun q => COf q = C
  refine ⟨C, hCinternal, hCnotF, Rsub, by simpa [Rsub] using hfiber, ?_⟩
  intro q hq
  have hqC : COf q = C := (Finset.mem_filter.mp hq).2
  simpa [pOf, hqC] using hpC q

/-- Highest-descendant step packaged with the next branch set in the original
tree-node type. -/
theorem exists_nextBranches_of_highestDescendant_step {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (hpart : IsBagPartition P)
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hnonempty :
      ∀ q : {q // q ∈ R}, (descendantsInBag B q.1).Nonempty)
    (hstrict :
      ∀ q : {q // q ∈ R},
        q.1.1.val < (highestDescendantInBag B q.1 (hnonempty q)).1.val) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      ∃ Rnext : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
        Rnext ⊆ R ∧ n < Rnext.card ∧
          (∀ ⦃q⦄, q ∈ Rnext → (descendantsInBag C q).Nonempty) := by
  classical
  rcases exists_internalNonSingletonTreeBag_of_highestDescendant_step
      (k := k) (d := d) (n := n) (P := P) (R := R) (B := B)
      hpart hB hred hRone hn hmul hanti hnonempty hstrict with
    ⟨C, hC, Rsub, hRsubCard, hparentsC⟩
  let Rnext : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :=
    Rsub.image fun q => q.1
  have hRnextCard : Rnext.card = Rsub.card := by
    change (Rsub.image Subtype.val).card = Rsub.card
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact Subtype.ext hab
  refine ⟨C, hC, Rnext, ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ Rsub.image (fun q => q.1) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, _hqsub, rfl⟩
    exact qsub.2
  · rwa [hRnextCard]
  · intro q hq
    change q ∈ Rsub.image (fun q => q.1) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, hqsub, rfl⟩
    refine ⟨highestParentInBag B qsub.1 (hnonempty qsub) (hstrict qsub), ?_⟩
    rw [mem_descendantsInBag]
    exact ⟨highestParentInBag_isAncestor, hparentsC qsub hqsub⟩

/-- Claim-19 one-step form matching the paper.  The selected descendant in the
current bag is the highest descendant and may equal the side branch.  The
ranked-level invariant and the singleton-parent invariant from Claim 18 ensure
that the pigeonholed next bag only keeps branches whose selected parent is
still a descendant of the original side branch. -/
theorem exists_nextBranches_of_ranked_highestDescendant_step {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (hpart : IsBagPartition P)
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hlevel_ne :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b → a.1.val ≠ b.1.val)
    (hparentSingleton :
      ∀ ⦃q⦄, q ∈ R →
        ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          FullTreeNode.IsParent p q ∧
            ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈ P)
    (hnonempty :
      ∀ q : {q // q ∈ R}, (descendantsInBag B q.1).Nonempty) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      ∃ Rnext : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
        Rnext ⊆ R ∧ n < Rnext.card ∧
          (∀ ⦃q⦄, q ∈ Rnext → (descendantsInBag C q).Nonempty) := by
  classical
  let zOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => highestDescendantInBag B q.1 (hnonempty q)
  have hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q) := by
    intro q
    exact highestDescendantInBag_isAncestor (hnonempty q)
  have hBz :
      ∀ q : {q // q ∈ R}, (Sum.inr (zOf q) : BonnetDepresVertex k) ∈ B := by
    intro q
    exact highestDescendantInBag_mem_bag (hnonempty q)
  have hz_pos : ∀ q : {q // q ∈ R}, 0 < (zOf q).1.val := by
    intro q
    rcases hparentSingleton q.2 with ⟨p, hp, _hpP⟩
    have hq_pos : 0 < q.1.1.val := by
      have hp_level := FullTreeNode.isParent_level hp
      omega
    rcases hdesc q with ⟨hqz, _⟩
    omega
  let pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => FullTreeNode.parent (zOf q) (hz_pos q)
  have hparent :
      ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q) := by
    intro q
    exact FullTreeNode.parent_isParent (zOf q) (hz_pos q)
  let COf : {q // q ∈ R} → Finset (BonnetDepresVertex k) :=
    fun q => Classical.choose (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))
  have hCOfP : ∀ q : {q // q ∈ R}, COf q ∈ P := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).1
  have hpC :
      ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ COf q := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).2
  have parentSingleton_of_nonstrict :
      ∀ q : {q // q ∈ R},
        ¬ q.1.1.val < (zOf q).1.val →
          ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) ∈ P := by
    intro q hnonstrict
    rcases hparentSingleton q.2 with ⟨p, hpq, hpP⟩
    have hz_level : q.1.1.val = (zOf q).1.val := by
      rcases hdesc q with ⟨hle, _⟩
      omega
    have hq_eq_z : q.1 = zOf q :=
      eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
        (hdesc q) (isTreeAncestor_refl (zOf q)) hz_level
    have hp_eq : pOf q = p :=
      FullTreeNode.isParent_unique (by simpa [hq_eq_z] using hparent q) hpq
    simpa [pOf, hp_eq] using hpP
  have hp_notMem_B :
      ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∉ B := by
    intro q hpB
    by_cases hstrict : q.1.1.val < (zOf q).1.val
    · exact parent_notMem_bag_of_highestDescendant
        (A := B) (q := q.1) (p := pOf q) (h := hnonempty q)
        (hp := hparent q) hstrict hpB
    · have hsingletonP := parentSingleton_of_nonstrict q hstrict
      by_cases hBsingleton :
          B = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k))
      · have hzB : (Sum.inr (zOf q) : BonnetDepresVertex k) ∈
            ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
          simpa [hBsingleton] using hBz q
        have hz_eq_p : zOf q = pOf q := by
          exact Sum.inr.inj (Finset.mem_singleton.mp hzB)
        exact FullTreeNode.not_isParent_self (zOf q) (by
          simpa [hz_eq_p] using hparent q)
      · have hdis := hpart.2.1 hB hsingletonP hBsingleton
        exact (Finset.disjoint_left.mp hdis) hpB (by simp)
  have hCneB : ∀ q : {q // q ∈ R}, COf q ≠ B := by
    intro q hEq
    exact hp_notMem_B q (by simpa [hEq] using hpC q)
  let redNeighbors := P.filter fun C => partitionRedAdj (bonnetDepresGraph k) B C
  have hmaps :
      ∀ q ∈ R.attach, COf q ∈ redNeighbors := by
    intro q _hq
    rw [Finset.mem_filter]
    refine ⟨hCOfP q, ?_⟩
    apply partitionRedAdj_symm
    exact partitionRedAdj_of_ranked_antichain_family_parent_part
      (k := k) (R := R) (B := B) (C := COf q) (a := q.1) (p := pOf q)
      q.2 hRone hanti hlevel_ne
      (fun r hr => zOf ⟨r, hr⟩)
      (fun r hr => hdesc ⟨r, hr⟩)
      (fun r hr => hBz ⟨r, hr⟩)
      (hparent q) (hCneB q).symm (hpC q)
  have hredCard : redNeighbors.card ≤ d := by
    simpa [redNeighbors] using hred hB
  have hpigeonMul :
      redNeighbors.card * n < R.attach.card := by
    have hle : redNeighbors.card * n ≤ d * n :=
      Nat.mul_le_mul_right _ hredCard
    exact hle.trans_lt (by simpa using hmul)
  rcases Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := R.attach) (t := redNeighbors) (f := COf) (n := n)
      hmaps hpigeonMul with
    ⟨C, hC, hfiber⟩
  let fiber := R.attach.filter fun q => COf q = C
  have hfiberOne : 1 < fiber.card := hn.trans_lt (by simpa [fiber] using hfiber)
  have hCP : C ∈ P := (Finset.mem_filter.mp hC).1
  have hinj : Function.Injective pOf :=
    parent_choice_injective_of_ranked_antichain
      (k := k) (R := R) hanti hlevel_ne
      (zOf := zOf) (pOf := pOf) hdesc hparent
  have hstrict_of_fiber :
      ∀ q : {q // q ∈ R}, q ∈ fiber → q.1.1.val < (zOf q).1.val := by
    intro q hqfiber
    by_contra hnonstrict
    have hqC : COf q = C := (Finset.mem_filter.mp hqfiber).2
    have hsingletonP := parentSingleton_of_nonstrict q hnonstrict
    have hCsingleton :
        C = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
      by_cases hEq : C = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k))
      · exact hEq
      · have hdis := hpart.2.1 hCP hsingletonP hEq
        exact False.elim
          ((Finset.disjoint_left.mp hdis) (by simpa [← hqC] using hpC q) (by simp))
    have hfiber_le_one : fiber.card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro r s hr hs
      have hrC : COf r = C := (Finset.mem_filter.mp hr).2
      have hsC : COf s = C := (Finset.mem_filter.mp hs).2
      have hpr : pOf r = pOf q := by
        have hmem : (Sum.inr (pOf r) : BonnetDepresVertex k) ∈
            ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
          simpa [hCsingleton, hrC] using hpC r
        exact Sum.inr.inj (Finset.mem_singleton.mp hmem)
      have hps : pOf s = pOf q := by
        have hmem : (Sum.inr (pOf s) : BonnetDepresVertex k) ∈
            ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
          simpa [hCsingleton, hsC] using hpC s
        exact Sum.inr.inj (Finset.mem_singleton.mp hmem)
      exact (hinj (hpr.trans hps.symm))
    omega
  rcases Finset.one_lt_card.mp hfiberOne with ⟨qa, hqa, qb, hqb, hqab⟩
  have hqaC : COf qa = C := (Finset.mem_filter.mp hqa).2
  have hqbC : COf qb = C := (Finset.mem_filter.mp hqb).2
  have hp_ne : pOf qa ≠ pOf qb := by
    intro hp_eq
    exact hqab (hinj hp_eq)
  have hCinternal : C ∈ internalNonSingletonTreeBags P :=
    mem_internalNonSingletonTreeBags_of_two_tree_vertices
      (k := k) (P := P) (A := C) (u := pOf qa) (v := pOf qb)
      hCP (parent_level_lt_depth_of_isParent (hparent qa))
      (by simpa [hqaC] using hpC qa)
      (by simpa [hqbC] using hpC qb)
      hp_ne
  let Rnext : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :=
    fiber.image fun q => q.1
  have hRnextCard : Rnext.card = fiber.card := by
    change (fiber.image Subtype.val).card = fiber.card
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact Subtype.ext hab
  refine ⟨C, hCinternal, Rnext, ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ fiber.image (fun q => q.1) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, _hqsub, rfl⟩
    exact qsub.2
  · rwa [hRnextCard]
  · intro q hq
    change q ∈ fiber.image (fun q => q.1) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, hqsub, rfl⟩
    refine descendantsInBag_nonempty_of_mem
      (q := qsub.1) (z := pOf qsub) ?_ ?_
    · exact isTreeAncestor_parent_of_strict_descendant
        (hdesc qsub) (hparent qsub) (hstrict_of_fiber qsub hqsub)
    · have hqC : COf qsub = C := (Finset.mem_filter.mp hqsub).2
      simpa [hqC] using hpC qsub

/-- Claim-19 step with the paper's path-avoidance invariant.  The next bag is
new with respect to the previously chosen bags, and the returned branch set has
available descendants for the enlarged previous-bag set. -/
theorem exists_nextBranches_of_availableDescendant_step {k d n : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    (F : Finset (Finset (BonnetDepresVertex k)))
    (hpart : IsBagPartition P)
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hRone : 1 < R.card)
    (hn : 1 ≤ n)
    (hmul : d * n < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hlevel_ne :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b → a.1.val ≠ b.1.val)
    (hparentSingleton :
      ∀ ⦃q⦄, q ∈ R →
        ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          FullTreeNode.IsParent p q ∧
            ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈ P)
    (hF_noSingleton :
      ∀ ⦃D⦄, D ∈ F →
        ∀ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          D ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)))
    (havailable :
      ∀ q : {q // q ∈ R}, (availableDescendantsInBag F B q.1).Nonempty) :
    ∃ C ∈ internalNonSingletonTreeBags P,
      C ∉ F ∧ C ≠ B ∧
        ∃ Rnext : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
          Rnext ⊆ R ∧ n < Rnext.card ∧
            (∀ ⦃q⦄, q ∈ Rnext →
              (availableDescendantsInBag (insert B F) C q).Nonempty) := by
  classical
  let zOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => highestAvailableDescendantInBag F B q.1 (havailable q)
  have hdesc : ∀ q : {q // q ∈ R}, IsTreeAncestor q.1 (zOf q) := by
    intro q
    exact highestAvailableDescendantInBag_isAncestor (havailable q)
  have hBz :
      ∀ q : {q // q ∈ R}, (Sum.inr (zOf q) : BonnetDepresVertex k) ∈ B := by
    intro q
    exact highestAvailableDescendantInBag_mem_bag (havailable q)
  have hz_pos : ∀ q : {q // q ∈ R}, 0 < (zOf q).1.val := by
    intro q
    rcases hparentSingleton q.2 with ⟨p, hp, _hpP⟩
    have hq_pos : 0 < q.1.1.val := by
      have hp_level := FullTreeNode.isParent_level hp
      omega
    rcases hdesc q with ⟨hqz, _⟩
    omega
  let pOf : {q // q ∈ R} →
      FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => FullTreeNode.parent (zOf q) (hz_pos q)
  have hparent :
      ∀ q : {q // q ∈ R}, FullTreeNode.IsParent (pOf q) (zOf q) := by
    intro q
    exact FullTreeNode.parent_isParent (zOf q) (hz_pos q)
  let COf : {q // q ∈ R} → Finset (BonnetDepresVertex k) :=
    fun q => Classical.choose (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))
  have hCOfP : ∀ q : {q // q ∈ R}, COf q ∈ P := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).1
  have hpC :
      ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∈ COf q := by
    intro q
    exact (Classical.choose_spec
      (hpart.2.2 (Sum.inr (pOf q) : BonnetDepresVertex k))).2
  have parentSingleton_of_nonstrict :
      ∀ q : {q // q ∈ R},
        ¬ q.1.1.val < (zOf q).1.val →
          ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) ∈ P := by
    intro q hnonstrict
    rcases hparentSingleton q.2 with ⟨p, hpq, hpP⟩
    have hz_level : q.1.1.val = (zOf q).1.val := by
      rcases hdesc q with ⟨hle, _⟩
      omega
    have hq_eq_z : q.1 = zOf q :=
      eq_of_isTreeAncestor_of_isTreeAncestor_of_level_eq
        (hdesc q) (isTreeAncestor_refl (zOf q)) hz_level
    have hp_eq : pOf q = p :=
      FullTreeNode.isParent_unique (by simpa [hq_eq_z] using hparent q) hpq
    simpa [pOf, hp_eq] using hpP
  have hp_notMem_B :
      ∀ q : {q // q ∈ R}, (Sum.inr (pOf q) : BonnetDepresVertex k) ∉ B := by
    intro q hpB
    by_cases hstrict : q.1.1.val < (zOf q).1.val
    · exact parent_notMem_bag_of_highestAvailableDescendant
        (F := F) (B := B) (q := q.1) (p := pOf q) (h := havailable q)
        (hp := hparent q) hstrict hpB
    · have hsingletonP := parentSingleton_of_nonstrict q hstrict
      by_cases hBsingleton :
          B = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k))
      · have hzB : (Sum.inr (zOf q) : BonnetDepresVertex k) ∈
            ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
          simpa [hBsingleton] using hBz q
        have hz_eq_p : zOf q = pOf q := by
          exact Sum.inr.inj (Finset.mem_singleton.mp hzB)
        exact FullTreeNode.not_isParent_self (zOf q) (by
          simpa [hz_eq_p] using hparent q)
      · have hdis := hpart.2.1 hB hsingletonP hBsingleton
        exact (Finset.disjoint_left.mp hdis) hpB (by simp)
  have hCneB : ∀ q : {q // q ∈ R}, COf q ≠ B := by
    intro q hEq
    exact hp_notMem_B q (by simpa [hEq] using hpC q)
  have hCOf_notMem_F : ∀ q : {q // q ∈ R}, COf q ∉ F := by
    intro q hCF
    by_cases hstrict : q.1.1.val < (zOf q).1.val
    · have hqp : IsTreeAncestor q.1 (pOf q) :=
        isTreeAncestor_parent_of_strict_descendant
          (hdesc q) (hparent q) hstrict
      exact highestAvailableDescendantInBag_path_avoids (havailable q) hCF
        ⟨hqp, isTreeAncestor_of_isParent (hparent q)⟩ (hpC q)
    · have hsingletonP := parentSingleton_of_nonstrict q hstrict
      have hCsingleton : COf q = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
        by_cases hEq : COf q = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k))
        · exact hEq
        · have hdis := hpart.2.1 (hCOfP q) hsingletonP hEq
          exact False.elim
            ((Finset.disjoint_left.mp hdis) (hpC q) (by simp))
      exact hF_noSingleton hCF (pOf q) hCsingleton
  let redNeighbors := P.filter fun C => partitionRedAdj (bonnetDepresGraph k) B C
  have hmaps :
      ∀ q ∈ R.attach, COf q ∈ redNeighbors := by
    intro q _hq
    rw [Finset.mem_filter]
    refine ⟨hCOfP q, ?_⟩
    apply partitionRedAdj_symm
    exact partitionRedAdj_of_ranked_antichain_family_parent_part
      (k := k) (R := R) (B := B) (C := COf q) (a := q.1) (p := pOf q)
      q.2 hRone hanti hlevel_ne
      (fun r hr => zOf ⟨r, hr⟩)
      (fun r hr => hdesc ⟨r, hr⟩)
      (fun r hr => hBz ⟨r, hr⟩)
      (hparent q) (hCneB q).symm (hpC q)
  have hredCard : redNeighbors.card ≤ d := by
    simpa [redNeighbors] using hred hB
  have hpigeonMul :
      redNeighbors.card * n < R.attach.card := by
    have hle : redNeighbors.card * n ≤ d * n :=
      Nat.mul_le_mul_right _ hredCard
    exact hle.trans_lt (by simpa using hmul)
  rcases Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := R.attach) (t := redNeighbors) (f := COf) (n := n)
      hmaps hpigeonMul with
    ⟨C, hC, hfiber⟩
  let fiber := R.attach.filter fun q => COf q = C
  have hfiberOne : 1 < fiber.card := hn.trans_lt (by simpa [fiber] using hfiber)
  have hCP : C ∈ P := (Finset.mem_filter.mp hC).1
  have hinj : Function.Injective pOf :=
    parent_choice_injective_of_ranked_antichain
      (k := k) (R := R) hanti hlevel_ne
      (zOf := zOf) (pOf := pOf) hdesc hparent
  have hstrict_of_fiber :
      ∀ q : {q // q ∈ R}, q ∈ fiber → q.1.1.val < (zOf q).1.val := by
    intro q hqfiber
    by_contra hnonstrict
    have hqC : COf q = C := (Finset.mem_filter.mp hqfiber).2
    have hsingletonP := parentSingleton_of_nonstrict q hnonstrict
    have hCsingleton :
        C = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
      by_cases hEq : C = ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k))
      · exact hEq
      · have hdis := hpart.2.1 hCP hsingletonP hEq
        exact False.elim
          ((Finset.disjoint_left.mp hdis) (by simpa [← hqC] using hpC q) (by simp))
    have hfiber_le_one : fiber.card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro r s hr hs
      have hrC : COf r = C := (Finset.mem_filter.mp hr).2
      have hsC : COf s = C := (Finset.mem_filter.mp hs).2
      have hpr : pOf r = pOf q := by
        have hmem : (Sum.inr (pOf r) : BonnetDepresVertex k) ∈
            ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
          simpa [hCsingleton, hrC] using hpC r
        exact Sum.inr.inj (Finset.mem_singleton.mp hmem)
      have hps : pOf s = pOf q := by
        have hmem : (Sum.inr (pOf s) : BonnetDepresVertex k) ∈
            ({Sum.inr (pOf q)} : Finset (BonnetDepresVertex k)) := by
          simpa [hCsingleton, hsC] using hpC s
        exact Sum.inr.inj (Finset.mem_singleton.mp hmem)
      exact (hinj (hpr.trans hps.symm))
    omega
  rcases Finset.one_lt_card.mp hfiberOne with ⟨qa, hqa, qb, hqb, hqab⟩
  have hqaC : COf qa = C := (Finset.mem_filter.mp hqa).2
  have hqbC : COf qb = C := (Finset.mem_filter.mp hqb).2
  have hp_ne : pOf qa ≠ pOf qb := by
    intro hp_eq
    exact hqab (hinj hp_eq)
  have hCinternal : C ∈ internalNonSingletonTreeBags P :=
    mem_internalNonSingletonTreeBags_of_two_tree_vertices
      (k := k) (P := P) (A := C) (u := pOf qa) (v := pOf qb)
      hCP (parent_level_lt_depth_of_isParent (hparent qa))
      (by simpa [hqaC] using hpC qa)
      (by simpa [hqbC] using hpC qb)
      hp_ne
  have hCnotF : C ∉ F := by
    intro hCF
    exact hCOf_notMem_F qa (by simpa [hqaC] using hCF)
  have hCneB_final : C ≠ B := by
    intro hCB
    exact hCneB qa (by simp [hqaC, hCB])
  let Rnext : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)) :=
    fiber.image fun q => q.1
  have hRnextCard : Rnext.card = fiber.card := by
    change (fiber.image Subtype.val).card = fiber.card
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact Subtype.ext hab
  refine ⟨C, hCinternal, hCnotF, hCneB_final, Rnext, ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ fiber.image (fun q => q.1) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, _hqsub, rfl⟩
    exact qsub.2
  · rwa [hRnextCard]
  · intro q hq
    change q ∈ fiber.image (fun q => q.1) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, hqsub, rfl⟩
    have hstrict := hstrict_of_fiber qsub hqsub
    have hqp : IsTreeAncestor qsub.1 (pOf qsub) :=
      isTreeAncestor_parent_of_strict_descendant
        (hdesc qsub) (hparent qsub) hstrict
    have hpCq : (Sum.inr (pOf qsub) : BonnetDepresVertex k) ∈ C := by
      have hqC : COf qsub = C := (Finset.mem_filter.mp hqsub).2
      simpa [hqC] using hpC qsub
    refine availableDescendantsInBag_nonempty_of_mem
      (F := insert B F) (B := C) (q := qsub.1) (z := pOf qsub)
      hqp hpCq ?_
    intro D hD x hxPath hxD
    rw [Finset.mem_insert] at hD
    rcases hD with hD_eq | hD_old
    · subst D
      have hxAvail : x ∈ availableDescendantsInBag F B qsub.1 := by
        rw [mem_availableDescendantsInBag]
        refine ⟨hxPath.1, hxD, ?_⟩
        intro D hD y hy
        exact highestAvailableDescendantInBag_path_avoids (havailable qsub) hD
          ⟨hy.1, isTreeAncestor_trans hy.2
            (isTreeAncestor_trans hxPath.2 (isTreeAncestor_of_isParent (hparent qsub)))⟩
      have hmin := (highestAvailableDescendantInBag_spec (havailable qsub)).2 x hxAvail
      have hz_le_x : (zOf qsub).1.val ≤ x.1.val := by
        simpa [zOf] using hmin
      have hx_le_p : x.1.val ≤ (pOf qsub).1.val := hxPath.2.1
      have hp_level : (zOf qsub).1.val = (pOf qsub).1.val + 1 :=
        FullTreeNode.isParent_level (hparent qsub)
      omega
    · exact highestAvailableDescendantInBag_path_avoids (havailable qsub) hD_old
        ⟨hxPath.1,
          isTreeAncestor_trans hxPath.2 (isTreeAncestor_of_isParent (hparent qsub))⟩ hxD

/-- Iterates the path-available Claim-19 step and accumulates distinct
non-singleton internal-tree bags. -/
theorem exists_internalNonSingletonTreeBags_of_available_iteration
    {k d steps : ℕ}
    {P : Finset (Finset (BonnetDepresVertex k))}
    {R : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {B : Finset (BonnetDepresVertex k)}
    {Prev Count : Finset (Finset (BonnetDepresVertex k))}
    (hd : d ≤ 2 ^ k)
    (hpart : IsBagPartition P)
    (hB : B ∈ P)
    (hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d)
    (hPrev_noSingleton :
      ∀ ⦃D⦄, D ∈ Prev →
        ∀ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          D ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)))
    (hB_noSingleton :
      ∀ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        B ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)))
    (hCount_subset : Count ⊆ insert B Prev)
    (hCount_internal : Count ⊆ internalNonSingletonTreeBags P)
    (hcard : (manyChildrenThreshold k) ^ steps < R.card)
    (hanti :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a)
    (hlevel_ne :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b → a.1.val ≠ b.1.val)
    (hparentSingleton :
      ∀ ⦃q⦄, q ∈ R →
        ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          FullTreeNode.IsParent p q ∧
            ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈ P)
    (havailable :
      ∀ q : {q // q ∈ R}, (availableDescendantsInBag Prev B q.1).Nonempty) :
    ∃ Count' : Finset (Finset (BonnetDepresVertex k)),
      Count ⊆ Count' ∧ Count'.card = Count.card + steps ∧
        Count' ⊆ internalNonSingletonTreeBags P := by
  induction steps generalizing B Prev Count R with
  | zero =>
      refine ⟨Count, fun _ h => h, by omega, hCount_internal⟩
  | succ r ih =>
      have ht_one : 1 < (manyChildrenThreshold k) ^ (r + 1) := by
        exact one_lt_pow₀
          (lt_of_lt_of_le (by omega : 1 < 2) (two_le_manyChildrenThreshold k))
          (by omega)
      have hRone : 1 < R.card := by omega
      have hn : 1 ≤ (manyChildrenThreshold k) ^ r :=
        (pow_pos (manyChildrenThreshold_pos k) r).succ_le
      have hmul : d * (manyChildrenThreshold k) ^ r < R.card :=
        (redBound_mul_manyChildrenThreshold_pow_lt_succ
          (k := k) (d := d) (r := r) hd).trans hcard
      rcases exists_nextBranches_of_availableDescendant_step
          (k := k) (d := d) (n := (manyChildrenThreshold k) ^ r)
          (P := P) (R := R) (B := B)
          Prev hpart hB hred hRone hn hmul hanti hlevel_ne
          hparentSingleton hPrev_noSingleton havailable with
        ⟨C, hCinternal, hCnotPrev, hCneB, Rnext, hRnext_subset,
          hRnext_card, havailableNext⟩
      have hCnotCount : C ∉ Count := by
        intro hCCount
        have hCin : C ∈ insert B Prev := hCount_subset hCCount
        rw [Finset.mem_insert] at hCin
        rcases hCin with hCB | hCPrev
        · exact hCneB hCB
        · exact hCnotPrev hCPrev
      have hPrev_noSingleton' :
          ∀ ⦃D⦄, D ∈ insert B Prev →
            ∀ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
              D ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
        intro D hD p
        rw [Finset.mem_insert] at hD
        rcases hD with rfl | hD
        · exact hB_noSingleton p
        · exact hPrev_noSingleton hD p
      have hCount_subset' : insert C Count ⊆ insert C (insert B Prev) := by
        intro D hD
        rw [Finset.mem_insert] at hD ⊢
        rcases hD with rfl | hD
        · exact Or.inl rfl
        · exact Or.inr (hCount_subset hD)
      have hCount_internal' : insert C Count ⊆ internalNonSingletonTreeBags P := by
        intro D hD
        rw [Finset.mem_insert] at hD
        rcases hD with rfl | hD
        · exact hCinternal
        · exact hCount_internal hD
      have hB_noSingleton' :
          ∀ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            C ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
        intro p
        exact internalNonSingletonTreeBag_ne_singleton_tree hCinternal p
      have hantiNext :
          ∀ ⦃a⦄, a ∈ Rnext → ∀ ⦃b⦄, b ∈ Rnext → a ≠ b →
            ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a :=
        antichain_mono hRnext_subset hanti
      have hlevelNext :
          ∀ ⦃a⦄, a ∈ Rnext → ∀ ⦃b⦄, b ∈ Rnext → a ≠ b →
            a.1.val ≠ b.1.val := by
        intro a ha b hb hab
        exact hlevel_ne (hRnext_subset ha) (hRnext_subset hb) hab
      have hparentNext :
          ∀ ⦃q⦄, q ∈ Rnext →
            ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
              FullTreeNode.IsParent p q ∧
                ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈ P := by
        intro q hq
        exact hparentSingleton (hRnext_subset hq)
      have hCP : C ∈ P := (mem_internalNonSingletonTreeBags.mp hCinternal).1
      rcases ih
          (B := C) (Prev := insert B Prev) (Count := insert C Count)
          (R := Rnext)
          hCP hPrev_noSingleton' hB_noSingleton'
          hCount_subset' hCount_internal' hRnext_card
          hantiNext hlevelNext hparentNext (fun q => havailableNext q.2) with
        ⟨CountFinal, hinsert_subset, hcardFinal, hinternalFinal⟩
      refine ⟨CountFinal, ?_, ?_, hinternalFinal⟩
      · intro D hD
        exact hinsert_subset (by simp [hD])
      · have hinsert_card : (insert C Count).card = Count.card + 1 := by
          rw [Finset.card_insert_of_notMem hCnotCount]
        omega

/-- A large-bag fiber of side branches has the same number of distinct preleaf
descendants witnessed by that large bag. -/
theorem exists_distinct_preleaf_witnesses_of_largeBag {k : ℕ}
    {Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    {A : Finset (BonnetDepresVertex k)}
    (hanti :
      ∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) :
    ∃ Vs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
      Vs.card = (sideBranchesWitnessedByLargeBag Qs A).card ∧
        ∀ ⦃v⦄, v ∈ Vs →
          IsPreleaf v ∧
            ∃ q ∈ sideBranchesWitnessedByLargeBag Qs A,
              IsTreeAncestor q v ∧
                ∃ hlevel : IsInternal v,
                  manyChildrenThreshold k ≤
                    (A ∩ childVertexSet v hlevel).card := by
  classical
  let R := sideBranchesWitnessedByLargeBag Qs A
  let witness :
      ∀ q : {q // q ∈ R},
        ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          IsTreeAncestor q.1 v ∧ IsPreleaf v ∧
            ∃ hlevel : IsInternal v,
              manyChildrenThreshold k ≤
                (A ∩ childVertexSet v hlevel).card := by
    intro q
    have hq : q.1 ∈ sideBranchesWitnessedByLargeBag Qs A := by
      change q.1 ∈ R
      exact q.2
    rw [sideBranchesWitnessedByLargeBag, Finset.mem_filter] at hq
    exact hq.2
  let vOf :
      {q // q ∈ R} →
        FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k) :=
    fun q => Classical.choose (witness q)
  have vOf_spec :
      ∀ q : {q // q ∈ R},
        IsTreeAncestor q.1 (vOf q) ∧ IsPreleaf (vOf q) ∧
          ∃ hlevel : IsInternal (vOf q),
            manyChildrenThreshold k ≤
              (A ∩ childVertexSet (vOf q) hlevel).card := by
    intro q
    exact Classical.choose_spec (witness q)
  have hRsubset : R ⊆ Qs := by
    simpa [R] using
      (sideBranchesWitnessedByLargeBag_subset (k := k) (Qs := Qs) (A := A))
  have hinj : Function.Injective vOf :=
    descendant_choice_injective_of_antichain
      (k := k) (Qs := Qs) (R := R) hRsubset hanti
      (vOf := vOf) (fun q => (vOf_spec q).1)
  let Vs := R.attach.image vOf
  refine ⟨Vs, ?_, ?_⟩
  · change (R.attach.image vOf).card = R.card
    rw [Finset.card_image_of_injective]
    · simp
    · exact hinj
  · intro v hv
    change v ∈ R.attach.image vOf at hv
    rw [Finset.mem_image] at hv
    rcases hv with ⟨q, _hq, rfl⟩
    refine ⟨(vOf_spec q).2.1, q.1, ?_, (vOf_spec q).1, ?_⟩
    · change q.1 ∈ R
      exact q.2
    · exact (vOf_spec q).2.2

/-- Pigeonholing Claim-18 side branches by the large bag supplied by their
descendant preleaf: one large bag receives many side branches. -/
theorem ContractionSequence.exists_largeChildBag_with_many_sideBranches
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    {Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k))}
    (hcard : Qs.card = bonnetDepresDepth k - 2)
    (hQmem :
      ∀ ⦃q⦄, q ∈ Qs →
        QProperty
          (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) :
    ∃ A ∈ largeChildBags
        (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags,
      manySideBranchesThreshold k ≤
        (sideBranchesWitnessedByLargeBag Qs A).card := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  let P := (S.state i).bags
  let L := largeChildBags P
  let witness :
      ∀ q : {q // q ∈ Qs},
        ∃ A ∈ L,
          ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
            IsTreeAncestor q.1 v ∧ IsPreleaf v ∧
              ∃ hlevel : IsInternal v,
                manyChildrenThreshold k ≤
                  (A ∩ childVertexSet v hlevel).card := by
    intro q
    have hQq :
        QProperty (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q.1 :=
      hQmem q.2
    rcases ContractionSequence.exists_descendant_preleaf_largeChildBag_of_qProperty
        S hd hQq with
      ⟨v, hqv, hpre, hlevel, A, hA, hmany⟩
    exact ⟨A, by simpa [L, P, i] using hA, v, hqv, hpre, hlevel, hmany⟩
  let chosenA :
      {q // q ∈ Qs} → Finset (BonnetDepresVertex k) :=
    fun q => Classical.choose (witness q)
  have chosenA_mem :
      ∀ q : {q // q ∈ Qs}, chosenA q ∈ L := by
    intro q
    exact (Classical.choose_spec (witness q)).1
  have chosenA_spec :
      ∀ q : {q // q ∈ Qs},
        ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          IsTreeAncestor q.1 v ∧ IsPreleaf v ∧
            ∃ hlevel : IsInternal v,
              manyChildrenThreshold k ≤
                (chosenA q ∩ childVertexSet v hlevel).card := by
    intro q
    exact (Classical.choose_spec (witness q)).2
  have hi_le : i ≤ S.stepCount := by
    have hfirst :=
      ContractionSequence.firstRootChildQIndex_le_before_first_pred S hd
    have hstep :=
      ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
    omega
  have hLcard : L.card ≤ 2 ^ (k + 2) := by
    have hroot : RootChildrenSingleton P := by
      simpa [P, i] using
        ContractionSequence.rootChildrenSingleton_firstRootChildQIndex S hd
    have hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d := by
      simpa [P, i] using
        _root_.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state
          S hi_le
    exact largeChildBags_card_le
      (k := k) (d := d) (P := P) hd
      (_root_.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
      hroot hred
  have hLnonempty : L.Nonempty := by
    have hcard_pos : 0 < Qs.card := by
      rw [hcard]
      have hdepth := two_lt_depth k
      omega
    rcases Finset.card_pos.mp hcard_pos with ⟨q, hq⟩
    rcases witness ⟨q, hq⟩ with ⟨A, hA, _hv⟩
    exact ⟨A, hA⟩
  have hpigeon_mul :
      L.card * manySideBranchesThreshold k ≤ Qs.attach.card := by
    calc
      L.card * manySideBranchesThreshold k
          ≤ 2 ^ (k + 2) * manySideBranchesThreshold k :=
        Nat.mul_le_mul_right _ hLcard
      _ = Qs.card := by
        rw [hcard, depth_sub_two_eq_largeBagBound_mul_manySideBranchesThreshold]
      _ = Qs.attach.card := by
        simp
  rcases Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := Qs.attach) (t := L) (f := chosenA)
      (n := manySideBranchesThreshold k)
      (by intro q _hq; exact chosenA_mem q)
      hLnonempty hpigeon_mul with
    ⟨A, hA, hfiber⟩
  let Fattach := Qs.attach.filter fun q => chosenA q = A
  let F :=
    sideBranchesWitnessedByLargeBag Qs A
  have himage_card :
      (Fattach.image fun q => q.1).card = Fattach.card := by
    rw [Finset.card_image_of_injective]
    intro q r hqr
    exact Subtype.ext hqr
  have hsubset : (Fattach.image fun q => q.1) ⊆ F := by
    intro q hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨qsub, hqsub, rfl⟩
    change qsub.1 ∈ sideBranchesWitnessedByLargeBag Qs A
    rw [sideBranchesWitnessedByLargeBag, Finset.mem_filter]
    have hchosen : chosenA qsub = A := (Finset.mem_filter.mp hqsub).2
    rcases chosenA_spec qsub with ⟨v, hqv, hpre, hlevel, hmany⟩
    refine ⟨qsub.2, v, hqv, hpre, hlevel, ?_⟩
    simpa [hchosen] using hmany
  have hFcard : Fattach.card ≤ F.card := by
    rw [← himage_card]
    exact Finset.card_le_card hsubset
  refine ⟨A, by simpa [L, P, i] using hA, ?_⟩
  exact hfiber.trans (by simpa [Fattach, F] using hFcard)

/-- Claim 18 combined with the large-bag pigeonhole step. -/
theorem ContractionSequence.exists_antichain_sideBranchSet_largeChildBag_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
      ∃ A ∈ largeChildBags
          (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags,
        Qs.card = bonnetDepresDepth k - 2 ∧
          (∀ ⦃q⦄, q ∈ Qs →
            QProperty
              (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
          (∀ ⦃q⦄, q ∈ Qs →
            ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
              FullTreeNode.IsParent p q ∧
                ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                  (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
          (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
            ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) ∧
          manySideBranchesThreshold k ≤
            (sideBranchesWitnessedByLargeBag Qs A).card := by
  rcases ContractionSequence.exists_antichain_sideBranchSet_firstRootChildQIndex
      S hd with
    ⟨Qs, hcard, hQmem, hparent, hanti⟩
  rcases ContractionSequence.exists_largeChildBag_with_many_sideBranches
      S hd hcard hQmem with
    ⟨A, hA, hmany⟩
  exact ⟨Qs, A, hA, hcard, hQmem, hparent, hanti, hmany⟩

/-- Ranked Claim 18 combined with the large-bag pigeonhole step. -/
theorem ContractionSequence.exists_ranked_antichain_sideBranchSet_largeChildBag_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ Qs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
      ∃ A ∈ largeChildBags
          (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags,
        Qs.card = bonnetDepresDepth k - 2 ∧
          (∀ ⦃q⦄, q ∈ Qs →
            QProperty
              (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags q) ∧
          (∀ ⦃q⦄, q ∈ Qs →
            ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
              FullTreeNode.IsParent p q ∧
                ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈
                  (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags) ∧
          (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
            ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a) ∧
          (∀ ⦃a⦄, a ∈ Qs → ∀ ⦃b⦄, b ∈ Qs → a ≠ b →
            a.1.val ≠ b.1.val) ∧
          manySideBranchesThreshold k ≤
            (sideBranchesWitnessedByLargeBag Qs A).card := by
  rcases ContractionSequence.exists_ranked_antichain_sideBranchSet_firstRootChildQIndex
      S hd with
    ⟨Qs, hcard, hQmem, hparent, hanti, hlevel_ne⟩
  rcases ContractionSequence.exists_largeChildBag_with_many_sideBranches
      S hd hcard hQmem with
    ⟨A, hA, hmany⟩
  exact ⟨Qs, A, hA, hcard, hQmem, hparent, hanti, hlevel_ne, hmany⟩

/-- The base object for Claim 19: a large bag containing many children below
many distinct preleafs. -/
theorem ContractionSequence.exists_largeChildBag_with_many_distinct_preleafs
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ A ∈ largeChildBags
        (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags,
      ∃ Vs : Finset (FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k)),
        manySideBranchesThreshold k ≤ Vs.card ∧
          ∀ ⦃v⦄, v ∈ Vs →
            IsPreleaf v ∧
              ∃ hlevel : IsInternal v,
                manyChildrenThreshold k ≤
                  (A ∩ childVertexSet v hlevel).card := by
  rcases ContractionSequence.exists_antichain_sideBranchSet_largeChildBag_firstRootChildQIndex
      S hd with
    ⟨Qs, A, hA, _hcard, _hQmem, _hparent, hanti, hmany⟩
  rcases exists_distinct_preleaf_witnesses_of_largeBag
      (k := k) (Qs := Qs) (A := A) hanti with
    ⟨Vs, hVsCard, hVs⟩
  refine ⟨A, hA, Vs, ?_, ?_⟩
  · rwa [hVsCard]
  · intro v hv
    rcases hVs hv with ⟨hpre, _q, _hq, _hqv, hlarge⟩
    exact ⟨hpre, hlarge⟩

/-- Claim 19 at the first root-child-`Q` state: the path-avoidance induction
produces enough distinct non-singleton parts containing internal tree nodes. -/
theorem ContractionSequence.many_internalNonSingletonTreeBags_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    manyInternalBagsThreshold k ≤
      (internalNonSingletonTreeBags
        (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags).card := by
  classical
  let i := ContractionSequence.firstRootChildQIndex S hd
  let P := (S.state i).bags
  rcases ContractionSequence.exists_ranked_antichain_sideBranchSet_largeChildBag_firstRootChildQIndex
      S hd with
    ⟨Qs, A, hA_large, _hcardQs, _hQmem, hparentQs, hantiQs, hlevelQs, hmanyR⟩
  let R := sideBranchesWitnessedByLargeBag Qs A
  have hRsubset : R ⊆ Qs :=
    sideBranchesWitnessedByLargeBag_subset (k := k) (Qs := Qs) (A := A)
  have hi_le : i ≤ S.stepCount := by
    have hfirst :=
      ContractionSequence.firstRootChildQIndex_le_before_first_pred S hd
    have hstep :=
      ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
    omega
  have hpart : IsBagPartition P :=
    _root_.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i)
  have hred : PartitionRedDegreeAtMost (bonnetDepresGraph k) P d := by
    simpa [P, i] using
      _root_.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state
        S hi_le
  have hA : A ∈ P := (mem_largeChildBags.mp (by simpa [P, i] using hA_large)).1
  have hB_noSingleton :
      ∀ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
        A ≠ ({Sum.inr p} : Finset (BonnetDepresVertex k)) := by
    intro p
    exact largeChildBag_ne_singleton_tree (by simpa [P, i] using hA_large) p
  have hantiR :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b →
        ¬ IsTreeAncestor a b ∧ ¬ IsTreeAncestor b a :=
    antichain_mono hRsubset hantiQs
  have hlevelR :
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ R → a ≠ b → a.1.val ≠ b.1.val := by
    intro a ha b hb hab
    exact hlevelQs (hRsubset ha) (hRsubset hb) hab
  have hparentR :
      ∀ ⦃q⦄, q ∈ R →
        ∃ p : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
          FullTreeNode.IsParent p q ∧
            ({Sum.inr p} : Finset (BonnetDepresVertex k)) ∈ P := by
    intro q hq
    simpa [P, i] using hparentQs (hRsubset hq)
  have havailable0 :
      ∀ q : {q // q ∈ R}, (availableDescendantsInBag ∅ A q.1).Nonempty := by
    intro q
    have hqR : q.1 ∈ sideBranchesWitnessedByLargeBag Qs A := q.2
    rw [sideBranchesWitnessedByLargeBag, Finset.mem_filter] at hqR
    rcases hqR with ⟨_hqQs, v, hqv, _hpre, hlevel, hmany⟩
    rcases exists_child_mem_bag_of_manyChildren hmany with ⟨c, hc, hcA⟩
    refine availableDescendantsInBag_nonempty_of_mem
      (F := ∅) (B := A) (q := q.1) (z := c)
      (isTreeAncestor_trans hqv (isAncestor_of_mem_childSet hc)) hcA ?_
    intro D hD x hx
    simp at hD
  have hcardStart :
      (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k) < R.card := by
    have ht_one : 1 < manyChildrenThreshold k :=
      lt_of_lt_of_le (by omega : 1 < 2) (two_le_manyChildrenThreshold k)
    have hpow_pos :
        0 < (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k) :=
      pow_pos (manyChildrenThreshold_pos k) _
    have hpow_lt :
        (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k) <
          (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k + 1) := by
      rw [Nat.pow_succ]
      calc
        (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k)
            = (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k) * 1 := by omega
        _ < (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k) *
              manyChildrenThreshold k :=
            Nat.mul_lt_mul_of_pos_left ht_one hpow_pos
    have hpow_le_R :
        (manyChildrenThreshold k) ^ (manyInternalBagsThreshold k + 1) ≤ R.card := by
      rw [← manySideBranchesThreshold_eq_manyChildrenThreshold_pow]
      simpa [R] using hmanyR
    exact hpow_lt.trans_le hpow_le_R
  rcases exists_internalNonSingletonTreeBags_of_available_iteration
      (k := k) (d := d) (steps := manyInternalBagsThreshold k)
      (P := P) (R := R) (B := A) (Prev := ∅) (Count := ∅)
      hd hpart hA hred
      (by intro D hD p; simp at hD)
      hB_noSingleton
      (by intro D hD; simp at hD)
      (by intro D hD; simp at hD)
      hcardStart hantiR hlevelR hparentR havailable0 with
    ⟨CountFinal, _hEmptySubset, hCountCard, hCountInternal⟩
  have hcard_le :
      CountFinal.card ≤ (internalNonSingletonTreeBags P).card :=
    Finset.card_le_card hCountInternal
  have htarget : CountFinal.card = manyInternalBagsThreshold k := by
    simpa using hCountCard
  change manyInternalBagsThreshold k ≤ (internalNonSingletonTreeBags P).card
  omega

/-- Final contradiction at the first root-child-`Q` state, once Claim 19 has
produced enough non-singleton internal-tree parts. -/
theorem ContractionSequence.false_of_many_internalNonSingletonTreeBags_firstRootChildQIndex
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k)
    (hmany :
      manyInternalBagsThreshold k ≤
        (internalNonSingletonTreeBags
          (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags).card) :
    False := by
  let i := ContractionSequence.firstRootChildQIndex S hd
  have hi_le : i ≤ S.stepCount := by
    have hfirst :=
      ContractionSequence.firstRootChildQIndex_le_before_first_pred S hd
    have hstep :=
      ContractionSequence.firstRootChildrenNonSingletonIndex_le_stepCount S
    omega
  have hroot : RootChildrenSingleton (S.state i).bags := by
    simpa [i] using
      ContractionSequence.rootChildrenSingleton_firstRootChildQIndex S hd
  have hred :
      PartitionRedDegreeAtMost (bonnetDepresGraph k) (S.state i).bags d :=
    _root_.TwinWidth.SimpleGraph.ContractionSequence.partitionRedDegreeAtMost_state
      S hi_le
  exact false_of_many_internalNonSingletonTreeBags
    (k := k) (d := d) (P := (S.state i).bags)
    hd (_root_.TwinWidth.SimpleGraph.TrigraphState.isBagPartition (S.state i))
    hroot hred (by simpa [i] using hmany)

/-- Combiner for the remaining Claim-19 induction: if every `2^k`-bounded
sequence has the final number of non-singleton internal-tree parts at the first
root-child-`Q` state, then no such sequence exists. -/
theorem not_hasTwinWidthAtMost_of_many_internalNonSingletonTreeBags
    {k d : ℕ}
    (hd : d ≤ 2 ^ k)
    (hClaim19 :
      ∀ S : ContractionSequence (bonnetDepresGraph k) d,
        manyInternalBagsThreshold k ≤
          (internalNonSingletonTreeBags
            (S.state (ContractionSequence.firstRootChildQIndex S hd)).bags).card) :
    ¬ HasTwinWidthAtMost (bonnetDepresGraph k) d := by
  rintro ⟨S⟩
  exact
    ContractionSequence.false_of_many_internalNonSingletonTreeBags_firstRootChildQIndex
      S hd (hClaim19 S)

/-- The Bonnet--Déprés graph has no contraction sequence of red degree at most
`2^k`. -/
theorem bonnetDepres_not_hasTwinWidthAtMost_two_pow (k : ℕ) :
    ¬ HasTwinWidthAtMost (bonnetDepresGraph k) (2 ^ k) := by
  exact not_hasTwinWidthAtMost_of_many_internalNonSingletonTreeBags
    (k := k) (d := 2 ^ k) le_rfl
    (fun S => ContractionSequence.many_internalNonSingletonTreeBags_firstRootChildQIndex
      S le_rfl)

/-- The concrete Bonnet--Déprés lower bound on twin-width. -/
theorem bonnetDepres_two_pow_lt_twinWidth (k : ℕ) :
    2 ^ k < twinWidth (bonnetDepresGraph k) :=
  _root_.TwinWidth.SimpleGraph.lt_twinWidth_of_not_hasTwinWidthAtMost
    (bonnetDepres_not_hasTwinWidthAtMost_two_pow k)

/-- Concrete separation: for every `k` there is a finite graph of treewidth at
most `2*k+4` and twin-width greater than `2^k`. -/
theorem exists_graph_treewidth_linear_twin_width_exponential (k : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : _root_.SimpleGraph V),
      treewidth G ≤ 2 * k + 4 ∧ 2 ^ k < twinWidth G := by
  exact ⟨BonnetDepresVertex k, inferInstance, inferInstance, bonnetDepresGraph k,
    bonnetDepres_treewidth_le k, bonnetDepres_two_pow_lt_twinWidth k⟩

/-- Before the first contraction involving a root child, some preleaf already
satisfies property `P`. -/
theorem ContractionSequence.exists_preleaf_hasManyChildrenInPart_before_first
    {k d : ℕ}
    (S : ContractionSequence (bonnetDepresGraph k) d)
    (hd : d ≤ 2 ^ k) :
    ∃ v : FullTreeNode (bonnetDepresBranch k) (bonnetDepresDepth k),
      ∃ hlevel : IsInternal v,
        IsPreleaf v ∧
          HasManyChildrenInPart
            (S.state (ContractionSequence.firstRootChildrenNonSingletonIndex S - 1)).bags
            v hlevel (manyChildrenThreshold k) := by
  rcases ContractionSequence.exists_rootChild_qProperty_before_first S hd with ⟨f, hQ⟩
  exact exists_preleaf_hasManyChildrenInPart_of_qProperty hQ

end BonnetDepres

end SimpleGraph
end TwinWidth
