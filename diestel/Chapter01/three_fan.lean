import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

structure ThreeFan {V : Type u} (G : SimpleGraph V) (S : Set V) (ports : Finset V) where
  center : V
  center_mem : center ∈ S
  arm : ∀ p : V, p ∈ ports → G.Walk center p
  arm_isPath : ∀ p hp, (arm p hp).IsPath
  arm_support_subset : ∀ p hp, ∀ z : V, z ∈ (arm p hp).support → z ∈ S
  arm_support_inter_support :
    ∀ ⦃p q : V⦄ (hp : p ∈ ports) (hq : q ∈ ports), p ≠ q →
      ∀ z : V, z ∈ (arm p hp).support → z ∈ (arm q hq).support → z = center
  arm_support_inter_ports :
    ∀ ⦃p q : V⦄ (hp : p ∈ ports) (hq : q ∈ ports),
      q ∈ (arm p hp).support → q = center ∨ q = p

structure IndexedFan {V : Type u} {ι : Type v} (G : SimpleGraph V) (S : Set V)
    (ports : Finset ι) (target : ι → V) where
  center : V
  center_mem : center ∈ S
  arm : ∀ i : ι, i ∈ ports → G.Walk center (target i)
  arm_isPath : ∀ i hi, (arm i hi).IsPath
  arm_support_subset : ∀ i hi, ∀ z : V, z ∈ (arm i hi).support → z ∈ S
  arm_support_inter_support :
    ∀ ⦃i j : ι⦄ (hi : i ∈ ports) (hj : j ∈ ports), i ≠ j →
      ∀ z : V, z ∈ (arm i hi).support → z ∈ (arm j hj).support → z = center

private def singleton_threeFan {V : Type u} (G : SimpleGraph V) (S : Set V) {a : V}
    (ha : a ∈ S) :
    ThreeFan G S {a} where
  center := a
  center_mem := ha
  arm := by
    intro p hp
    have hpa : p = a := by simpa using hp
    exact (SimpleGraph.Walk.nil : G.Walk a a).copy rfl hpa.symm
  arm_isPath := by
    intro p hp
    have hpa : p = a := by simpa using hp
    subst p
    exact SimpleGraph.Walk.IsPath.nil
  arm_support_subset := by
    intro p hp z hz
    have hpa : p = a := by simpa using hp
    subst p
    have hza : z = a := by simpa [SimpleGraph.Walk.support_nil] using hz
    exact hza.symm ▸ ha
  arm_support_inter_support := by
    intro p q hp hq hpq z hzp hzq
    have hpa : p = a := by simpa using hp
    have hqa : q = a := by simpa using hq
    exact False.elim (hpq (hpa.trans hqa.symm))
  arm_support_inter_ports := by
    intro p q hp hq hqmem
    have hpa : p = a := by simpa using hp
    have hqa : q = a := by simpa using hq
    left
    exact hqa

private noncomputable def pathInSet {V : Type u} {G : SimpleGraph V} {S : Set V}
    (hconn : (G.induce S).Connected) {a b : V} (ha : a ∈ S) (hb : b ∈ S) :
    G.Walk a b := by
  classical
  let aa : S := ⟨a, ha⟩
  let bb : S := ⟨b, hb⟩
  exact (Classical.choice (hconn.preconnected aa bb)).map
    (SimpleGraph.Embedding.induce (G := G) S).toHom

private theorem pathInSet_isPath {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V]
    (hconn : (G.induce S).Connected) {a b : V} (ha : a ∈ S) (hb : b ∈ S) :
    ((pathInSet hconn ha hb).bypass).IsPath := by
  exact SimpleGraph.Walk.bypass_isPath _

private theorem pathInSet_support_subset {V : Type u} {G : SimpleGraph V} {S : Set V}
    (hconn : (G.induce S).Connected) {a b z : V} (ha : a ∈ S) (hb : b ∈ S)
    (hz : z ∈ (pathInSet hconn ha hb).support) :
    z ∈ S := by
  classical
  let aa : S := ⟨a, ha⟩
  let bb : S := ⟨b, hb⟩
  let p : (G.induce S).Walk aa bb := Classical.choice (hconn.preconnected aa bb)
  have hz' :
      z ∈ (p.map (SimpleGraph.Embedding.induce (G := G) S).toHom).support := by
    simpa [pathInSet, aa, bb, p] using hz
  rw [SimpleGraph.Walk.support_map] at hz'
  rcases List.mem_map.mp hz' with ⟨x, _hx, rfl⟩
  exact x.2

private theorem pathInSet_bypass_support_subset {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V]
    (hconn : (G.induce S).Connected) {a b z : V} (ha : a ∈ S) (hb : b ∈ S)
    (hz : z ∈ ((pathInSet hconn ha hb).bypass).support) :
    z ∈ S := by
  exact pathInSet_support_subset hconn ha hb
    (SimpleGraph.Walk.support_bypass_subset _ hz)

private noncomputable def empty_threeFan {V : Type u} (G : SimpleGraph V) (S : Set V)
    (hconn : (G.induce S).Connected) :
    ThreeFan G S ∅ where
  center := (Classical.choice hconn.nonempty : S)
  center_mem := (Classical.choice hconn.nonempty : S).2
  arm := by
    intro p hp
    exact False.elim (by simpa using hp)
  arm_isPath := by
    intro p hp
    exact False.elim (by simpa using hp)
  arm_support_subset := by
    intro p hp
    exact False.elim (by simpa using hp)
  arm_support_inter_support := by
    intro p q hp
    exact False.elim (by simpa using hp)
  arm_support_inter_ports := by
    intro p q hp
    exact False.elim (by simpa using hp)

private noncomputable def pairArm {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V] (hconn : (G.induce S).Connected) {a b p : V}
    (ha : a ∈ S) (hb : b ∈ S) (hp : p ∈ ({a, b} : Finset V)) :
    G.Walk a p :=
  if hpa : p = a then
    (SimpleGraph.Walk.nil : G.Walk a a).copy rfl hpa.symm
  else
    have hpb : p = b := by
      have hpab : p = a ∨ p = b := by simpa using hp
      exact hpab.resolve_left hpa
    ((pathInSet hconn ha hb).bypass).copy rfl hpb.symm

private theorem pairArm_isPath {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V] (hconn : (G.induce S).Connected) {a b p : V}
    (ha : a ∈ S) (hb : b ∈ S) (hp : p ∈ ({a, b} : Finset V)) :
    (pairArm hconn ha hb hp).IsPath := by
  by_cases hpa : p = a
  · subst p
    simpa [pairArm] using (SimpleGraph.Walk.IsPath.nil :
      (SimpleGraph.Walk.nil : G.Walk a a).IsPath)
  · have hpb : p = b := by
      have hpab : p = a ∨ p = b := by simpa using hp
      exact hpab.resolve_left hpa
    have hba : ¬ b = a := by
      intro h
      exact hpa (hpb.trans h)
    have hpath := pathInSet_isPath hconn ha hb
    subst p
    simpa [pairArm, hba] using hpath

private theorem pairArm_support_subset {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V] (hconn : (G.induce S).Connected) {a b p z : V}
    (ha : a ∈ S) (hb : b ∈ S) (hp : p ∈ ({a, b} : Finset V))
    (hz : z ∈ (pairArm hconn ha hb hp).support) :
    z ∈ S := by
  by_cases hpa : p = a
  · have hza : z = a := by simpa [pairArm, hpa, SimpleGraph.Walk.support_nil] using hz
    exact hza.symm ▸ ha
  · have hpb : p = b := by
      have hpab : p = a ∨ p = b := by simpa using hp
      exact hpab.resolve_left hpa
    have hba : ¬ b = a := by
      intro h
      exact hpa (hpb.trans h)
    have hz' : z ∈ ((pathInSet hconn ha hb).bypass).support := by
      subst p
      simpa [pairArm, hba] using hz
    exact pathInSet_bypass_support_subset hconn ha hb hz'

private theorem pairArm_support_eq_center_of_left {V : Type u} {G : SimpleGraph V}
    {S : Set V} [DecidableEq V] (hconn : (G.induce S).Connected) {a b z : V}
    (ha : a ∈ S) (hb : b ∈ S) (hp : a ∈ ({a, b} : Finset V))
    (hz : z ∈ (pairArm hconn ha hb hp).support) :
    z = a := by
  unfold pairArm at hz
  simp [SimpleGraph.Walk.support_nil] at hz
  exact hz

private noncomputable def pair_threeFan {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V] (hconn : (G.induce S).Connected) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) :
    ThreeFan G S ({a, b} : Finset V) where
  center := a
  center_mem := ha
  arm := fun p hp => pairArm hconn ha hb hp
  arm_isPath := fun p hp => pairArm_isPath hconn ha hb hp
  arm_support_subset := fun p hp z hz => pairArm_support_subset hconn ha hb hp hz
  arm_support_inter_support := by
    intro p q hp hq hpq z hzp hzq
    have hpab : p = a ∨ p = b := by simpa using hp
    have hqab : q = a ∨ q = b := by simpa using hq
    rcases hpab with rfl | rfl
    · exact pairArm_support_eq_center_of_left hconn ha hb hp hzp
    · rcases hqab with rfl | rfl
      · exact pairArm_support_eq_center_of_left hconn ha hb hq hzq
      · exact False.elim (hpq rfl)
  arm_support_inter_ports := by
    intro p q hp hq hqmem
    have hpab : p = a ∨ p = b := by simpa using hp
    have hqab : q = a ∨ q = b := by simpa using hq
    rcases hpab with rfl | rfl
    · left
      exact pairArm_support_eq_center_of_left hconn ha hb hp hqmem
    · rcases hqab with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

private noncomputable def triplePathAB {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V] (hconn : (G.induce S).Connected) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) : G.Walk a b :=
  (pathInSet hconn ha hb).bypass

private theorem triplePathAB_isPath {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V] (hconn : (G.induce S).Connected) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) :
    (triplePathAB hconn ha hb).IsPath :=
  pathInSet_isPath hconn ha hb

private theorem triplePathAB_support_subset {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V] (hconn : (G.induce S).Connected) {a b z : V}
    (ha : a ∈ S) (hb : b ∈ S)
    (hz : z ∈ (triplePathAB hconn ha hb).support) :
    z ∈ S :=
  pathInSet_bypass_support_subset hconn ha hb hz

private structure FirstHit {V : Type u} {G : SimpleGraph V} [DecidableEq V] {a b c : V}
    (P : G.Walk a b) (Q : G.Walk c a) where
  center : V
  center_mem_P : center ∈ P.support
  center_mem_Q : center ∈ Q.support
  first :
    ∀ t : V, t ∈ P.support →
      t ∈ (Q.takeUntil center center_mem_Q).support → t = center

private noncomputable def firstHit {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {a b c : V} (P : G.Walk a b) (Q : G.Walk c a) : FirstHit P Q := by
  classical
  let s : Finset V := P.support.toFinset
  have hne : {x ∈ s | x ∈ Q.support}.Nonempty := by
    refine ⟨a, ?_⟩
    simp [s]
  let ex := Q.exists_mem_support_forall_mem_support_imp_eq s hne
  let x := Classical.choose ex
  have hxspec := Classical.choose_spec ex
  have hxP : x ∈ s := hxspec.1
  let hxQ : x ∈ Q.support := Classical.choose hxspec.2
  have hxfirst :
      ∀ t ∈ s, t ∈ (Q.takeUntil x hxQ).support → t = x :=
    Classical.choose_spec hxspec.2
  refine {
    center := x
    center_mem_P := ?_
    center_mem_Q := hxQ
    first := ?_
  }
  · simpa [s] using hxP
  · intro t htP htQ
    exact hxfirst t (by simpa [s] using htP) htQ

private noncomputable def tripleArm {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V] (hconn : (G.induce S).Connected) {a b c p : V}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hp : p ∈ ({a, b, c} : Finset V)) :
    G.Walk (firstHit (triplePathAB hconn ha hb) (triplePathAB hconn hc ha)).center p :=
  let P := triplePathAB hconn ha hb
  let Q := triplePathAB hconn hc ha
  let F := firstHit P Q
  if hpa : p = a then
    ((P.takeUntil F.center F.center_mem_P).reverse).copy rfl hpa.symm
  else if hpb : p = b then
    (P.dropUntil F.center F.center_mem_P).copy rfl hpb.symm
  else
    have hpc : p = c := by
      have hpabc : p = a ∨ p = b ∨ p = c := by simpa using hp
      exact (hpabc.resolve_left hpa).resolve_left hpb
    ((Q.takeUntil F.center F.center_mem_Q).reverse).copy rfl hpc.symm

private theorem tripleArm_isPath {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V] (hconn : (G.induce S).Connected) {a b c p : V}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hp : p ∈ ({a, b, c} : Finset V)) :
    (tripleArm hconn ha hb hc hp).IsPath := by
  let P := triplePathAB hconn ha hb
  let Q := triplePathAB hconn hc ha
  let F := firstHit P Q
  have hP : P.IsPath := triplePathAB_isPath hconn ha hb
  have hQ : Q.IsPath := triplePathAB_isPath hconn hc ha
  by_cases hpa : p = a
  · subst p
    simpa [tripleArm, P, Q, F] using
      (hP.takeUntil F.center_mem_P).reverse
  · by_cases hpb : p = b
    · subst p
      simpa [tripleArm, P, Q, F, hpa] using
        hP.dropUntil F.center_mem_P
    · have hpc : p = c := by
        have hpabc : p = a ∨ p = b ∨ p = c := by simpa using hp
        exact (hpabc.resolve_left hpa).resolve_left hpb
      have hca : ¬ c = a := by
        intro h
        exact hpa (hpc.trans h)
      have hcb : ¬ c = b := by
        intro h
        exact hpb (hpc.trans h)
      subst p
      simpa [tripleArm, P, Q, F, hca, hcb] using
        (hQ.takeUntil F.center_mem_Q).reverse

private theorem tripleArm_support_subset {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V] (hconn : (G.induce S).Connected) {a b c p z : V}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hp : p ∈ ({a, b, c} : Finset V))
    (hz : z ∈ (tripleArm hconn ha hb hc hp).support) :
    z ∈ S := by
  let P := triplePathAB hconn ha hb
  let Q := triplePathAB hconn hc ha
  let F := firstHit P Q
  by_cases hpa : p = a
  · have hzP : z ∈ P.support := by
      subst p
      have hz' :
          z ∈ ((P.takeUntil F.center F.center_mem_P).reverse).support := by
        simpa [tripleArm, P, Q, F] using hz
      rw [SimpleGraph.Walk.support_reverse] at hz'
      exact P.support_takeUntil_subset F.center_mem_P
        (by simpa using hz')
    exact triplePathAB_support_subset hconn ha hb hzP
  · by_cases hpb : p = b
    · have hzP : z ∈ P.support := by
        subst p
        have hz' : z ∈ (P.dropUntil F.center F.center_mem_P).support := by
          simpa [tripleArm, P, Q, F, hpa] using hz
        exact P.support_dropUntil_subset F.center_mem_P hz'
      exact triplePathAB_support_subset hconn ha hb hzP
    · have hpc : p = c := by
        have hpabc : p = a ∨ p = b ∨ p = c := by simpa using hp
        exact (hpabc.resolve_left hpa).resolve_left hpb
      have hca : ¬ c = a := by
        intro h
        exact hpa (hpc.trans h)
      have hcb : ¬ c = b := by
        intro h
        exact hpb (hpc.trans h)
      have hzQ : z ∈ Q.support := by
        subst p
        have hz' :
            z ∈ ((Q.takeUntil F.center F.center_mem_Q).reverse).support := by
          simpa [tripleArm, P, Q, F, hca, hcb] using hz
        rw [SimpleGraph.Walk.support_reverse] at hz'
        exact Q.support_takeUntil_subset F.center_mem_Q
          (by simpa using hz')
      exact triplePathAB_support_subset hconn hc ha hzQ

private theorem reverse_take_drop_inter_eq_center {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {a b m z : V} {P : G.Walk a b}
    (hP : P.IsPath) (hm : m ∈ P.support)
    (hz_take : z ∈ (P.takeUntil m hm).reverse.support)
    (hz_drop : z ∈ (P.dropUntil m hm).support) :
    z = m := by
  rw [SimpleGraph.Walk.support_reverse] at hz_take
  by_contra hzm
  have hpath :
      ((P.takeUntil m hm).append (P.dropUntil m hm)).IsPath := by
    rw [SimpleGraph.Walk.take_spec]
    exact hP
  exact (hpath.ne_of_mem_support_of_append hzm (by simpa using hz_take) hz_drop) rfl

private theorem reverse_take_qtake_inter_eq_center {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {a b c z : V} {P : G.Walk a b} {Q : G.Walk c a}
    (F : FirstHit P Q)
    (hz_take : z ∈ (P.takeUntil F.center F.center_mem_P).reverse.support)
    (hz_q : z ∈ (Q.takeUntil F.center F.center_mem_Q).reverse.support) :
    z = F.center := by
  rw [SimpleGraph.Walk.support_reverse] at hz_take
  rw [SimpleGraph.Walk.support_reverse] at hz_q
  exact F.first z
    (P.support_takeUntil_subset F.center_mem_P (by simpa using hz_take))
    (by simpa using hz_q)

private theorem drop_qtake_inter_eq_center {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {a b c z : V} {P : G.Walk a b} {Q : G.Walk c a}
    (F : FirstHit P Q)
    (hz_drop : z ∈ (P.dropUntil F.center F.center_mem_P).support)
    (hz_q : z ∈ (Q.takeUntil F.center F.center_mem_Q).reverse.support) :
    z = F.center := by
  rw [SimpleGraph.Walk.support_reverse] at hz_q
  exact F.first z
    (P.support_dropUntil_subset F.center_mem_P hz_drop)
    (by simpa using hz_q)

private theorem end_mem_reverse_take_eq_center {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {a b m : V} {P : G.Walk a b}
    (hP : P.IsPath) (hm : m ∈ P.support)
    (hbmem : b ∈ (P.takeUntil m hm).reverse.support) :
    b = m := by
  rw [SimpleGraph.Walk.support_reverse] at hbmem
  have hbmem' : b ∈ (P.takeUntil m hm).support := by
    simpa using hbmem
  by_contra hbm
  exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil hP hm hbm hbmem'

private theorem start_mem_drop_eq_center {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {a b m : V} {P : G.Walk a b}
    (hP : P.IsPath) (hm : m ∈ P.support)
    (hamem : a ∈ (P.dropUntil m hm).support) :
    a = m := by
  by_contra ham
  have hpath :
      ((P.takeUntil m hm).append (P.dropUntil m hm)).IsPath := by
    rw [SimpleGraph.Walk.take_spec]
    exact hP
  have ha_take : a ∈ (P.takeUntil m hm).support :=
    (P.takeUntil m hm).start_mem_support
  exact (hpath.ne_of_mem_support_of_append ham ha_take hamem) rfl

private noncomputable def triple_threeFan {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V] (hconn : (G.induce S).Connected) {a b c : V}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ThreeFan G S ({a, b, c} : Finset V) where
  center := (firstHit (triplePathAB hconn ha hb) (triplePathAB hconn hc ha)).center
  center_mem := by
    let P := triplePathAB hconn ha hb
    let Q := triplePathAB hconn hc ha
    let F := firstHit P Q
    exact triplePathAB_support_subset hconn ha hb F.center_mem_P
  arm := fun p hp => tripleArm hconn ha hb hc hp
  arm_isPath := fun p hp => tripleArm_isPath hconn ha hb hc hp
  arm_support_subset := fun p hp z hz => tripleArm_support_subset hconn ha hb hc hp hz
  arm_support_inter_support := by
    intro p q hp hq hpq z hzp hzq
    let P := triplePathAB hconn ha hb
    let Q := triplePathAB hconn hc ha
    let F := firstHit P Q
    have hP : P.IsPath := triplePathAB_isPath hconn ha hb
    have hba : ¬ b = a := fun h => hab h.symm
    have hca : ¬ c = a := fun h => hac h.symm
    have hcb : ¬ c = b := fun h => hbc h.symm
    have hpabc : p = a ∨ p = b ∨ p = c := by simpa using hp
    have hqabc : q = a ∨ q = b ∨ q = c := by simpa using hq
    rcases hpabc with rfl | rfl | rfl
    · have hzpA :
          z ∈ (P.takeUntil F.center F.center_mem_P).reverse.support := by
        simpa [tripleArm, P, Q, F] using hzp
      rcases hqabc with rfl | rfl | rfl
      · exact False.elim (hpq rfl)
      · have hzqB : z ∈ (P.dropUntil F.center F.center_mem_P).support := by
          simpa [tripleArm, P, Q, F, hba] using hzq
        exact reverse_take_drop_inter_eq_center hP F.center_mem_P hzpA hzqB
      · have hzqC :
            z ∈ (Q.takeUntil F.center F.center_mem_Q).reverse.support := by
          simpa [tripleArm, P, Q, F, hca, hcb] using hzq
        exact reverse_take_qtake_inter_eq_center F hzpA hzqC
    · have hzpB : z ∈ (P.dropUntil F.center F.center_mem_P).support := by
        simpa [tripleArm, P, Q, F, hba] using hzp
      rcases hqabc with rfl | rfl | rfl
      · have hzqA :
            z ∈ (P.takeUntil F.center F.center_mem_P).reverse.support := by
          simpa [tripleArm, P, Q, F] using hzq
        exact reverse_take_drop_inter_eq_center hP F.center_mem_P hzqA hzpB
      · exact False.elim (hpq rfl)
      · have hzqC :
            z ∈ (Q.takeUntil F.center F.center_mem_Q).reverse.support := by
          simpa [tripleArm, P, Q, F, hca, hcb] using hzq
        exact drop_qtake_inter_eq_center F hzpB hzqC
    · have hzpC :
          z ∈ (Q.takeUntil F.center F.center_mem_Q).reverse.support := by
        simpa [tripleArm, P, Q, F, hca, hcb] using hzp
      rcases hqabc with rfl | rfl | rfl
      · have hzqA :
            z ∈ (P.takeUntil F.center F.center_mem_P).reverse.support := by
          simpa [tripleArm, P, Q, F] using hzq
        exact reverse_take_qtake_inter_eq_center F hzqA hzpC
      · have hzqB : z ∈ (P.dropUntil F.center F.center_mem_P).support := by
          simpa [tripleArm, P, Q, F, hba] using hzq
        exact drop_qtake_inter_eq_center F hzqB hzpC
      · exact False.elim (hpq rfl)
  arm_support_inter_ports := by
    intro p q hp hq hqmem
    let P := triplePathAB hconn ha hb
    let Q := triplePathAB hconn hc ha
    let F := firstHit P Q
    have hP : P.IsPath := triplePathAB_isPath hconn ha hb
    have hba : ¬ b = a := fun h => hab h.symm
    have hca : ¬ c = a := fun h => hac h.symm
    have hcb : ¬ c = b := fun h => hbc h.symm
    have hpabc : p = a ∨ p = b ∨ p = c := by simpa using hp
    have hqabc : q = a ∨ q = b ∨ q = c := by simpa using hq
    rcases hpabc with rfl | rfl | rfl
    · have hpA :
          q ∈ (P.takeUntil F.center F.center_mem_P).reverse.support := by
        simpa [tripleArm, P, Q, F] using hqmem
      rcases hqabc with hqa | hqb | hqc
      · subst q
        exact Or.inr rfl
      · left
        subst q
        exact end_mem_reverse_take_eq_center hP F.center_mem_P hpA
      · left
        subst q
        have hcQ : c ∈ (Q.takeUntil F.center F.center_mem_Q).reverse.support := by
          rw [SimpleGraph.Walk.support_reverse]
          simpa using (Q.takeUntil F.center F.center_mem_Q).start_mem_support
        exact reverse_take_qtake_inter_eq_center F hpA hcQ
    · have hpB : q ∈ (P.dropUntil F.center F.center_mem_P).support := by
        simpa [tripleArm, P, Q, F, hba] using hqmem
      rcases hqabc with hqa | hqb | hqc
      · left
        subst q
        exact start_mem_drop_eq_center hP F.center_mem_P hpB
      · subst q
        exact Or.inr rfl
      · left
        subst q
        have hcQ : c ∈ (Q.takeUntil F.center F.center_mem_Q).reverse.support := by
          rw [SimpleGraph.Walk.support_reverse]
          simpa using (Q.takeUntil F.center F.center_mem_Q).start_mem_support
        exact drop_qtake_inter_eq_center F hpB hcQ
    · have hpC :
          q ∈ (Q.takeUntil F.center F.center_mem_Q).reverse.support := by
        simpa [tripleArm, P, Q, F, hca, hcb] using hqmem
      rcases hqabc with hqa | hqb | hqc
      · left
        subst q
        rw [SimpleGraph.Walk.support_reverse] at hpC
        exact F.first a P.start_mem_support (by simpa using hpC)
      · left
        subst q
        rw [SimpleGraph.Walk.support_reverse] at hpC
        exact F.first b P.end_mem_support (by simpa using hpC)
      · subst q
        exact Or.inr rfl

private noncomputable def empty_indexedFan {V : Type u} {ι : Type v}
    (G : SimpleGraph V) (S : Set V) (target : ι → V)
    (hconn : (G.induce S).Connected) :
    IndexedFan G S ∅ target where
  center := (Classical.choice hconn.nonempty : S)
  center_mem := (Classical.choice hconn.nonempty : S).2
  arm := by
    intro i hi
    exact False.elim (by simpa using hi)
  arm_isPath := by
    intro i hi
    exact False.elim (by simpa using hi)
  arm_support_subset := by
    intro i hi
    exact False.elim (by simpa using hi)
  arm_support_inter_support := by
    intro i j hi
    exact False.elim (by simpa using hi)

private noncomputable def centeredIndexedFan {V : Type u} {ι : Type v}
    {G : SimpleGraph V} {S : Set V} [DecidableEq V]
    (hconn : (G.induce S).Connected) (ports : Finset ι) (target : ι → V)
    (center : V) (hcenter : center ∈ S)
    (htarget : ∀ i : ι, i ∈ ports → target i ∈ S)
    (hunique :
      ∀ ⦃i j : ι⦄ (hi : i ∈ ports) (hj : j ∈ ports),
        target i ≠ center → target j ≠ center → i = j) :
    IndexedFan G S ports target where
  center := center
  center_mem := hcenter
  arm := by
    intro i hi
    if h : target i = center then
      exact (SimpleGraph.Walk.nil : G.Walk center center).copy rfl h.symm
    else
      exact (pathInSet hconn hcenter (htarget i hi)).bypass
  arm_isPath := by
    intro i hi
    by_cases h : target i = center
    · simpa [h] using (SimpleGraph.Walk.IsPath.nil :
        (SimpleGraph.Walk.nil : G.Walk center center).IsPath)
    · simpa [h] using pathInSet_isPath hconn hcenter (htarget i hi)
  arm_support_subset := by
    intro i hi z hz
    by_cases h : target i = center
    · have hzc : z = center := by
        simpa [h, SimpleGraph.Walk.support_nil] using hz
      exact hzc.symm ▸ hcenter
    · exact pathInSet_bypass_support_subset hconn hcenter (htarget i hi)
        (by simpa [h] using hz)
  arm_support_inter_support := by
    intro i j hi hj hij z hzi hzj
    by_cases hi_center : target i = center
    · have hzc : z = center := by
        simpa [hi_center, SimpleGraph.Walk.support_nil] using hzi
      exact hzc
    · by_cases hj_center : target j = center
      · have hzc : z = center := by
          simpa [hj_center, SimpleGraph.Walk.support_nil] using hzj
        exact hzc
      · exact False.elim (hij (hunique hi hj hi_center hj_center))

private noncomputable def indexedPairFan {V : Type u} {ι : Type v}
    {G : SimpleGraph V} {S : Set V} [DecidableEq ι] [DecidableEq V]
    (hconn : (G.induce S).Connected) {target : ι → V} {i j : ι}
    (hij : i ≠ j) (hiS : target i ∈ S) (hjS : target j ∈ S) :
    IndexedFan G S ({i, j} : Finset ι) target := by
  classical
  by_cases ht : target i = target j
  · refine centeredIndexedFan hconn ({i, j} : Finset ι) target (target i) hiS ?_ ?_
    · intro k hk
      have hki : k = i ∨ k = j := by simpa using hk
      rcases hki with rfl | rfl
      · exact hiS
      · exact hjS
    · intro k l hk hl hk_ne hl_ne
      have hki : k = i ∨ k = j := by simpa using hk
      have hli : l = i ∨ l = j := by simpa using hl
      rcases hki with rfl | rfl
      · exact False.elim (hk_ne rfl)
      · exact False.elim (hk_ne ht.symm)
  · let F := pair_threeFan hconn hiS hjS
    refine {
      center := F.center
      center_mem := F.center_mem
      arm := ?_
      arm_isPath := ?_
      arm_support_subset := ?_
      arm_support_inter_support := ?_
    }
    · intro k hk
      if hki : k = i then
        exact (F.arm (target i) (by simp)).copy rfl (by rw [← hki])
      else
        have hkj : k = j := by
          have hki_or : k = i ∨ k = j := by simpa using hk
          exact hki_or.resolve_left hki
        exact (F.arm (target j) (by simp)).copy rfl (by rw [← hkj])
    · intro k hk
      by_cases hki : k = i
      · simpa [hki] using F.arm_isPath (target i) (by simp)
      · have hkj : k = j := by
          have hki_or : k = i ∨ k = j := by simpa using hk
          exact hki_or.resolve_left hki
        have hji : j ≠ i := Ne.symm hij
        simpa [hki, hkj, hji] using F.arm_isPath (target j) (by simp)
    · intro k hk z hz
      by_cases hki : k = i
      · exact F.arm_support_subset (target i) (by simp) z (by
          simpa [hki] using hz)
      · have hkj : k = j := by
          have hki_or : k = i ∨ k = j := by simpa using hk
          exact hki_or.resolve_left hki
        have hji : j ≠ i := Ne.symm hij
        exact F.arm_support_subset (target j) (by simp) z (by
          simpa [hki, hkj, hji] using hz)
    · intro k l hk hl hkl z hzk hzl
      by_cases hki : k = i
      · by_cases hli : l = i
        · exact False.elim (hkl (hki.trans hli.symm))
        · have hlj : l = j := by
            have hli_or : l = i ∨ l = j := by simpa using hl
            exact hli_or.resolve_left hli
          have hji : j ≠ i := Ne.symm hij
          exact F.arm_support_inter_support (by simp) (by simp) ht z
            (by simpa [hki] using hzk) (by simpa [hli, hlj, hji] using hzl)
      · have hkj : k = j := by
          have hki_or : k = i ∨ k = j := by simpa using hk
          exact hki_or.resolve_left hki
        have hji : j ≠ i := Ne.symm hij
        by_cases hli : l = i
        · exact F.arm_support_inter_support (by simp) (by simp) (Ne.symm ht) z
            (by simpa [hki, hkj, hji] using hzk) (by simpa [hli] using hzl)
        · have hlj : l = j := by
            have hli_or : l = i ∨ l = j := by simpa using hl
            exact hli_or.resolve_left hli
          exact False.elim (hkl (hkj.trans hlj.symm))

private noncomputable def indexedTripleFan {V : Type u} {ι : Type v}
    {G : SimpleGraph V} {S : Set V} [DecidableEq ι] [DecidableEq V]
    (hconn : (G.induce S).Connected) {target : ι → V} {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hiS : target i ∈ S) (hjS : target j ∈ S) (hkS : target k ∈ S) :
    IndexedFan G S ({i, j, k} : Finset ι) target := by
  classical
  by_cases hijt : target i = target j
  · refine centeredIndexedFan hconn ({i, j, k} : Finset ι) target (target i) hiS ?_ ?_
    · intro l hl
      have hli : l = i ∨ l = j ∨ l = k := by simpa using hl
      rcases hli with rfl | rfl | rfl
      · exact hiS
      · exact hjS
      · exact hkS
    · intro l m hl hm hl_ne hm_ne
      have hli : l = i ∨ l = j ∨ l = k := by simpa using hl
      have hmi : m = i ∨ m = j ∨ m = k := by simpa using hm
      rcases hli with rfl | rfl | rfl
      · exact False.elim (hl_ne rfl)
      · exact False.elim (hl_ne hijt.symm)
      · rcases hmi with rfl | rfl | rfl
        · exact False.elim (hm_ne rfl)
        · exact False.elim (hm_ne hijt.symm)
        · rfl
  · by_cases hikt : target i = target k
    · refine centeredIndexedFan hconn ({i, j, k} : Finset ι) target (target i) hiS ?_ ?_
      · intro l hl
        have hli : l = i ∨ l = j ∨ l = k := by simpa using hl
        rcases hli with rfl | rfl | rfl
        · exact hiS
        · exact hjS
        · exact hkS
      · intro l m hl hm hl_ne hm_ne
        have hli : l = i ∨ l = j ∨ l = k := by simpa using hl
        have hmi : m = i ∨ m = j ∨ m = k := by simpa using hm
        rcases hli with rfl | rfl | rfl
        · exact False.elim (hl_ne rfl)
        · rcases hmi with rfl | rfl | rfl
          · exact False.elim (hm_ne rfl)
          · rfl
          · exact False.elim (hm_ne hikt.symm)
        · exact False.elim (hl_ne hikt.symm)
    · by_cases hjkt : target j = target k
      · refine centeredIndexedFan hconn ({i, j, k} : Finset ι) target (target j) hjS ?_ ?_
        · intro l hl
          have hli : l = i ∨ l = j ∨ l = k := by simpa using hl
          rcases hli with rfl | rfl | rfl
          · exact hiS
          · exact hjS
          · exact hkS
        · intro l m hl hm hl_ne hm_ne
          have hli : l = i ∨ l = j ∨ l = k := by simpa using hl
          have hmi : m = i ∨ m = j ∨ m = k := by simpa using hm
          rcases hli with rfl | rfl | rfl
          · rcases hmi with rfl | rfl | rfl
            · rfl
            · exact False.elim (hm_ne rfl)
            · exact False.elim (hm_ne hjkt.symm)
          · exact False.elim (hl_ne rfl)
          · exact False.elim (hl_ne hjkt.symm)
      · let F := triple_threeFan hconn hiS hjS hkS hijt hikt hjkt
        refine {
          center := F.center
          center_mem := F.center_mem
          arm := ?_
          arm_isPath := ?_
          arm_support_subset := ?_
          arm_support_inter_support := ?_
        }
        · intro l hl
          if hli : l = i then
            exact (F.arm (target i) (by simp)).copy rfl (by rw [← hli])
          else if hlj : l = j then
            exact (F.arm (target j) (by simp)).copy rfl (by rw [← hlj])
          else
            have hlk : l = k := by
              have hli_or : l = i ∨ l = j ∨ l = k := by simpa using hl
              exact (hli_or.resolve_left hli).resolve_left hlj
            exact (F.arm (target k) (by simp)).copy rfl (by rw [← hlk])
        · intro l hl
          by_cases hli : l = i
          · simpa [hli] using F.arm_isPath (target i) (by simp)
          · by_cases hlj : l = j
            · have hji : j ≠ i := Ne.symm hij
              simpa [hli, hlj, hji] using F.arm_isPath (target j) (by simp)
            · have hlk : l = k := by
                have hli_or : l = i ∨ l = j ∨ l = k := by simpa using hl
                exact (hli_or.resolve_left hli).resolve_left hlj
              have hki : k ≠ i := Ne.symm hik
              have hkj : k ≠ j := Ne.symm hjk
              simpa [hli, hlj, hlk, hki, hkj] using F.arm_isPath (target k) (by simp)
        · intro l hl z hz
          by_cases hli : l = i
          · exact F.arm_support_subset (target i) (by simp) z (by
              simpa [hli] using hz)
          · by_cases hlj : l = j
            · have hji : j ≠ i := Ne.symm hij
              exact F.arm_support_subset (target j) (by simp) z (by
                simpa [hli, hlj, hji] using hz)
            · have hlk : l = k := by
                have hli_or : l = i ∨ l = j ∨ l = k := by simpa using hl
                exact (hli_or.resolve_left hli).resolve_left hlj
              have hki : k ≠ i := Ne.symm hik
              have hkj : k ≠ j := Ne.symm hjk
              exact F.arm_support_subset (target k) (by simp) z (by
                simpa [hli, hlj, hlk, hki, hkj] using hz)
        · intro a b ha hb hab z hza hzb
          by_cases hai : a = i
          · by_cases hbi : b = i
            · exact False.elim (hab (hai.trans hbi.symm))
            · by_cases hbj : b = j
              · have hji : j ≠ i := Ne.symm hij
                exact F.arm_support_inter_support (by simp) (by simp) hijt z
                  (by simpa [hai] using hza)
                  (by simpa [hbi, hbj, hji] using hzb)
              · have hbk : b = k := by
                  have hb_cases : b = i ∨ b = j ∨ b = k := by simpa using hb
                  exact (hb_cases.resolve_left hbi).resolve_left hbj
                have hki : k ≠ i := Ne.symm hik
                have hkj : k ≠ j := Ne.symm hjk
                exact F.arm_support_inter_support (by simp) (by simp) hikt z
                  (by simpa [hai] using hza)
                  (by simpa [hbi, hbj, hbk, hki, hkj] using hzb)
          · by_cases haj : a = j
            · by_cases hbi : b = i
              · have hji : j ≠ i := Ne.symm hij
                exact F.arm_support_inter_support (by simp) (by simp) (Ne.symm hijt) z
                  (by simpa [hai, haj, hji] using hza)
                  (by simpa [hbi] using hzb)
              · by_cases hbj : b = j
                · exact False.elim (hab (haj.trans hbj.symm))
                · have hbk : b = k := by
                    have hb_cases : b = i ∨ b = j ∨ b = k := by simpa using hb
                    exact (hb_cases.resolve_left hbi).resolve_left hbj
                  have hji : j ≠ i := Ne.symm hij
                  have hki : k ≠ i := Ne.symm hik
                  have hkj : k ≠ j := Ne.symm hjk
                  exact F.arm_support_inter_support (by simp) (by simp) hjkt z
                    (by simpa [hai, haj, hji] using hza)
                    (by simpa [hbi, hbj, hbk, hki, hkj] using hzb)
            · have hak : a = k := by
                have ha_cases : a = i ∨ a = j ∨ a = k := by simpa using ha
                exact (ha_cases.resolve_left hai).resolve_left haj
              by_cases hbi : b = i
              · have hki : k ≠ i := Ne.symm hik
                have hkj : k ≠ j := Ne.symm hjk
                exact F.arm_support_inter_support (by simp) (by simp) (Ne.symm hikt) z
                  (by simpa [hai, haj, hak, hki, hkj] using hza)
                  (by simpa [hbi] using hzb)
              · by_cases hbj : b = j
                · have hji : j ≠ i := Ne.symm hij
                  have hki : k ≠ i := Ne.symm hik
                  have hkj : k ≠ j := Ne.symm hjk
                  exact F.arm_support_inter_support (by simp) (by simp) (Ne.symm hjkt) z
                    (by simpa [hai, haj, hak, hki, hkj] using hza)
                    (by simpa [hbi, hbj, hji] using hzb)
                · have hbk : b = k := by
                    have hb_cases : b = i ∨ b = j ∨ b = k := by simpa using hb
                    exact (hb_cases.resolve_left hbi).resolve_left hbj
                  exact False.elim (hab (hak.trans hbk.symm))

theorem exists_indexedFan_of_card_le_three {V : Type u} {ι : Type v}
    {G : SimpleGraph V} {S : Set V} [DecidableEq ι] [DecidableEq V]
    (ports : Finset ι) (target : ι → V)
    (hconn : (G.induce S).Connected)
    (htarget : ∀ i : ι, i ∈ ports → target i ∈ S)
    (hcard : ports.card ≤ 3) :
    ∃ F : IndexedFan G S ports target, True := by
  have hcases : ports.card = 0 ∨ ports.card = 1 ∨ ports.card = 2 ∨ ports.card = 3 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3
  · have hports_eq : ports = ∅ := Finset.card_eq_zero.mp h0
    subst ports
    exact ⟨empty_indexedFan G S target hconn, trivial⟩
  · obtain ⟨i, hports_eq⟩ := Finset.card_eq_one.mp h1
    subst ports
    exact ⟨centeredIndexedFan hconn ({i} : Finset ι) target (target i)
      (htarget i (by simp)) (fun j hj => htarget j hj) (by
        intro j k hj hk hj_ne hk_ne
        have hji : j = i := by simpa using hj
        have hki : k = i := by simpa using hk
        exact hji.trans hki.symm), trivial⟩
  · obtain ⟨i, j, hij, hports_eq⟩ := Finset.card_eq_two.mp h2
    subst ports
    exact ⟨indexedPairFan hconn hij (htarget i (by simp)) (htarget j (by simp)), trivial⟩
  · obtain ⟨i, j, k, hij, hik, hjk, hports_eq⟩ := Finset.card_eq_three.mp h3
    subst ports
    exact ⟨indexedTripleFan hconn hij hik hjk
      (htarget i (by simp)) (htarget j (by simp)) (htarget k (by simp)), trivial⟩

theorem exists_threeFan_of_card_le_three {V : Type u} {G : SimpleGraph V} {S : Set V}
    [DecidableEq V] (ports : Finset V)
    (hconn : (G.induce S).Connected)
    (hports : ∀ p : V, p ∈ ports → p ∈ S)
    (hcard : ports.card ≤ 3) :
    ∃ F : ThreeFan G S ports, True := by
  have hcases : ports.card = 0 ∨ ports.card = 1 ∨ ports.card = 2 ∨ ports.card = 3 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3
  · have hports_eq : ports = ∅ := Finset.card_eq_zero.mp h0
    subst ports
    exact ⟨empty_threeFan G S hconn, trivial⟩
  · obtain ⟨a, hports_eq⟩ := Finset.card_eq_one.mp h1
    subst ports
    exact ⟨singleton_threeFan G S (hports a (by simp)), trivial⟩
  · obtain ⟨a, b, hab, hports_eq⟩ := Finset.card_eq_two.mp h2
    subst ports
    exact ⟨pair_threeFan hconn (hports a (by simp)) (hports b (by simp)), trivial⟩
  · obtain ⟨a, b, c, hab, hac, hbc, hports_eq⟩ := Finset.card_eq_three.mp h3
    subst ports
    exact ⟨triple_threeFan hconn
      (hports a (by simp)) (hports b (by simp)) (hports c (by simp))
      hab hac hbc, trivial⟩

end Chapter01
end Diestel
