import Chapter02.two_factor_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

open TwoFactorAux

/--
Diestel, Corollary 2.1.5 (Petersen).
Every finite regular graph of positive even degree has a 2-factor.
-/
theorem corollary_2_1_5 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (k : ℕ) :
  1 ≤ k →
    G.IsRegularOfDegree (2 * k) →
      HasKFactor G 2 := by
  intro hk hreg
  classical
  letI : DecidableEq V := Classical.decEq V
  have hEuler : ∀ C : G.ConnectedComponent, Diestel.Chapter01.IsEulerian C.toSimpleGraph := by
    intro C
    exact TwoFactorAux.connectedComponent_toSimpleGraph_eulerian_of_even_regular G hreg C
  let base : (C : G.ConnectedComponent) → C := fun C => Classical.choose (hEuler C)
  let tour : (C : G.ConnectedComponent) → C.toSimpleGraph.Walk (base C) (base C) :=
    fun C => Classical.choose (Classical.choose_spec (hEuler C))
  have htour : ∀ C : G.ConnectedComponent, (tour C).IsEulerian := by
    intro C
    simpa [Diestel.Chapter01.IsEulerTour, tour, base] using
      (Classical.choose_spec (Classical.choose_spec (hEuler C)))
  let orientedDarts : G.ConnectedComponent → List G.Dart :=
    fun C => (tour C).darts.map (TwoFactorAux.liftComponentDart C)
  let R : V → V → Prop := fun x y =>
    ∃ d : G.Dart, d ∈ orientedDarts (G.connectedComponentMk x) ∧ d.fst = x ∧ d.snd = y
  letI : DecidableRel R := Classical.decRel _
  apply TwoFactorAux.hasKFactor_two_of_regular_orientation G R hk
  · intro x y hxy
    rcases hxy with ⟨d, _hd, hfst, hsnd⟩
    simpa [hfst, hsnd] using d.adj
  · intro x y hxy hyx
    rcases hxy with ⟨dxy, hdxy, hxy_fst, hxy_snd⟩
    rcases hyx with ⟨dyx, hdyx, hyx_fst, hyx_snd⟩
    let C := G.connectedComponentMk x
    have hcomp_yx : G.connectedComponentMk y = C := by
      have hadj_yx : G.Adj y x := by
        simpa [hyx_fst, hyx_snd] using dyx.adj
      simpa [C] using SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj_yx
    have hdyx' : dyx ∈ orientedDarts C := by
      simpa [R, orientedDarts, hcomp_yx] using hdyx
    have hdxy' : dxy ∈ orientedDarts C := by
      simpa [R, C] using hdxy
    have hnodup : ((orientedDarts C).map SimpleGraph.Dart.edge).Nodup := by
      simpa [orientedDarts] using
        (TwoFactorAux.liftedDartList_edges_nodup C (tour C) (htour C))
    have hedge : dxy.edge = dyx.edge := by
      have hedgexy : dxy.edge = s(x, y) := by
        rw [SimpleGraph.dart_edge_eq_mk'_iff']
        exact Or.inl ⟨hxy_fst, hxy_snd⟩
      have hedgeyx : dyx.edge = s(y, x) := by
        rw [SimpleGraph.dart_edge_eq_mk'_iff']
        exact Or.inl ⟨hyx_fst, hyx_snd⟩
      calc
        dxy.edge = s(x, y) := hedgexy
        _ = s(y, x) := Sym2.eq_swap
        _ = dyx.edge := hedgeyx.symm
    have hdart_eq : dxy = dyx :=
      List.inj_on_of_nodup_map hnodup hdxy' hdyx' hedge
    have hxy_eq : x = y := by
      calc
        x = dxy.fst := hxy_fst.symm
        _ = dyx.fst := congrArg (fun d : G.Dart => d.fst) hdart_eq
        _ = y := hyx_fst
    have hloop : dxy.fst = dxy.snd := by
      calc
        dxy.fst = x := hxy_fst
        _ = y := hxy_eq
        _ = dxy.snd := hxy_snd.symm
    exact dxy.fst_ne_snd hloop
  · intro v
    let C := G.connectedComponentMk v
    let vv : C := ⟨v, rfl⟩
    have hnodup : ((orientedDarts C).map SimpleGraph.Dart.edge).Nodup := by
      simpa [orientedDarts] using
        (TwoFactorAux.liftedDartList_edges_nodup C (tour C) (htour C))
    have hcard := TwoFactorAux.natCard_dart_targets_eq_countP G (orientedDarts C) hnodup v
    have hcount : (orientedDarts C).countP (fun d => d.fst = v) = k := by
      letI : DecidablePred (fun x : V => x ∈ C.supp) := Classical.decPred _
      letI : Fintype C := Subtype.fintype (fun x : V => x ∈ C.supp)
      letI : DecidableRel C.toSimpleGraph.Adj := by
        dsimp [SimpleGraph.ConnectedComponent.toSimpleGraph, SimpleGraph.induce]
        infer_instance
      change ((tour C).darts.map (TwoFactorAux.liftComponentDart C)).countP
        (fun d => d.fst = v) = k
      rw [TwoFactorAux.liftedDarts_countP_fst C (tour C) vv]
      apply TwoFactorAux.eulerian_count_out_eq_half_degree C.toSimpleGraph (htour C)
      have hdegree : C.toSimpleGraph.degree vv = G.degree v := by
        exact SimpleGraph.degree_induce_of_neighborSet_subset (G := G) (s := C.supp)
          (v := vv) (by
            intro w hw
            exact (C.mem_supp_congr_adj hw).mp vv.2)
      rw [hdegree, hreg.degree_eq v]
    simpa [R, orientedDarts, C] using hcard.trans hcount
  · intro v
    let C := G.connectedComponentMk v
    let vv : C := ⟨v, rfl⟩
    have hnodup : ((orientedDarts C).map SimpleGraph.Dart.edge).Nodup := by
      simpa [orientedDarts] using
        (TwoFactorAux.liftedDartList_edges_nodup C (tour C) (htour C))
    have hcard := TwoFactorAux.natCard_dart_sources_eq_countP G (orientedDarts C) hnodup v
    have hcount : (orientedDarts C).countP (fun d => d.snd = v) = k := by
      letI : DecidablePred (fun x : V => x ∈ C.supp) := Classical.decPred _
      letI : Fintype C := Subtype.fintype (fun x : V => x ∈ C.supp)
      letI : DecidableRel C.toSimpleGraph.Adj := by
        dsimp [SimpleGraph.ConnectedComponent.toSimpleGraph, SimpleGraph.induce]
        infer_instance
      change ((tour C).darts.map (TwoFactorAux.liftComponentDart C)).countP
        (fun d => d.snd = v) = k
      rw [TwoFactorAux.liftedDarts_countP_snd C (tour C) vv]
      apply TwoFactorAux.eulerian_count_in_eq_half_degree C.toSimpleGraph (htour C)
      have hdegree : C.toSimpleGraph.degree vv = G.degree v := by
        exact SimpleGraph.degree_induce_of_neighborSet_subset (G := G) (s := C.supp)
          (v := vv) (by
            intro w hw
            exact (C.mem_supp_congr_adj hw).mp vv.2)
      rw [hdegree, hreg.degree_eq v]
    have hiff : ∀ w : V,
        R w v ↔ ∃ d : G.Dart, d ∈ orientedDarts C ∧ d.snd = v ∧ d.fst = w := by
      intro w
      constructor
      · intro hwv
        rcases hwv with ⟨d, hd, hfst, hsnd⟩
        have hadj_wv : G.Adj w v := by
          simpa [hfst, hsnd] using d.adj
        have hcomp : G.connectedComponentMk w = C := by
          simpa [C] using SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj_wv
        exact ⟨d, by simpa [hcomp] using hd, hsnd, hfst⟩
      · rintro ⟨d, hd, hsnd, hfst⟩
        have hadj_wv : G.Adj w v := by
          simpa [hfst, hsnd] using d.adj
        refine ⟨d, ?_, hfst, hsnd⟩
        simpa [C, SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj_wv] using hd
    have htarget : Nat.card {w : V // R w v} =
        Nat.card {w : V // ∃ d : G.Dart, d ∈ orientedDarts C ∧ d.snd = v ∧ d.fst = w} := by
      exact Nat.card_congr (Equiv.subtypeEquivRight hiff)
    rw [htarget]
    exact hcard.trans hcount

end Chapter02
end Diestel
