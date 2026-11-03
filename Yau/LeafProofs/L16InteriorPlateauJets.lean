import Yau.LeafProofs.L16InteriorHighBound

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem innerPatchBump_eventually_one_of_inside {n : ℕ} {r : ℝ}
    (hr : 0 < r) (c : Space n) {y : Space n} (hy : ‖y-c‖ < r) :
    (innerPatchBump r hr c : Space n → ℝ) =ᶠ[𝓝 y] (fun _ => 1) := by
  have hBall : y ∈ Metric.ball c r := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
  filter_upwards [Metric.isOpen_ball.mem_nhds hBall] with z hz
  apply innerPatchBump_eq_one hr
  simpa only [dist_eq_norm] using (Metric.mem_ball.mp hz).le

theorem initialTimeCutoff_eventually_one_of_plateau {T v : ℝ}
    (hT : 0 < T) (hv : T/2 < v) :
    initialTimeCutoff T =ᶠ[𝓝 v] (fun _ => 1) := by
  filter_upwards [Ioi_mem_nhds hv] with t ht
  exact initialTimeCutoff_eq_one hT ht.le

theorem classicalInteriorPatch_spatialDD_on_plateau {n : ℕ} {δ h σ v : ℝ}
    (hδ : 0 < δ) (hh : 0 < h) (c : Space n) {y : Space n} (u : Point n → ℝ)
    (hv : localSchauderTime δ h/2 ≤ v) (hy : ‖y-c‖ < h/8) :
    spatialDD (classicalInteriorPatch δ h σ hh c u) (y,v) =
      spatialDD u (y,v+σ) := by
  let T : ℝ := localSchauderTime δ h
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hθ : initialTimeCutoff T v = 1 := initialTimeCutoff_eq_one hT hv
  have hφ := innerPatchBump_eventually_one_of_inside (n := n) (r := h/8) (by positivity) c hy
  have hEq : (fun x : Space n => classicalInteriorPatch δ h σ hh c u (x,v)) =ᶠ[𝓝 y]
      (fun x => u (x,v+σ)) := by
    filter_upwards [hφ] with x hx
    dsimp only [classicalInteriorPatch,timeTranslate,timeTranslatePoint]
    rw [hθ,hx,one_mul,one_mul]
  simpa only [spatialDD] using (hEq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)

theorem classicalInteriorPatch_timeD_on_plateau {n : ℕ} {δ h σ v : ℝ}
    (hδ : 0 < δ) (hh : 0 < h) (c : Space n) {y : Space n} (u : Point n → ℝ)
    (hv : localSchauderTime δ h/2 < v) (hy : ‖y-c‖ < h/8) :
    timeD (cylinder Set.univ 0 (localSchauderTime δ h))
      (classicalInteriorPatch δ h σ hh c u) (y,v) =
    timeD (cylinder Set.univ 0 (localSchauderTime δ h))
      (timeTranslate σ u) (y,v) := by
  let T : ℝ := localSchauderTime δ h
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hφ : innerPatchBump (h/8) (by positivity) c y = 1 :=
    innerPatchBump_eq_one (by positivity) hy.le
  have hEq : (fun t : ℝ => classicalInteriorPatch δ h σ hh c u (y,t)) =ᶠ[𝓝 v]
      (fun t => timeTranslate σ u (y,t)) := by
    filter_upwards [initialTimeCutoff_eventually_one_of_plateau hT hv] with t ht
    dsimp only [classicalInteriorPatch]
    rw [ht,hφ,one_mul,one_mul]
  simpa only [timeD,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,
    Set.mem_univ,true_and,Set.ofPred_mem_eq] using hEq.derivWithin_eq_of_nhds (s := Set.Icc 0 T)

theorem timeD_timeTranslate_backward_on_slab {n : ℕ} {T σ R v : ℝ}
    (hT : 0 < T) (hσ : -(R^2) < σ) (hEnd : T+σ ≤ 0) (hv : v ∈ Set.Icc 0 T)
    {c : Space n} (hc : c ∈ Metric.ball 0 R) {u : Point n → ℝ}
    (hu : C2 (backward R) u) :
    timeD (cylinder Set.univ 0 T) (timeTranslate σ u) (c,v) =
      timeD (backward R) u (c,v+σ) := by
  have hp : ((c,v+σ) : Point n) ∈ backward R :=
    ⟨hc,by linarith [hv.1],by linarith [hv.2]⟩
  have hBack : {t : ℝ | (c,t) ∈ backward R} = Set.Ioc (-(R^2)) 0 := by
    ext t
    simp [backward,hc]
  have hSlice : {t : ℝ | (c,t) ∈ cylinder (n := n) Set.univ 0 T} = Set.Icc 0 T := by
    ext t
    simp [Yau.Parabolic.cylinder]
  have hDeriv : HasDerivWithinAt (fun t => u (c,t))
      (timeD (backward R) u (c,v+σ)) (Set.Ioc (-(R^2)) 0) (v+σ) := by
    simpa only [timeD,hBack] using (hu.2.2.2.2.2 (c,v+σ) hp).hasDerivWithinAt
  have hComp := hDeriv.comp v ((hasDerivAt_id v).add_const σ).hasDerivWithinAt
    (show Set.MapsTo (fun t : ℝ => t+σ) (Set.Icc 0 T) (Set.Ioc (-(R^2)) 0) from by
      intro t ht
      exact ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hValue := hComp.derivWithin (uniqueDiffOn_Icc hT v hv)
  simpa only [timeD,hSlice,timeTranslate,timeTranslatePoint,Function.comp_def,id_eq,mul_one] using hValue

theorem timeD_backward_restrict_radius {n : ℕ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) {u : Point n → ℝ} (hu : C2 (backward R) u)
    {p : Point n} (hp : p ∈ backward r) :
    timeD (backward r) u p = timeD (backward R) u p := by
  have hSpace : p.1 ∈ Metric.ball 0 R := Metric.ball_subset_ball hrR hp.1
  have hSmall : {t | (p.1,t) ∈ backward r} = Set.Ioc (-(r^2)) 0 := by
    ext t
    simp [backward,hp.1]
  have hLarge : {t | (p.1,t) ∈ backward R} = Set.Ioc (-(R^2)) 0 := by
    ext t
    simp [backward,hSpace]
  have hSq := pow_le_pow_left₀ hr hrR 2
  have hSub : Set.Ioc (-(r^2)) (0 : ℝ) ⊆ Set.Ioc (-(R^2)) 0 :=
    Set.Ioc_subset_Ioc (by linarith) le_rfl
  simp only [timeD,hSmall,hLarge]
  apply derivWithin_subset hSub (uniqueDiffOn_Ioc _ _ p.2 hp.2)
  simpa only [hLarge] using hu.2.2.2.2.2 p ⟨hSpace,hSub hp.2⟩

theorem c2_backward_restrict_radius {n : ℕ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) {u : Point n → ℝ} (hu : C2 (backward R) u) :
    C2 (backward r) u := by
  have hSq := pow_le_pow_left₀ hr hrR 2
  have hSub : backward (n := n) r ⊆ backward R := by
    intro p hp
    exact ⟨Metric.ball_subset_ball hrR hp.1,by linarith [hp.2.1],hp.2.2⟩
  refine ⟨hu.1.mono hSub,hu.2.1.mono hSub,hu.2.2.1.mono hSub,?_,
    fun p hp => hu.2.2.2.2.1 p (hSub hp),?_⟩
  · exact (hu.2.2.2.1.mono hSub).congr (fun p hp => timeD_backward_restrict_radius hr hrR hu hp)
  · intro p hp
    exact (hu.2.2.2.2.2 p (hSub hp)).mono (fun t ht => hSub ht)

end Yau.LeafProofs.L16Aux
