import Yau.LeafProofs.L16OriginalInteriorPatches

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem innerPatchBump_eventually_one {n : ℕ} {r : ℝ} (hr : 0 < r) (c : Space n) :
    (innerPatchBump r hr c : Space n → ℝ) =ᶠ[𝓝 c] (fun _ => 1) := by
  filter_upwards [Metric.ball_mem_nhds c hr] with x hx
  apply innerPatchBump_eq_one hr
  simpa only [dist_eq_norm] using (Metric.mem_ball.mp hx).le

theorem initialTimeCutoff_eventually_one {T : ℝ} (hT : 0 < T) :
    initialTimeCutoff T =ᶠ[𝓝 T] (fun _ => 1) := by
  filter_upwards [Ioi_mem_nhds (show T/2 < T by linarith)] with t ht
  exact initialTimeCutoff_eq_one hT ht.le

theorem classicalInteriorPatch_spatialDD_at_top {n : ℕ} {δ h σ : ℝ}
    (hδ : 0 < δ) (hh : 0 < h) (c : Space n) (u : Point n → ℝ) :
    spatialDD (classicalInteriorPatch δ h σ hh c u) (c,localSchauderTime δ h) =
      spatialDD u (c,localSchauderTime δ h+σ) := by
  let T : ℝ := localSchauderTime δ h
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hθ : initialTimeCutoff T T = 1 := initialTimeCutoff_eq_one hT (by linarith)
  have hφ := innerPatchBump_eventually_one (n := n) (r := h/8) (by positivity) c
  have hEq : (fun x : Space n => classicalInteriorPatch δ h σ hh c u (x,T)) =ᶠ[𝓝 c]
      (fun x => u (x,T+σ)) := by
    filter_upwards [hφ] with x hx
    dsimp only [classicalInteriorPatch,timeTranslate,timeTranslatePoint]
    rw [hθ,hx,one_mul,one_mul]
  simpa only [spatialDD] using (hEq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)

theorem classicalInteriorPatch_timeD_at_top {n : ℕ} {δ h σ : ℝ}
    (hδ : 0 < δ) (hh : 0 < h) (c : Space n) (u : Point n → ℝ) :
    timeD (cylinder Set.univ 0 (localSchauderTime δ h))
      (classicalInteriorPatch δ h σ hh c u) (c,localSchauderTime δ h) =
    timeD (cylinder Set.univ 0 (localSchauderTime δ h))
      (timeTranslate σ u) (c,localSchauderTime δ h) := by
  let T : ℝ := localSchauderTime δ h
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hφ : innerPatchBump (h/8) (by positivity) c c = 1 :=
    innerPatchBump_eq_one (by positivity) (by simp; positivity)
  have hEq : (fun t : ℝ => classicalInteriorPatch δ h σ hh c u (c,t)) =ᶠ[𝓝 T]
      (fun t => timeTranslate σ u (c,t)) := by
    filter_upwards [initialTimeCutoff_eventually_one hT] with t ht
    dsimp only [classicalInteriorPatch]
    rw [ht,hφ,one_mul,one_mul]
  have hSlice : {t : ℝ | (c,t) ∈ cylinder (n := n) Set.univ 0 T} = Set.Icc 0 T := by
    ext t
    simp [Yau.Parabolic.cylinder]
  simpa only [timeD,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,
    Set.mem_univ,true_and,Set.ofPred_mem_eq] using hEq.derivWithin_eq_of_nhds (s := Set.Icc 0 T)

theorem timeD_timeTranslate_backward_at_top {n : ℕ} {T σ R : ℝ}
    (hT : 0 < T) (hσ : -(R^2) < σ) (hEnd : T+σ ≤ 0)
    {c : Space n} (hc : c ∈ Metric.ball 0 R) {u : Point n → ℝ}
    (hu : C2 (backward R) u) :
    timeD (cylinder Set.univ 0 T) (timeTranslate σ u) (c,T) =
      timeD (backward R) u (c,T+σ) := by
  have hp : ((c,T+σ) : Point n) ∈ backward R := ⟨hc,by linarith,hEnd⟩
  have hBack : {t : ℝ | (c,t) ∈ backward R} = Set.Ioc (-(R^2)) 0 := by
    ext t
    simp [backward,hc]
  have hSlice : {t : ℝ | (c,t) ∈ cylinder (n := n) Set.univ 0 T} = Set.Icc 0 T := by
    ext t
    simp [Yau.Parabolic.cylinder]
  have hDeriv : HasDerivWithinAt (fun t => u (c,t))
      (timeD (backward R) u (c,T+σ)) (Set.Ioc (-(R^2)) 0) (T+σ) := by
    simpa only [timeD,hBack] using (hu.2.2.2.2.2 (c,T+σ) hp).hasDerivWithinAt
  have hComp := hDeriv.comp T ((hasDerivAt_id T).add_const σ).hasDerivWithinAt
    (show Set.MapsTo (fun t : ℝ => t+σ) (Set.Icc 0 T) (Set.Ioc (-(R^2)) 0) from by
      intro t ht
      exact ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hValue := hComp.derivWithin (uniqueDiffOn_Icc hT T ⟨hT.le,le_rfl⟩)
  simpa only [timeD,hSlice,timeTranslate,timeTranslatePoint,Function.comp_def,id_eq,mul_one] using hValue

end Yau.LeafProofs.L16Aux
