import Yau.LeafProofs.L16SpatialBootstrap

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def parabolicFirstDeriv {n : ℕ} (Q : Set (Point n)) (u : Point n → ℝ) (p : Point n) :
    Point n →L[ℝ] ℝ :=
  (spatialD u p).comp (ContinuousLinearMap.fst ℝ (Space n) ℝ)+
    (ContinuousLinearMap.snd ℝ (Space n) ℝ).smulRight (timeD Q u p)

theorem c2_hasFDerivWithinAt {n : ℕ} {T : ℝ} {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    HasFDerivWithinAt u (parabolicFirstDeriv (cylinder Set.univ 0 T) u p)
      (cylinder Set.univ 0 T) p := by
  letI : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
  let Q : Set (Point n) := cylinder Set.univ 0 T
  have hFst (q : Point n) : ‖q.1-p.1‖ ≤ ‖q-p‖ := by
    change ‖q.1-p.1‖ ≤ max ‖q.1-p.1‖ ‖q.2-p.2‖
    exact le_max_left _ _
  have hSnd (q : Point n) : ‖q.2-p.2‖ ≤ ‖q-p‖ := by
    change ‖q.2-p.2‖ ≤ max ‖q.1-p.1‖ ‖q.2-p.2‖
    exact le_max_right _ _
  have hSpatial : (fun q : Point n => u q-u (p.1,q.2)-spatialD u p (q.1-p.1)) =o[𝓝[Q] p] (fun q => q-p) := by
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    obtain ⟨δ,hδ,hCont⟩ := Metric.continuousWithinAt_iff.mp (hu.2.1 p hp) c hc
    have hδ2 : 0 < δ/2 := by positivity
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds p hδ2)] with q hq hqp
    have hqp' : ‖q-p‖ < δ/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hqp
    let B : Set (Space n) := Metric.closedBall p.1 (δ/2)
    have hDeriv (x : Space n) : HasFDerivAt (fun y => u (y,q.2)-spatialD u p y)
        (spatialD u (x,q.2)-spatialD u p) x :=
      ((hu.2.2.2.2.1 (x,q.2) ⟨Set.mem_univ _,hq.2⟩).differentiableAt (by norm_num)).hasFDerivAt.sub
        (spatialD u p).hasFDerivAt
    have hBound (x : Space n) (hx : x ∈ B) : ‖spatialD u (x,q.2)-spatialD u p‖ ≤ c := by
      have hx' : ‖x-p.1‖ ≤ δ/2 := by simpa only [B,Metric.mem_closedBall,dist_eq_norm] using hx
      have hDist : dist (x,q.2) p < δ := by
        rw [dist_eq_norm]
        change max ‖x-p.1‖ ‖q.2-p.2‖ < δ
        exact max_lt_iff.mpr ⟨lt_of_le_of_lt hx' (by linarith),
          (hSnd q).trans_lt (hqp'.trans (by linarith))⟩
      have hc' := hCont (x := (x,q.2)) ⟨Set.mem_univ _,hq.2⟩ hDist
      have hc'' : ‖spatialD u (x,q.2)-spatialD u p‖ < c := by
        simpa only [dist_eq_norm] using hc'
      exact hc''.le
    have hx : p.1 ∈ B := by simp only [B,Metric.mem_closedBall,dist_self]; positivity
    have hy : q.1 ∈ B := by
      simpa only [B,Metric.mem_closedBall,dist_eq_norm] using ((hFst q).trans_lt hqp').le
    have hMV := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x (_ : x ∈ B) => (hDeriv x).hasFDerivWithinAt) hBound (convex_closedBall p.1 (δ/2)) hx hy
    have hEq : u q-u (p.1,q.2)-spatialD u p (q.1-p.1) =
        (u (q.1,q.2)-spatialD u p q.1)-(u (p.1,q.2)-spatialD u p p.1) := by
      rw [map_sub]
      ring
    rw [hEq]
    exact hMV.trans (mul_le_mul_of_nonneg_left (hFst q) hc.le)
  have hTime : HasDerivWithinAt (fun t => u (p.1,t)) (timeD Q u p) (Set.Icc 0 T) p.2 := by
    simpa only [timeD,Q,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,Set.mem_univ,true_and,Set.ofPred_mem_eq]
      using (hu.2.2.2.2.2 p hp).hasDerivWithinAt
  have hSndTendsto : Tendsto (fun q : Point n => q.2) (𝓝[Q] p) (𝓝[Set.Icc 0 T] p.2) := by
    have hMem : ∀ᶠ q : Point n in 𝓝[Q] p, q ∈ Q := self_mem_nhdsWithin
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      hMem.mono (fun q hq => hq.2)⟩
  have hSndO : (fun q : Point n => q.2-p.2) =O[𝓝[Q] p] (fun q => q-p) := by
    exact Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall (fun q => by simpa only [one_mul] using hSnd q))
  have hTemporal := (hTime.isLittleO.comp_tendsto hSndTendsto).trans_isBigO hSndO
  apply HasFDerivWithinAt.of_isLittleO
  have hSum := hSpatial.add hTemporal
  convert hSum using 1
  funext q
  simp only [parabolicFirstDeriv,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.coe_snd',
    Prod.fst_sub,Prod.snd_sub,smul_eq_mul,Function.comp_apply,Q]
  ring

theorem parabolicFirstDeriv_continuousOn {n : ℕ} {T : ℝ} {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) :
    ContinuousOn (fun p => parabolicFirstDeriv (cylinder Set.univ 0 T) u p) (cylinder Set.univ 0 T) := by
  have hSpace := hu.2.1.clm_comp (continuousOn_const (c := ContinuousLinearMap.fst ℝ (Space n) ℝ))
  have hTime := (ContinuousLinearMap.smulRightL ℝ (Point n) ℝ
    (ContinuousLinearMap.snd ℝ (Space n) ℝ)).continuous.comp_continuousOn hu.2.2.2.1
  exact hSpace.add hTime

theorem c2_fderivWithin {n : ℕ} {T : ℝ} (hT : 0 < T) {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    fderivWithin ℝ u (cylinder Set.univ 0 T) p = parabolicFirstDeriv (cylinder Set.univ 0 T) u p :=
  (c2_hasFDerivWithinAt hu hp).fderivWithin ((uniqueDiffOn_univ.prod (uniqueDiffOn_Icc hT)) p hp)

theorem c2_contDiffOn_one {n : ℕ} {T : ℝ} (hT : 0 < T) {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) : ContDiffOn ℝ 1 u (cylinder Set.univ 0 T) := by
  have hCont : ContinuousOn (fderivWithin ℝ u (cylinder Set.univ 0 T)) (cylinder Set.univ 0 T) :=
    (parabolicFirstDeriv_continuousOn hu).congr (fun p hp => c2_fderivWithin hT hu hp)
  have h := contDiffOn_succ_of_fderivWithin
    (fun p hp => (c2_hasFDerivWithinAt hu hp).differentiableWithinAt)
    (show (0 : ℕ∞ω) = ω → AnalyticOn ℝ u (cylinder Set.univ 0 T) from by simp)
    (contDiffOn_zero.mpr hCont)
  simpa only [zero_add] using h

end Yau.LeafProofs.L16Aux
