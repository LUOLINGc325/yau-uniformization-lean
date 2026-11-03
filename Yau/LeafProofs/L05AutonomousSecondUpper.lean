import Yau.LeafProofs.L05AutonomousJointHessianRepresentation
import Yau.LeafProofs.L05AutonomousTimeIncrements
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Positive smooth second FTC and the actual uniform convolution limit preserve
an arbitrary real upper budget exactly. In particular M need not be nonnegative. -/
theorem auto_second_upper_from_joint_mollifications {n : ℕ}
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ))
    (e : Space n) {h : ℝ} (hh : h≠0) (p : Point n) {M delta : ℝ} (hdelta : 0 < delta)
    (hUpper : ∀ eps : ℝ, 0 < eps → eps < delta → ∀ s∈Icc (-1 : ℝ) 1,
      fderiv ℝ (fderiv ℝ (abpMollify eps w)) (p+(s*h) • (e,0)) (e,0) (e,0) ≤ M) :
    autoSecond w e h p ≤ M := by
  let eps := autoDyadicStep (delta/2)
  have heps (j : ℕ) : 0 < eps j := auto_dyadicStep_pos (half_pos hdelta) j
  have hepsSmall (j : ℕ) : eps j < delta :=
    (auto_dyadicStep_le (half_pos hdelta).le j).trans_lt (half_lt_self hdelta)
  have hSecond (j : ℕ) : autoSecond (abpMollify (eps j) w) e h p ≤ M := by
    let : IsProbabilityMeasure autoTentMeasure := autoTentMeasure_isProbability
    have hSmooth := abpMollify_smooth (heps j) w.continuous
    have hD : Continuous (fun z : Point n =>
        fderiv ℝ (fderiv ℝ (abpMollify (eps j) w)) z (e,0) (e,0)) :=
      (((((hSmooth.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
        contDiff_const).clm_apply contDiff_const).continuous)
    have hPath : Continuous (fun s : ℝ => p+(s*h) • (e,0)) :=
      continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const)
    have hInt := autoTentMeasure_continuous_integrable (hD.comp hPath)
    rw [auto_joint_second_as_probability hSmooth p e hh]
    have hm := integral_mono_ae hInt (integrable_const M) (by
      filter_upwards [autoTentMeasure_interval_ae] with s hs
      exact hUpper _ (heps j) (hepsSmall j) s hs)
    simpa only [integral_const,probReal_univ,one_smul,Function.comp_def] using hm
  have hUniform := auto_joint_mollify_uniform w hw eps heps (auto_dyadicStep_tendsto _)
  have hPlus := hUniform.tendsto_at (p.1+h • e,p.2)
  have hMinus := hUniform.tendsto_at (p.1-h • e,p.2)
  have hCenter := hUniform.tendsto_at p
  have hLimit : Tendsto (fun j => autoSecond (abpMollify (eps j) w) e h p) atTop
      (𝓝 (autoSecond w e h p)) := by
    simpa only [autoSecond] using ((hPlus.add hMinus).sub (hCenter.const_mul 2)).div_const (h^2)
  exact le_of_tendsto hLimit (Eventually.of_forall hSecond)

/-- The full space-time a.e. upper bound of the actual directional Peano limit
controls the finite difference at EVERY point whose spatial segment is in O.
The compact segment supplies a true common convolution neighborhood. -/
theorem auto_second_upper_of_ae_directional_limit {n : ℕ} {O : Set (Point n)} (hO : IsOpen O)
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ))
    {H : Point n → ℝ} (hH : Measurable H) (e : Space n) {h : ℝ} (hh : h≠0) (p : Point n)
    (hSegment : ∀ s∈Icc (-1 : ℝ) 1, p+(s*h) • (e,0)∈O)
    (steps : ℕ → ℝ) (hpos : ∀ j, 0 < steps j) (hzero : Tendsto steps atTop (𝓝 0))
    {B M : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ j, ∀ z∈O, |autoSecond w e (steps j) z| ≤ B)
    (hLimit : ∀ᵐ z ∂((volume : Measure (Point n)).restrict O),
      Tendsto (fun j => autoSecond w e (steps j) z) atTop (𝓝 (H z)))
    (hUpper : ∀ᵐ z ∂((volume : Measure (Point n)).restrict O), H z ≤ M) :
    autoSecond w e h p ≤ M := by
  let path : ℝ → Point n := fun s => p+(s*h) • (e,0)
  have hPath : Continuous path :=
    continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const)
  let S := path '' Icc (-1 : ℝ) 1
  have hS : IsCompact S := isCompact_Icc.image hPath
  have hSO : S⊆O := by
    rintro z ⟨s,hs,rfl⟩
    exact hSegment s hs
  obtain ⟨delta,hdelta,hTube⟩ := hS.exists_thickening_subset_open hO hSO
  apply auto_second_upper_from_joint_mollifications w hw e hh p hdelta
  intro eps heps hepsSmall s hs
  have hRegion : ∀ q∈Metric.ball (0 : Point n) eps, path s-q∈O := by
    intro q hq
    apply hTube
    apply Metric.mem_thickening_iff.mpr
    refine ⟨path s,⟨s,hs,rfl⟩,?_⟩
    have hqn : ‖q‖ < eps := by simpa only [Metric.mem_ball,dist_zero_right] using hq
    rw [dist_eq_norm,show path s-q-path s=-q by abel,norm_neg]
    exact hqn.trans hepsSmall
  exact auto_joint_mollify_second_upper_along hO.measurableSet heps w hH e (path s)
    hRegion steps hpos hzero hB hBound hLimit hUpper

/-- The exact directional upper bound holds on the CLOSED half-cylinder,
including its genuine top face, by continuity of the actual finite difference. -/
theorem auto_second_upper_closed_half {n : ℕ} (c : Space n) {R : ℝ} (hR : 0 < R) (T : ℝ)
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ))
    {H : Point n → ℝ} (hH : Measurable H) (e : Space n) (he : ‖e‖ ≤ 1)
    (steps : ℕ → ℝ) (hpos : ∀ j, 0 < steps j) (hzero : Tendsto steps atTop (𝓝 0))
    {B M : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ j, ∀ z∈autoOpen c R T, |autoSecond w e (steps j) z| ≤ B)
    (hLimit : ∀ᵐ z ∂((volume : Measure (Point n)).restrict (autoOpen c R T)),
      Tendsto (fun j => autoSecond w e (steps j) z) atTop (𝓝 (H z)))
    (hUpper : ∀ᵐ z ∂((volume : Measure (Point n)).restrict (autoOpen c R T)), H z ≤ M)
    {h : ℝ} (hh : h≠0) (hhR : |h| < R/4) :
    ∀ p∈autoClosed c (R/2) T, autoSecond w e h p ≤ M := by
  have hOpen : ∀ p∈autoOpen c (R/2) T, autoSecond w e h p ≤ M := by
    intro p hp
    apply auto_second_upper_of_ae_directional_limit (autoOpen_isOpen c R T) w hw hH e hh p
      ?_ steps hpos hzero hB hBound hLimit hUpper
    intro s hs
    have hsabs : |s| ≤ 1 := abs_le.mpr hs
    have hShift : ‖(s*h) • e‖ ≤ |h| := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul]
      calc
        _ ≤ 1*|h| *1 := by gcongr
        _ = _ := by ring
    have hDist : dist (p.1+(s*h) • e) c ≤ dist p.1 c+‖(s*h) • e‖ := by
      rw [dist_eq_norm,dist_eq_norm,show p.1+(s*h) • e-c=(p.1-c)+(s*h) • e by abel]
      exact norm_add_le _ _
    have hpDist : dist p.1 c < R/2 := hp.1
    have hpTime : T-(R/2)^2 < p.2 ∧ p.2 < T := hp.2
    have hSpatial : dist (p.1+(s*h) • e) c < R := by
      linarith only [hDist,hShift,hpDist,hhR,hR]
    have hTime : T-R^2 < p.2 ∧ p.2 < T :=
      ⟨by nlinarith only [hpTime.1,sq_pos_of_pos hR],hpTime.2⟩
    simpa [autoOpen] using
      (show p.1+(s*h) • e∈Metric.ball c R ∧ p.2∈Ioo (T-R^2) T from ⟨hSpatial,hTime⟩)
  have hClosure : closure (autoOpen c (R/2) T)=autoClosed c (R/2) T := by
    rw [autoOpen,autoClosed,closure_prod_eq,closure_ball c (half_pos hR).ne',
      closure_Ioo (by nlinarith only [sq_pos_of_pos hR] : T-(R/2)^2≠T)]
  intro p hp
  have hpClosure : p∈closure (autoOpen c (R/2) T) := by rwa [hClosure]
  exact le_on_closure hOpen (autoSecond_continuous w.continuous e h).continuousOn
    continuousOn_const hpClosure

end Yau.LeafProofs.L05AutonomousAux
