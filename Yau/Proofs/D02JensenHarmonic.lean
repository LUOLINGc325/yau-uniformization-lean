import Yau.LeafProofs.L08
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Topology.TietzeExtension

open MeasureTheory Filter Set InnerProductSpace
open scoped Topology ContDiff

noncomputable section
namespace Yau.NodeProofs.D02JensenAux

/-- The frozen real Laplacian zero condition gives genuine Euclidean
harmonicity on the open disc. -/
theorem harmonicOnNhd_of_laplacian_zero {h : ℂ → ℝ} {O : Set ℂ}
    (hO : IsOpen O) (hh : ContDiffOn ℝ ∞ h O)
    (hΔ : ∀ z ∈ O, LeafCandidates.realPlanarLaplacian h z = 0) :
    HarmonicOnNhd h O := by
  intro z hz
  refine ⟨(hh.contDiffAt (hO.mem_nhds hz)).of_le (by simp), ?_⟩
  filter_upwards [hO.mem_nhds hz] with w hw
  rw [← LeafProofs.L08_realPlanarLaplacian_eq_laplacian
    ((hh.contDiffAt (hO.mem_nhds hw)).of_le (by simp))]
  exact hΔ w hw

/-- A harmonic function has an interior pointwise bound depending only on
its L¹ norm on a fixed larger closed disc. No pointwise lower bound is an input. -/
theorem harmonic_abs_le_L1 {h : ℂ → ℝ} {z₀ z : ℂ} {R : ℝ} (hR : 0 < R)
    (hh : ContDiffOn ℝ ∞ h (Metric.ball z₀ R))
    (hΔ : ∀ w ∈ Metric.ball z₀ R, LeafCandidates.realPlanarLaplacian h w = 0)
    (hz : z ∈ Metric.ball z₀ (R / 4)) :
    |h z| ≤ (∫ w in Metric.closedBall z₀ (R / 2), |h w|) /
      (Real.pi * ((R / 4) ^ 2 - (R / 8) ^ 2)) := by
  let a := R / 8
  let b := R / 4
  let A := {w : ℂ | a < ‖w - z‖ ∧ ‖w - z‖ < b}
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := by dsimp [a, b]; linarith
  have hb : 0 < b := ha.trans hab
  have hsmall : Metric.closedBall z b ⊆ Metric.ball z₀ R := by
    intro w hw
    have hd := dist_triangle w z z₀
    have hw' : dist w z ≤ b := hw
    have hz' : dist z z₀ < R / 4 := hz
    change dist w z₀ < R
    dsimp [b] at hw'
    linarith
  have hH := harmonicOnNhd_of_laplacian_zero Metric.isOpen_ball hh hΔ
  have hct : ContinuousOn h (Metric.closedBall z b) := hh.continuousOn.mono hsmall
  let f : C(Metric.closedBall z b, ℝ) := ⟨fun w ↦ h w, continuousOn_iff_continuous_domRestrict.mp hct⟩
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq Metric.isClosed_closedBall f
  have hFeq : ∀ w ∈ Metric.closedBall z b, F w = h w := by
    intro w hw
    exact congrArg (fun g : C(Metric.closedBall z b, ℝ) ↦ g ⟨w, hw⟩) hF
  have hG : Continuous (fun w ↦ -|F w|) := F.continuous.abs.neg
  have hcircle : ∀ t ∈ Icc a b,
      Yau.circleAverage (fun θ ↦ -|F (z + t * Complex.exp (θ * Complex.I))|) ≤ -|h z| := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have hmean : Real.circleAverage h z t = h z := by
      apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
      simpa only [abs_of_pos ht0] using hH.mono ((Metric.closedBall_subset_closedBall ht.2).trans hsmall)
    have hn := Real.abs_circleAverage_le_circleAverage_abs (f := h) (c := z) (R := t)
    rw [hmean] at hn
    have heq : Real.circleAverage (fun w ↦ -|F w|) z t =
        -Real.circleAverage (fun w ↦ |h w|) z t := by
      calc
        _ = Real.circleAverage (fun w ↦ -|h w|) z t := by
          apply Real.circleAverage_congr_sphere
          intro w hw
          dsimp only
          rw [hFeq w ((Metric.closedBall_subset_closedBall ht.2)
            (Metric.sphere_subset_closedBall (by simpa only [abs_of_pos ht0] using hw)))]
        _ = _ := by simp [Real.circleAverage_def, intervalIntegral.integral_neg, smul_eq_mul]
    have hY : Yau.circleAverage (fun θ ↦ -|F (z + t * Complex.exp (θ * Complex.I))|) =
        Real.circleAverage (fun w ↦ -|F w|) z t := by
      simp only [Yau.circleAverage, Real.circleAverage_def, circleMap, smul_eq_mul]
    rw [hY, heq]
    exact neg_le_neg hn
  have hupper := LeafProofs.L08_continuous_annulus_upper_bound hG ha hab hcircle
  change (∫ w in A, -|F w|) ≤ -|h z| * (Real.pi * (b ^ 2 - a ^ 2)) at hupper
  rw [integral_neg] at hupper
  have hApos : 0 < Real.pi * (b ^ 2 - a ^ 2) := by
    apply mul_pos Real.pi_pos
    nlinarith
  have hAK : A ⊆ Metric.closedBall z₀ (R / 2) := by
    intro w hw
    have hd := dist_triangle w z z₀
    have hw' : dist w z < b := by simpa only [dist_eq_norm] using hw.2
    have hz' : dist z z₀ < R / 4 := hz
    change dist w z₀ ≤ R / 2
    dsimp [b] at hw'
    linarith
  have hKA : Metric.closedBall z₀ (R / 2) ⊆ Metric.ball z₀ R := by
    intro w hw
    change dist w z₀ < R
    have hw' : dist w z₀ ≤ R / 2 := hw
    linarith
  have hi : IntegrableOn (fun w ↦ |h w|) (Metric.closedBall z₀ (R / 2)) volume :=
    ((hh.continuousOn.mono hKA).abs).integrableOn_compact (isCompact_closedBall _ _)
  have hFA : (∫ w in A, |F w|) = ∫ w in A, |h w| := by
    apply setIntegral_congr_fun
      (((isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
        (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)).measurableSet)
    intro w hw
    dsimp only
    rw [hFeq w (by change dist w z ≤ b; simpa only [dist_eq_norm] using hw.2.le)]
  rw [hFA] at hupper
  have hmono := setIntegral_mono_set hi (Filter.Eventually.of_forall fun w ↦ abs_nonneg (h w))
    hAK.eventuallyLE
  apply (le_div_iff₀ hApos).mpr
  exact (by nlinarith : |h z| * (Real.pi * (b ^ 2 - a ^ 2)) ≤ ∫ w in A, |h w|).trans hmono

end Yau.NodeProofs.D02JensenAux
