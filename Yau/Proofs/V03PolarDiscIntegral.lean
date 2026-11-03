import Yau.Proofs.V03PolarGradient
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! The native complex change of variables gives the actual unit-disc
integral in the polar rectangle with its exact radial Jacobian. -/

open scoped Topology
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem polarDiscPoint_eq_polarCoord (p : ℝ × ℝ) :
    polarDiscPoint p = Complex.polarCoord.symm p := by
  simp only [polarDiscPoint, Complex.polarCoord_symm_apply, circlePoint, Complex.exp_mul_I,
    Complex.ofReal_cos, Complex.ofReal_sin]

theorem integral_unitDisc_eq_polar {g : ℂ → ℝ}
    (hg : ContinuousOn g (Metric.closedBall (0 : ℂ) 1)) :
    (∫ z in Metric.ball (0 : ℂ) 1, g z) =
      ∫ r in (0 : ℝ)..1, ∫ θ in (-Real.pi)..Real.pi, r * g (polarDiscPoint (r, θ)) := by
  let R := Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi
  let f : ℝ × ℝ → ℝ := fun p => p.1 * g (polarDiscPoint p)
  have hC : ContinuousOn f (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-Real.pi) Real.pi) := by
    exact continuousOn_fst.mul (hg.comp polarDiscPoint_contDiff.continuous.continuousOn
      (fun p hp => polarDiscPoint_mem_closedDisc hp.1))
  have hi : IntegrableOn f R :=
    (hC.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
  have hindicator : polarCoord.target.indicator
      (fun p : ℝ × ℝ => p.1 * (Metric.ball (0 : ℂ) 1).indicator g (Complex.polarCoord.symm p)) =
      R.indicator f := by
    funext p
    by_cases hp : p ∈ polarCoord.target
    · by_cases hz : polarDiscPoint p ∈ Metric.ball (0 : ℂ) 1
      · have hr : p ∈ R := by
          refine ⟨⟨hp.1, ?_⟩, hp.2⟩
          simpa only [Metric.mem_ball, dist_zero_right, polarDiscPoint_norm,
            abs_of_pos (show 0 < p.1 from hp.1)] using hz
        simp only [Set.indicator_of_mem hp, ← polarDiscPoint_eq_polarCoord,
          Set.indicator_of_mem hz, Set.indicator_of_mem hr, f]
      · have hr : p ∉ R := fun h => hz (polarDiscPoint_mem_ball h.1)
        simp only [Set.indicator_of_mem hp, ← polarDiscPoint_eq_polarCoord,
          Set.indicator_of_notMem hz, mul_zero, Set.indicator_of_notMem hr]
    · have hr : p ∉ R := fun h => hp ⟨h.1.1, h.2⟩
      simp only [Set.indicator_of_notMem hp, Set.indicator_of_notMem hr]
  have hh := Complex.integral_comp_polarCoord_symm ((Metric.ball (0 : ℂ) 1).indicator g)
  simp only [smul_eq_mul] at hh
  rw [← integral_indicator polarCoord.open_target.measurableSet, hindicator,
    integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo), integral_indicator measurableSet_ball] at hh
  rw [Measure.volume_eq_prod] at hi hh
  rw [setIntegral_prod f hi] at hh
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  apply hh.symm.trans
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  dsimp only
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo]

end Yau.Blueprint.V03Proof
