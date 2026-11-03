import Yau.Proofs.P03CircleFubini
import Yau.Proofs.P03LineMean

open scoped Topology
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

theorem circleAverage_integral_swap {k : ComplexVector n → ℝ}
    {h : ComplexVector n → ℂ} {r : ℝ} (hk : Continuous k) (hkc : HasCompactSupport k)
    (hks : tsupport k ⊆ Metric.closedBall 0 r) (hc : Continuous h)
    (x : ComplexVector n) :
    Real.circleAverage (fun c : ℂ => ∫ y, k y • h (x - c • y)) 0 1 =
      ∫ y, k y • Real.circleAverage (fun c : ℂ => h (x - c • y)) 0 1 := by
  have hi := circleKernelIntegrand_integrable hk hkc hks hc x
  have hi' : Integrable (Function.uncurry (fun (θ : ℝ) (y : ComplexVector n) =>
      k y • h (x - circleMap 0 1 θ • y)))
      (((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi))).prod volume) := by
    convert! hi using 1
  have hswap := integral_integral_swap hi'
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  calc
    (2 * Real.pi)⁻¹ • (∫ θ in Set.Ioc 0 (2 * Real.pi),
        ∫ y : ComplexVector n, k y • h (x - circleMap 0 1 θ • y)) =
        (2 * Real.pi)⁻¹ • (∫ y : ComplexVector n,
          ∫ θ in Set.Ioc 0 (2 * Real.pi), k y • h (x - circleMap 0 1 θ • y)) := by
      exact congrArg (fun z : ℂ => (2 * Real.pi)⁻¹ • z) hswap
    _ = ∫ y : ComplexVector n, (2 * Real.pi)⁻¹ •
        (∫ θ in Set.Ioc 0 (2 * Real.pi), k y • h (x - circleMap 0 1 θ • y)) :=
      (integral_smul _ _).symm
    _ = ∫ y, k y • Real.circleAverage (fun c : ℂ => h (x - c • y)) 0 1 := by
      apply integral_congr_ae
      filter_upwards with y
      rw [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le,
        integral_smul]
      exact smul_comm _ _ _

/-- A fixed normalized radial kernel reproduces holomorphic functions.
The several-variable statement uses only the proved real phase isometry,
the integrable Fubini identity, and native one-variable circle mean value. -/
theorem radial_smoothing_eq {k : ComplexVector n → ℝ} {h : ComplexVector n → ℂ}
    {r : ℝ} {a x : ComplexVector n}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hks : tsupport k ⊆ Metric.closedBall 0 r) (hkmass : (∫ y, k y) = 1)
    (hkinv : ∀ c : ℂ, ‖c‖ = 1 → ∀ y, k (c • y) = k y)
    (hc : Continuous h) (hh : DifferentiableOn ℂ h (Metric.ball a (3 * r)))
    (hx : x ∈ Metric.ball a (2 * r)) : smoothBy k h x = h x := by
  have hphase : ∀ c ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|,
      (∫ y, k y • h (x - c • y)) = smoothBy k h x := by
    intro c hcirc
    have hc1 : ‖c‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hcirc
    exact (smoothBy_phase_change k h c hc1 (hkinv c hc1) x).symm
  have havg := Real.circleAverage_const_on_circle hphase
  calc
    smoothBy k h x =
        Real.circleAverage (fun c : ℂ => ∫ y, k y • h (x - c • y)) 0 1 := havg.symm
    _ = ∫ y, k y • Real.circleAverage (fun c : ℂ => h (x - c • y)) 0 1 :=
      circleAverage_integral_swap hk hkc hks hc x
    _ = ∫ y, k y • h x := by
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ tsupport k
      · have hnorm : ‖y‖ ≤ r := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hks hy
        rw [circleAverage_affineLine hc hh hx hnorm]
      · have hk0 := image_eq_zero_of_notMem_tsupport hy
        simp only [hk0, zero_smul]
    _ = h x := by rw [integral_smul_const, hkmass, one_smul]

end Yau.NodeProofs.P03Aux
