import Yau.Proofs.V02HarmonicExtension
import Yau.Proofs.V03ScalarAreaFourier
import Yau.Proofs.V03GagliardoVector

/-! The real part of a genuine holomorphic disc controls its real
Dirichlet energy, with the original Fourier and area normalizations. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint Yau.LeafProofs

theorem realPart_gradient_sq_of_holomorphic {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discEnergyRealGradientSq (fun w => (f w).re) z = ‖fderiv ℂ f z 1‖ ^ 2 := by
  have hd : DifferentiableAt ℂ f z :=
    (hf.contDiffAt (discEnergy_closedBall_mem_nhds hz)).differentiableAt (by simp)
  have he : fderiv ℝ (fun w => (f w).re) z =
      Complex.reCLM.comp ((fderiv ℂ f z).restrictScalars ℝ) :=
    (Complex.reCLM.hasFDerivAt.comp z (hd.hasFDerivAt.restrictScalars ℝ)).fderiv
  have hI : fderiv ℂ f z Complex.I = Complex.I * fderiv ℂ f z 1 := by
    simpa only [smul_eq_mul, mul_one] using (fderiv ℂ f z).map_smul Complex.I (1 : ℂ)
  unfold discEnergyRealGradientSq
  rw [discEnergyPartial_eq_fderiv _ _ hz, discEnergyPartial_eq_fderiv _ _ hz, he]
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
  change (fderiv ℂ f z 1).re ^ 2 + (fderiv ℂ f z Complex.I).re ^ 2 = ‖fderiv ℂ f z 1‖ ^ 2
  rw [hI, Complex.I_mul_re, discEnergy_norm_sq_re_im]
  ring

theorem normDiscArea_eq_realPartGradient {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    V03Proof.normDiscArea f = ENNReal.ofReal
      (2 * ∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq (fun w => (f w).re) z) := by
  have ha := V03Proof.normDiscArea_radial_eq_integral hf (r := 1) (by simp)
  simp only [Complex.ofReal_one, one_mul, V03Proof.radialEuclideanDensity, one_smul] at ha
  rw [ha, ← integral_const_mul]
  congr 1
  apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
  intro z hz
  dsimp only
  rw [realPart_gradient_sq_of_holomorphic hf hz, V03Proof.closedDiscDerivative,
    fderivWithin_of_mem_nhds (discEnergy_closedBall_mem_nhds hz)]

theorem boundaryDSq_realPart_le_energy {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    scalarDSq (fun θ => (f (circlePoint θ)).re) ≤ ENNReal.ofReal
      ((Real.pi)⁻¹ * ∫ z in Metric.ball (0 : ℂ) 1,
        discEnergyRealGradientSq (fun w => (f w).re) z) := by
  have hc : Continuous (fun θ => f (circlePoint θ)) :=
    hf.continuousOn.comp_continuous V03Proof.circlePoint_contDiff.continuous
      V03Proof.circlePoint_mem_closedBall
  have hp := V03Proof.circleTrace_periodic f
  have hproject : scalarDSq (fun θ => (f (circlePoint θ)).re) ≤
      boundaryDSq (fun θ (_ : Unit) => f (circlePoint θ)) := by
    have h := V03Proof.boundaryDSq_le_of_sum_square_bound
      (u := fun θ (_ : Unit) => f (circlePoint θ))
      (v := fun θ => ((f (circlePoint θ)).re : ℂ))
      (fun _ => hc) (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hc))
      (fun _ => hp) (fun θ => congrArg (fun z : ℂ => (z.re : ℂ)) (hp θ))
      (C := 1) (by norm_num) (by
        intro θ t
        have hnorm := Complex.abs_re_le_norm (f (circlePoint θ) - f (circlePoint t))
        simp only [Finset.univ_unique, Finset.sum_singleton, one_mul,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.sub_re]
        simp only [Complex.sub_re] at hnorm
        nlinarith [abs_nonneg ((f (circlePoint θ)).re - (f (circlePoint t)).re),
          norm_nonneg (f (circlePoint θ) - f (circlePoint t))])
    simpa only [ENNReal.ofReal_one, one_mul, scalarDSq] using h
  calc
    _ ≤ _ := hproject
    _ = _ := by
      rw [V03Proof.boundaryDSq_scalar_eq_inverse_area hf,
        normDiscArea_eq_realPartGradient hf,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
      congr 1
      field_simp
      <;> ring

end Yau.Blueprint.V02Proof
