import Yau.Proofs.V02HarmonicEnergy
import Yau.Proofs.V02HolomorphicRealEnergy
import Yau.Proofs.V02DiscTraceL2

/-! The full homogeneous H¹/² trace estimate for an arbitrary smooth
closed-disc function. The original function is never assumed holomorphic. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint Yau.LeafProofs

theorem real_disc_Hhalf_bound {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    scalarDSq (realDiscTrace u) ≤ ENNReal.ofReal
      ((Real.pi)⁻¹ * ∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq u z) := by
  let f := V03Proof.outerExponent (realDiscTrace u) 1
  have hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1) :=
    V03Proof.outerExponent_contDiffOn (realDiscTrace_contDiff hu) (realDiscTrace_periodic u) 1
  have hB : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = realHarmonicExtension u z := by
    intro z hz
    have hn : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    have he : circlePoint (Complex.arg z) = z := by
      simpa only [circlePoint, hn, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z
    simpa only [he] using (realHarmonicExtension_boundary hu (Complex.arg z)).symm
  have hmin := real_harmonic_energy_minimizes hu (realHarmonicExtension_contDiffOn hu) hB
    (fun _ hz => realHarmonicExtension_laplacian hu hz)
  have heq : realDiscTrace u = fun θ => (f (circlePoint θ)).re := by
    funext θ
    exact (realHarmonicExtension_boundary hu θ).symm
  calc
    _ = scalarDSq (fun θ => (f (circlePoint θ)).re) := congrArg scalarDSq heq
    _ ≤ ENNReal.ofReal ((Real.pi)⁻¹ * ∫ z in Metric.ball (0 : ℂ) 1,
        discEnergyRealGradientSq (realHarmonicExtension u) z) := boundaryDSq_realPart_le_energy hf
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmin (by positivity))

theorem complex_disc_Hhalf_bound {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    boundaryDSq (fun θ (_ : Unit) => u (circlePoint θ)) ≤ ENNReal.ofReal
      ((Real.pi)⁻¹ * ∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z) := by
  have hur : ContDiffOn ℝ ∞ (fun z => (u z).re) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.reCLM.contDiff.comp_contDiffOn hu
  have hui : ContDiffOn ℝ ∞ (fun z => (u z).im) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.imCLM.contDiff.comp_contDiffOn hu
  have hc : Continuous (fun θ => u (circlePoint θ)) :=
    hu.continuousOn.comp_continuous V03Proof.circlePoint_contDiff.continuous
      V03Proof.circlePoint_mem_closedBall
  have hp := V03Proof.circleTrace_periodic u
  let U : ℝ → Fin 2 → ℂ := fun θ => ![((u (circlePoint θ)).re : ℂ), ((u (circlePoint θ)).im : ℂ)]
  have hUc (i : Fin 2) : Continuous (fun θ => U θ i) := by
    fin_cases i
    · exact Complex.continuous_ofReal.comp (Complex.continuous_re.comp hc)
    · exact Complex.continuous_ofReal.comp (Complex.continuous_im.comp hc)
  have hUp (i : Fin 2) : Function.Periodic (fun θ => U θ i) (2 * Real.pi) := by
    intro θ
    exact congrArg (fun v : ℂ => ![(v.re : ℂ), (v.im : ℂ)] i) (hp θ)
  have hproj := V03Proof.boundaryDSq_le_of_sum_square_bound hUc hc hUp hp
    (C := 1) (by norm_num) (by
      intro θ t
      simp only [U, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [discEnergy_norm_sq_re_im]
      simp only [Complex.sub_re, Complex.sub_im]
      exact le_rfl)
  have hsplit : boundaryDSq U =
      scalarDSq (realDiscTrace (fun z => (u z).re)) +
        scalarDSq (realDiscTrace (fun z => (u z).im)) := by
    rw [V03Proof.boundaryDSq_eq_sum_singleton, Fin.sum_univ_two]
    rfl
  rw [ENNReal.ofReal_one, one_mul, hsplit] at hproj
  have hGr := discEnergy_integrableOn (discEnergyRealGradientSq_continuousOn hur)
  have hGi := discEnergy_integrableOn (discEnergyRealGradientSq_continuousOn hui)
  have hG : (∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z) =
      (∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq (fun w => (u w).re) z) +
        (∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq (fun w => (u w).im) z) := by
    calc
      _ = ∫ z in Metric.ball (0 : ℂ) 1,
          discEnergyRealGradientSq (fun w => (u w).re) z +
            discEnergyRealGradientSq (fun w => (u w).im) z :=
        setIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun z hz =>
          discEnergyGradientSq_re_im hu (Metric.ball_subset_closedBall hz))
      _ = _ := integral_add hGr hGi
  calc
    _ ≤ _ := hproj
    _ ≤ ENNReal.ofReal ((Real.pi)⁻¹ * ∫ z in Metric.ball (0 : ℂ) 1,
        discEnergyRealGradientSq (fun w => (u w).re) z) +
      ENNReal.ofReal ((Real.pi)⁻¹ * ∫ z in Metric.ball (0 : ℂ) 1,
        discEnergyRealGradientSq (fun w => (u w).im) z) :=
      add_le_add (real_disc_Hhalf_bound hur) (real_disc_Hhalf_bound hui)
    _ = _ := by
      have hnon : 0 ≤ Real.pi⁻¹ * ∫ z in Metric.ball (0 : ℂ) 1,
          discEnergyRealGradientSq (fun w => (u w).re) z :=
        mul_nonneg (by positivity) (integral_nonneg (fun z =>
          add_nonneg (sq_nonneg _) (sq_nonneg _)))
      rw [← ENNReal.ofReal_add hnon, hG, mul_add]
      exact mul_nonneg (by positivity) (integral_nonneg (fun z =>
        add_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem complex_disc_Hhalf_ne_top {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    boundaryDSq (fun θ (_ : Unit) => u (circlePoint θ)) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (complex_disc_Hhalf_bound hu)

end Yau.Blueprint.V02Proof
