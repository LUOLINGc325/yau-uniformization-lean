import Yau.Proofs.V02AreaTaylorIntegral
import Yau.Proofs.V02WallTaylorDirichletJets

/-! The generic compact integral theorem, specialized to the original
normalized circle average and its actual parameter derivatives. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof V02AreaTaylorProof

def circleTraceMeasure : Measure BoundaryAngleInterval :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) •
    (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))).comap Subtype.val

instance : IsFiniteMeasure circleTraceMeasure := by
  letI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) :=
    isFiniteMeasure_restrict.mpr (by
      simpa only [Real.volume_Ioc, sub_zero] using (ENNReal.ofReal_ne_top : ENNReal.ofReal (2 * Real.pi) ≠ ⊤))
  exact ((volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))).comap
      (Subtype.val : BoundaryAngleInterval → ℝ)).smul_finite ENNReal.ofReal_ne_top

theorem circleTraceIntegral_eq (g : ℝ → ℝ) :
    (∫ θ : BoundaryAngleInterval, g θ ∂circleTraceMeasure) = circleAverage g := by
  rw [circleTraceMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi)⁻¹), smul_eq_mul]
  rw [integral_subtype_comap
    (μ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))
    (s := BoundaryAngleInterval) measurableSet_Icc g,
    Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_right.mpr Set.Ioc_subset_Icc_self]
  rw [circleAverage, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

theorem circleTraceIntegral_compactParamTrace {U : Set ℂ} {f : ℂ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ BoundaryAngleInterval)) {z : ℂ} (hz : z ∈ U) :
    compactIntegralL circleTraceMeasure (compactParamTrace hf.continuousOn z) =
      circleAverage (fun θ => f (z, θ)) := by
  change (∫ θ : BoundaryAngleInterval, compactParamTrace hf.continuousOn z θ ∂circleTraceMeasure) = _
  rw [← circleTraceIntegral_eq]
  exact integral_congr_ae (Eventually.of_forall (fun θ => compactParamTrace_apply hf.continuousOn hz θ))

theorem circleAverage_contDiffOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ BoundaryAngleInterval)) :
    ContDiffOn ℝ ∞ (fun z => circleAverage (fun θ => f (z, θ))) U := by
  have hh := compactParamIntegral_contDiffOn hU (uniqueDiffOn_Icc (by positivity : (0 : ℝ) < 2 * Real.pi))
    circleTraceMeasure hf
  exact hh.congr (fun z hz => (circleTraceIntegral_compactParamTrace hf hz).symm)

theorem iteratedFDeriv_circleAverage_apply {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ BoundaryAngleInterval)) {z : ℂ} (hz : z ∈ U)
    (k : ℕ) (v : Fin k → ℂ) :
    iteratedFDeriv ℝ k (fun p => circleAverage (fun θ => f (p, θ))) z v =
      circleAverage (fun θ => iteratedFDeriv ℝ k (fun p => f (p, θ)) z v) := by
  have he : (fun p => circleAverage (fun θ => f (p, θ))) =ᶠ[𝓝 z]
      (fun p => compactIntegralL circleTraceMeasure (compactParamTrace hf.continuousOn p)) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact (circleTraceIntegral_compactParamTrace hf hp).symm
  rw [(he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds,
    iteratedFDeriv_compactParamIntegral_apply hU
      (uniqueDiffOn_Icc (by positivity : (0 : ℝ) < 2 * Real.pi)) circleTraceMeasure hf hz k v]
  exact circleTraceIntegral_eq (fun θ => iteratedFDeriv ℝ k (fun p => f (p, θ)) z v)

theorem norm_iteratedFDeriv_circleAverage_le {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ BoundaryAngleInterval)) {z : ℂ} (hz : z ∈ U)
    (k : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ θ : BoundaryAngleInterval, ‖iteratedFDeriv ℝ k (fun p => f (p, θ)) z‖ ≤ M) :
    ‖iteratedFDeriv ℝ k (fun p => circleAverage (fun θ => f (p, θ))) z‖ ≤ M := by
  have he : (fun p => circleAverage (fun θ => f (p, θ))) =ᶠ[𝓝 z]
      (fun p => compactIntegralL circleTraceMeasure (compactParamTrace hf.continuousOn p)) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact (circleTraceIntegral_compactParamTrace hf hp).symm
  rw [(he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  have hh := norm_iteratedFDeriv_compactParamIntegral_le hU
    (uniqueDiffOn_Icc (by positivity : (0 : ℝ) < 2 * Real.pi)) circleTraceMeasure hf hz k
    (integrable_const M) (fun _ => hM) hb
  have hconst : (∫ θ : BoundaryAngleInterval, M ∂circleTraceMeasure) = M := by
    rw [circleTraceIntegral_eq (fun _ => M), circleAverage, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul]
  exact hh.trans_eq hconst

end Yau.Blueprint.V02WallTaylorProof
