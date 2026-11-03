import Yau.Proofs.V03CompactIntegralOperator
import Yau.Proofs.V03CompactParamSmoothness
import Yau.Proofs.V03ClosedLaplacian

/-! Smoothness and actual first and second parameter differentiation of
disc integrals follow from the genuine joint closed-disc density. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

abbrev ClosedDiscTraceDomain := Metric.closedBall (0 : ℂ) 1

def discInteriorTraceMeasure : Measure ClosedDiscTraceDomain :=
  (volume.restrict (Metric.ball (0 : ℂ) 1)).comap Subtype.val

instance : IsFiniteMeasure discInteriorTraceMeasure := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  exact inferInstanceAs (IsFiniteMeasure ((volume.restrict (Metric.ball (0 : ℂ) 1)).comap
    (Subtype.val : ClosedDiscTraceDomain → ℂ)))

def discTraceIntegralL : C(ClosedDiscTraceDomain, ℝ) →L[ℝ] ℝ := compactIntegralL discInteriorTraceMeasure

theorem discTraceIntegral_compactParamTrace {U : Set ℂ} {f : ℂ × ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ ClosedDiscTraceDomain)) {z : ℂ} (hz : z ∈ U) :
    discTraceIntegralL (compactParamTrace hf.continuousOn z) =
      ∫ ζ in Metric.ball (0 : ℂ) 1, f (z, ζ) := by
  change (∫ ζ : ClosedDiscTraceDomain, compactParamTrace hf.continuousOn z ζ
    ∂discInteriorTraceMeasure) = _
  calc
    _ = ∫ ζ : ClosedDiscTraceDomain, f (z, ζ) ∂discInteriorTraceMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ζ => compactParamTrace_apply hf.continuousOn hz ζ)
    _ = _ := by
      rw [discInteriorTraceMeasure, integral_subtype_comap
        (μ := volume.restrict (Metric.ball (0 : ℂ) 1)) (s := ClosedDiscTraceDomain)
        measurableSet_closedBall (fun ζ : ℂ => f (z, ζ)),
        Measure.restrict_restrict measurableSet_closedBall,
        Set.inter_eq_right.mpr Metric.ball_subset_closedBall]

theorem discIntegral_contDiffOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ ClosedDiscTraceDomain)) :
    ContDiffOn ℝ ∞ (fun z => ∫ ζ in Metric.ball (0 : ℂ) 1, f (z, ζ)) U := by
  have hT := compactParamTrace_contDiffOn hU uniqueDiffOn_real_closedDisc hf
  have hh : ContDiffOn ℝ ∞ (fun z => discTraceIntegralL (compactParamTrace hf.continuousOn z)) U :=
    discTraceIntegralL.contDiff.comp_contDiffOn hT
  exact hh.congr (fun z hz => (discTraceIntegral_compactParamTrace hf hz).symm)

def discParameterDerivative (f : ℂ × ℂ → ℝ) (U : Set ℂ) (v : ℂ) (p : ℂ × ℂ) : ℝ :=
  fderivWithin ℝ f (U ×ˢ ClosedDiscTraceDomain) p (v, 0)

theorem discParameterDerivative_contDiffOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ ClosedDiscTraceDomain)) (v : ℂ) :
    ContDiffOn ℝ ∞ (discParameterDerivative f U v) (U ×ˢ ClosedDiscTraceDomain) :=
  partialFDeriv_contDiffOn (hU.uniqueDiffOn.prod uniqueDiffOn_real_closedDisc) hf v

theorem discParameterDerivative_eq_slice {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ ClosedDiscTraceDomain)) {z : ℂ} (hz : z ∈ U)
    {ζ : ℂ} (hζ : ζ ∈ ClosedDiscTraceDomain) (v : ℂ) :
    discParameterDerivative f U v (z, ζ) = fderiv ℝ (fun p => f (p, ζ)) z v :=
  (fderiv_spatial_slice hU hz hζ ((hf.differentiableOn (by simp)) _ ⟨hz, hζ⟩) v).symm

theorem fderiv_compactDiscTrace {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ ClosedDiscTraceDomain)) {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ (compactParamTrace hf.continuousOn) z v =
      compactParamTrace (discParameterDerivative_contDiffOn hU hf v).continuousOn z := by
  have hT : DifferentiableAt ℝ (compactParamTrace hf.continuousOn) z :=
    ((compactParamTrace_contDiffOn hU uniqueDiffOn_real_closedDisc hf).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  ext ζ
  rw [fderiv_real_continuousMap_eval hT v ζ,
    (compactParamTrace_pointwise_hasFDerivAt hU hf hz ζ).fderiv,
    compactParamTrace_apply _ hz ζ]
  rfl

theorem fderiv_discIntegral {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ ClosedDiscTraceDomain)) {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ (fun p => ∫ ζ in Metric.ball (0 : ℂ) 1, f (p, ζ)) z v =
      ∫ ζ in Metric.ball (0 : ℂ) 1, discParameterDerivative f U v (z, ζ) := by
  have hT : DifferentiableAt ℝ (compactParamTrace hf.continuousOn) z :=
    ((compactParamTrace_contDiffOn hU uniqueDiffOn_real_closedDisc hf).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have heq : (fun p => ∫ ζ in Metric.ball (0 : ℂ) 1, f (p, ζ)) =ᶠ[𝓝 z]
      (fun p => discTraceIntegralL (compactParamTrace hf.continuousOn p)) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact (discTraceIntegral_compactParamTrace hf hp).symm
  rw [heq.fderiv_eq, fderiv_comp_realCLM discTraceIntegralL hT v,
    fderiv_compactDiscTrace hU hf hz v]
  exact discTraceIntegral_compactParamTrace (discParameterDerivative_contDiffOn hU hf v) hz

theorem secondFDeriv_discIntegral {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ ClosedDiscTraceDomain)) {z : ℂ} (hz : z ∈ U) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ (fun p => ∫ ζ in Metric.ball (0 : ℂ) 1, f (p, ζ))) z w v =
      ∫ ζ in Metric.ball (0 : ℂ) 1,
        discParameterDerivative (discParameterDerivative f U v) U w (z, ζ) := by
  have hI : ContDiffAt ℝ ∞ (fun p => ∫ ζ in Metric.ball (0 : ℂ) 1, f (p, ζ)) z :=
    (discIntegral_contDiffOn hU hf).contDiffAt (hU.mem_nhds hz)
  rw [fderiv_real_clm_apply ((hI.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero) w v]
  have heq : (fun p => fderiv ℝ (fun p' => ∫ ζ in Metric.ball (0 : ℂ) 1, f (p', ζ)) p v) =ᶠ[𝓝 z]
      (fun p => ∫ ζ in Metric.ball (0 : ℂ) 1, discParameterDerivative f U v (p, ζ)) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact fderiv_discIntegral hU hf hp v
  rw [heq.fderiv_eq]
  exact fderiv_discIntegral hU (discParameterDerivative_contDiffOn hU hf v) hz w

theorem mixedReal_discIntegral {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ ClosedDiscTraceDomain)) (h0 : (0 : ℂ) ∈ U) :
    mixedReal (fun p => ∫ ζ in Metric.ball (0 : ℂ) 1, f (p, ζ)) =
      (1 / 4 : ℝ) * ((∫ ζ in Metric.ball (0 : ℂ) 1,
        discParameterDerivative (discParameterDerivative f U 1) U 1 (0, ζ)) +
        ∫ ζ in Metric.ball (0 : ℂ) 1,
          discParameterDerivative (discParameterDerivative f U Complex.I) U Complex.I (0, ζ)) := by
  have hI : ContDiffAt ℝ 2 (fun p => ∫ ζ in Metric.ball (0 : ℂ) 1, f (p, ζ)) 0 :=
    ((discIntegral_contDiffOn hU hf).contDiffAt (hU.mem_nhds h0)).of_le (by simp)
  rw [mixedReal, mixedWirt_real_diagonal hI]
  simp only [smul_eq_mul, mul_one, secondFDeriv_discIntegral hU hf h0]

end Yau.Blueprint.V03Proof
