import Yau.Proofs.P06Weitzenbock

noncomputable section
open Filter MeasureTheory
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L23Aux L03
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

/-- The original 1/2! form metric contracted with both derivative directions. -/
def chartGradientPair (h : HermitianField M) (A B : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b *
    tensorCoefficientPairing (realMetricFn h c z)⁻¹
      (fun I => covariantComponents h c (formComponents B c) z a I)
      (fun I => covariantComponents h c (formComponents A c) z b I)

def chartRoughPair (h : HermitianField M) (A B : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) : ℝ :=
  (1 / 2 : ℝ) * tensorCoefficientPairing (realMetricFn h c z)⁻¹
    (formComponents B c z) (roughTwoComponents h A c z)

def chartCurvaturePair (h : HermitianField M) (A B : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) : ℝ :=
  (1 / 2 : ℝ) * tensorCoefficientPairing (realMetricFn h c z)⁻¹
    (formComponents B c z) (curvatureTwoComponents h A c z)

theorem roughTwo_eq_codifferential_covariant (h : HermitianField M) (A : RealForm M 2)
    (c : M.Carrier) (z : ComplexVector n) :
    roughTwoComponents h A c z =
      codifferentialComponents h c (covariantD h c (formComponents A c)) z := by
  funext I
  simp only [roughTwoComponents, codifferentialComponents, covariantD,
    covariantComponents, Fin.cons_zero, Fin.cons_succ]

theorem tensorGreen_raised_covariant (g : SmoothMetric M) (A B : RealForm M 2)
    (hA : SmoothRealForm A) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    (1 / 2 : ℝ) * (∑ a, tensorCovariantGreenTerm g.form c (formComponents B c)
      (raisedFirstComponents g.form c (covariantD g.form c (formComponents A c))) a z) =
      chartGradientPair g.form A B c z - chartRoughPair g.form A B c z := by
  have hU := covariantD_contDiffOn g.form (L12Aux.metricSmooth_of_smoothMetric g)
    c (formComponents A c) (hA c)
  rw [tensorCovariantGreenTerm_raisedFirst g c (formComponents B c) _ hU hz,
    ← roughTwo_eq_codifferential_covariant]
  simp only [covariantD_form_cons, chartGradientPair, chartRoughPair]
  ring

theorem hodgePair_eq_rough_add_curvature (h : HermitianField M) (hs : MetricSmooth h)
    (A B : RealForm M 2) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    formInner h B (hodgeRealForm h 2 A) (chartInv c z) =
      chartRoughPair h A B c z + chartCurvaturePair h A B c z := by
  rw [formInner_chartInv_eq_tensorPairing h B (hodgeRealForm h 2 A) c hz]
  have hh : formComponents (hodgeRealForm h 2 A) c z =
      fun I => roughTwoComponents h A c z I + curvatureTwoComponents h A c z I := by
    funext I
    rw [hodge_represents h hs A hA c z hz I,
      hodgeTwo_eq_rough_add_curvature h hs A hA c hz]
  rw [hh, tensorCoefficientPairing_add_right]
  simp only [chartRoughPair, chartCurvaturePair]
  norm_num
  ring

/-- Local bilinear Green formula with the actual volume density and every
boundary term retained. Neither input is assumed closed or of type (1,1). -/
theorem integral_chart_rough_green (g : SmoothMetric M) (A B : RealForm M 2)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (c : M.Carrier)
    {φ : ComplexVector n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget c) :
    (∫ z, φ z * Real.sqrt (realMetricFn g.form c z).det *
      (chartGradientPair g.form A B c z - chartRoughPair g.form A B c z) ∂lebesgueC n) =
      -(1 / 2 : ℝ) * (∫ z, ∑ a, rDeriv φ z a *
        tensorMetricFlux g.form c (formComponents B c)
          (raisedFirstComponents g.form c (covariantD g.form c (formComponents A c))) a z
        ∂lebesgueC n) := by
  let U := covariantD g.form c (formComponents A c)
  let V := raisedFirstComponents g.form c U
  have hU := covariantD_contDiffOn g.form (L12Aux.metricSmooth_of_smoothMetric g)
    c (formComponents A c) (hA c)
  have hV (a : RIdx n) (I : Fin 2 → RIdx n) :
      ContDiffOn ℝ ∞ (fun w => V a w I) (chartTarget c) :=
    raisedFirstComponents_contDiffOn g c U hU a I
  have he := integral_tensor_covariant_derivative g c (formComponents B c) V
    (hB c) hV hφ hcφ hφO
  calc
    _ = (1 / 2 : ℝ) * (∫ z, φ z * Real.sqrt (realMetricFn g.form c z).det *
        (∑ a, tensorCovariantGreenTerm g.form c (formComponents B c) V a z)
        ∂lebesgueC n) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ chartTarget c
      · have hp := tensorGreen_raised_covariant g A B hA c hz
        change (1 / 2 : ℝ) * (∑ a, tensorCovariantGreenTerm g.form c
          (formComponents B c) V a z) = _ at hp
        rw [← hp]
        ring
      · have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hz (hφO hh))
        simp only [hzero, zero_mul, mul_zero]
    _ = _ := by rw [he]; ring

end Yau.NodeProofs.P06Weitzenbock
