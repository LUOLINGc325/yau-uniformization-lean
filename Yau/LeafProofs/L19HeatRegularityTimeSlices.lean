import Yau.LeafProofs.L19HeatRegularityChartTest
import Yau.LeafProofs.L19HeatFamilyDerivative

/-! The actual constructed heat family in the genuine chart energy maps. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- Every positive-time actual heat slice has the genuine completed chart
weak derivative, with no representative regularity premise. -/
theorem scalarHeat_chartWeakGradient (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ 1 η)
    (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O) (i : RIdx n) :
    (∫ z in O, scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
        (scalarHeatFamily g μ hμ t f) z * rDeriv η z i) =
      -(∫ z in O, scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i
        (scalarHeatEnergy g μ hμ t f) z * η z) := by
  rw [← scalarHeatEnergy_L2 g μ hμ ht f]
  exact scalarEnergy_chartWeakGradient g μ hμ x hO hOc hOt
    (scalarHeatEnergy g μ hμ t f) hη hcη hηO i

/-- The actual chart L² values vary continuously at every positive time. -/
theorem scalarHeat_chartValues_continuousAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ) :
    ContinuousAt (fun s => scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
      (scalarHeatFamily g μ hμ s f)) t :=
  (scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt).continuous.continuousAt.comp
    (scalarHeatFamily_apply_hasDerivAt g μ hμ ht f).continuousAt

/-- The actual chart derivatives vary continuously in their L² norm at
every positive time. -/
theorem scalarHeat_chartDerivatives_continuousAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ) (i : RIdx n) :
    ContinuousAt (fun s => scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i
      (scalarHeatEnergy g μ hμ s f)) t :=
  (scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i).continuous.continuousAt.comp
    (scalarHeatEnergy_continuousAt g μ hμ ht f)

/-- The actual heat variational equation, evaluated on a genuine chart
pushforward test, has the exact computed density and half inverse metric. -/
theorem scalarHeat_chart_test_equation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηO : tsupport η ⊆ O) :
    inner ℝ (deriv (fun s => scalarHeatFamily g μ hμ s f) t)
      (scalarEnergyL2 g μ hμ
        (scalarEnergy_chartTest g μ hμ x hη hcη (hηO.trans (subset_closure.trans hOt)) :
          ScalarEnergySpace g μ hμ)) +
      (∫ z in O, Real.sqrt (realMetricFn g.form x z).det *
        ∑ i, ∑ j, ((1 / 2 : ℝ) * (realMetricFn g.form x z)⁻¹ i j) *
          scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt j
            (scalarHeatEnergy g μ hμ t f) z * rDeriv η z i) = 0 := by
  rw [← scalarClosedEnergy_chartTest g μ hμ x hO hOc hOt
    (scalarHeatEnergy g μ hμ t f) hη hcη hηO]
  exact scalarHeatFamily_weak_equation g μ hμ ht f _

end Yau.LeafProofs.L19Aux
