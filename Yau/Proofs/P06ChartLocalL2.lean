import Yau.Proofs.P06ChartProjection
import Yau.Proofs.P06HodgeDavies

/-! Fixed compact chart projections are controlled by the physical local
Hilbert norm, uniformly over every actual L² form in every degree. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderChartL2
open Yau Yau.LeafProofs Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def restrictForm (F : Set M.Carrier) (A : RealForm M k) : RealForm M k :=
  multiplyRealForm (F.indicator (fun _ => (1 : ℝ))) A

theorem restrictForm_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (F : Set M.Carrier) (hF : MeasurableSet F)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    L2RealForm g.form μ (restrictForm F A) :=
  l2RealForm_multiply_bounded g μ _
    (stronglyMeasurable_const.indicator hF).aestronglyMeasurable 1 zero_le_one
    (fun y => by by_cases hy : y ∈ F <;> simp [hy]) A hA

/-- Physical restriction and the genuine Hilbert indicator are identical. -/
theorem realize_restrictForm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (F : Set M.Carrier) (hF : MeasurableSet F)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    realizeActualForm g μ (restrictForm F A) (restrictForm_l2 g μ F hF A hA) =
      Davies.indicator g μ F hF (realizeActualForm g μ A hA) := by
  simp only [Davies.indicator, realizeActualForm, multiplyL2FormHilbert_realize] <;> rfl

theorem chartFunctional_restrictForm (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (F : Set M.Carrier) (hcover : ∀ z ∈ tsupport φ, chartInv x z ∈ F)
    (A : RealForm M k) :
    chartFunctional x φ L (restrictForm F A) = chartFunctional x φ L A := by
  funext z
  by_cases hz : z ∈ tsupport φ
  · simp only [chartFunctional, restrictForm, chartForm_multiply,
      Set.indicator_of_mem (hcover z hz), one_smul]
  · simp only [chartFunctional, image_eq_zero_of_notMem_tsupport hz, zero_mul]

/-- Localize the input of the existing chart integral estimate before
applying it.  The constant precedes the actual datum and its L² proof. -/
theorem chartFunctional_integral_bound_on_physical_set
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (F : Set M.Carrier) (hF : MeasurableSet F)
    (hcover : ∀ z ∈ tsupport φ, chartInv x z ∈ F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : RealForm M k) (hA : L2RealForm g.form μ A),
      (∫ z, (chartFunctional x φ L A z) ^ 2 ∂lebesgueC n) ≤
        C * ‖Davies.indicator g μ F hF (realizeActualForm g μ A hA)‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := chartFunctional_integral_bound g μ hμ x φ hφ hcφ hφO L
  refine ⟨C, hC, fun A hA => ?_⟩
  have hh := hb (restrictForm F A) (restrictForm_l2 g μ F hF A hA)
  rwa [chartFunctional_restrictForm x φ L F hcover A,
    realize_restrictForm g μ F hF A hA] at hh

def physicalSupport (x : M.Carrier) (φ : ComplexVector n → ℝ) : Set M.Carrier :=
  chartInv x '' tsupport φ

theorem physicalSupport_isCompact (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x) :
    IsCompact (physicalSupport x φ) :=
  hcφ.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) x).mono hφO)

theorem physicalSupport_measurable (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x) :
    MeasurableSet (physicalSupport x φ) :=
  (physicalSupport_isCompact x φ hcφ hφO).isClosed.measurableSet

/-- LP for the exact compact physical support of the fixed chart cutoff. -/
theorem chartFunctional_integral_local_bound
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : RealForm M k) (hA : L2RealForm g.form μ A),
      (∫ z, (chartFunctional x φ L A z) ^ 2 ∂lebesgueC n) ≤
        C * ‖Davies.indicator g μ (physicalSupport x φ)
          (physicalSupport_measurable x φ hcφ hφO) (realizeActualForm g μ A hA)‖ ^ 2 :=
  chartFunctional_integral_bound_on_physical_set g μ hμ x φ hφ hcφ hφO L
    (physicalSupport x φ) (physicalSupport_measurable x φ hcφ hφO)
    (fun _ hz => Set.mem_image_of_mem _ hz)

/-- On a measurable cutoff plateau, the uncut chart coefficient has the
same localized bound.  No smoothness of the actual input is assumed. -/
theorem chartCoefficient_integral_local_bound
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (O : Set (ComplexVector n)) (hO : MeasurableSet O)
    (hone : ∀ z ∈ O, φ z = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : RealForm M k) (hA : L2RealForm g.form μ A),
      (∫ z in O, (L (chartForm A x z)) ^ 2 ∂lebesgueC n) ≤
        C * ‖Davies.indicator g μ (physicalSupport x φ)
          (physicalSupport_measurable x φ hcφ hφO) (realizeActualForm g μ A hA)‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := chartFunctional_integral_local_bound g μ hμ x φ hφ hcφ hφO L
  refine ⟨C, hC, fun A hA => ?_⟩
  have hi := (memLp_two_iff_integrable_sq
    (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L A hA).aestronglyMeasurable).mp
      (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L A hA)
  calc
    _ = ∫ z in O, (chartFunctional x φ L A z) ^ 2 ∂lebesgueC n :=
      setIntegral_congr_fun hO (fun z hz => by simp only [chartFunctional, hone z hz, one_mul])
    _ ≤ ∫ z, (chartFunctional x φ L A z) ^ 2 ∂lebesgueC n :=
      setIntegral_le_integral hi (Eventually.of_forall (fun z => sq_nonneg _))
    _ ≤ _ := hb A hA

theorem chartFunctional_integral_volume_local_bound
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : RealForm M k) (hA : L2RealForm g.form μ A),
      (∫ z, (chartFunctional x φ L A z) ^ 2) ≤
        C * ‖Davies.indicator g μ (physicalSupport x φ)
          (physicalSupport_measurable x φ hcφ hφO) (realizeActualForm g μ A hA)‖ ^ 2 := by
  simpa only [lebesgueC_eq_volume] using
    chartFunctional_integral_local_bound g μ hμ x φ hφ hcφ hφO L

theorem chartCoefficient_integral_volume_local_bound
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (O : Set (ComplexVector n)) (hO : MeasurableSet O)
    (hone : ∀ z ∈ O, φ z = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : RealForm M k) (hA : L2RealForm g.form μ A),
      (∫ z in O, (L (chartForm A x z)) ^ 2) ≤
        C * ‖Davies.indicator g μ (physicalSupport x φ)
          (physicalSupport_measurable x φ hcφ hφO) (realizeActualForm g μ A hA)‖ ^ 2 := by
  simpa only [lebesgueC_eq_volume] using
    chartCoefficient_integral_local_bound g μ hμ x φ hφ hcφ hφO L O hO hone

end Yau.NodeProofs.P06Aux.CylinderChartL2
