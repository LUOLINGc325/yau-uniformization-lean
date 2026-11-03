import Yau.Proofs.F04AdjointGlobal
import Yau.LeafProofs.L18

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- Exact chart transport of the actual Hermitian Laplacian against a
 genuine compact chart test, with the original fixed volume density. -/
theorem chartPushforward_laplacian_integral
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (H : HermitianField M) (hH : MetricSmooth H) (c : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget c)
    {f : M.Carrier → ℝ} (hf : SmoothFn f)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηO : tsupport η ⊆ O) :
    (∫ y, chartPushforwardZero c η y * laplacian H f y ∂μ) =
      ∫ z in O, Real.sqrt (realMetricFn g.form c z).det * η z * laplacian H f (chartInv c z) := by
  let ψ := chartPushforwardZero c η
  have hψM : AEStronglyMeasurable ψ μ :=
    (continuous_of_smoothFn (smoothFn_chartPushforwardZero c hη hcη (hηO.trans hOt))).aestronglyMeasurable
  have hLM : AEStronglyMeasurable (laplacian H f) μ :=
    (continuous_of_smoothFn (Adjoint.smoothFn_laplacian H hH hf)).aestronglyMeasurable
  have hsource : (∫ y, ψ y * laplacian H f y ∂μ) =
      ∫ y in (extChartAt (ComplexModel n) c).source, ψ y * laplacian H f y ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    simp only [ψ, chartPushforwardZero, ite_eq_right hy, zero_mul]
  have ht := integral_chart_volume_ae g μ hμ c (hψM.mul hLM).restrict
  rw [Yau.LeafProofs.lebesgueC_eq_volume] at ht
  simp only [Pi.mul_apply, smul_eq_mul] at ht
  have hlocal : (∫ z in chartTarget c, Real.sqrt (realMetricFn g.form c z).det *
      (ψ (chartInv c z) * laplacian H f (chartInv c z))) =
      ∫ z in O, Real.sqrt (realMetricFn g.form c z).det *
        (η z * laplacian H f (chartInv c z)) := by
    calc
      _ = ∫ z in chartTarget c, Real.sqrt (realMetricFn g.form c z).det *
          (η z * laplacian H f (chartInv c z)) := by
        apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) c).measurableSet
        intro z hz
        change Real.sqrt (realMetricFn g.form c z).det *
          (chartPushforwardZero c η (chartInv c z) * laplacian H f (chartInv c z)) = _
        rw [chartPushforwardZero_chartInv c η hz]
      _ = _ := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (isOpen_extChartAt_target (I := ComplexModel n) c).measurableSet hOt
        intro z hz
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hz.2 (hηO hh)), zero_mul, mul_zero]
  change (∫ y, ψ y * laplacian H f y ∂μ) = _
  rw [hsource, ht, hlocal]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by ring)

end Yau.F04Proof
