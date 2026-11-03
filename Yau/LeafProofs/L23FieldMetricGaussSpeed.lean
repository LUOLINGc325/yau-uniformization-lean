import Yau.LeafProofs.L23FieldMetricGaussEndpoint
import Yau.LeafProofs.L23FieldMetricNormalRadius

/-! Gauss's identity gives the pointwise physical length bound. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem chartGeodesicFamily_gauss_speed_bound
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (B : Set (ComplexVector n)) (hB : IsOpen B) {ρ ε : ℝ} (hε : 0 < ε)
    (η : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
    (hη : ContDiffOn ℝ 2 (Function.uncurry η)
      ((B ×ˢ Metric.ball (0 : ComplexVector n) ρ) ×ˢ Set.Ioo (-ε) (1+ε)))
    (hi : ∀ p ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ, η p 0 = p)
    (hs : ∀ p ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ,
      ∀ u ∈ Set.Ioo (-ε) (1+ε), (η p u).1 ∈ chartTarget c ∧
        HasDerivAt (η p) (chartGeodesicSpray h c (η p u)) u)
    {z v : ComplexVector n} (hz : z ∈ B) (hv : v ∈ Metric.ball (0 : ComplexVector n) ρ)
    (w : ComplexVector n) :
    |realMetricInChart h c z v w| ≤ chartVectorNorm h c z v*
      chartVectorNorm h c (η (z,v) 1).1 (fderiv ℝ (fun b => (η (z,b) 1).1) v w) := by
  have h₀ : (0 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have h₁ : (1 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have hp : (z,v) ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ := ⟨hz,hv⟩
  have HE := chartGeodesicEnergy_constant h hh c (η (z,v)) (hs (z,v) hp) h₁ h₀
  have Hinitial : η (z,v) 0 = (z,v) := hi (z,v) hp
  have Hnorm : chartVectorNorm h c (η (z,v) 1).1 (η (z,v) 1).2 = chartVectorNorm h c z v := by
    change Real.sqrt (chartGeodesicEnergy h c (η (z,v) 1)) = Real.sqrt (realMetricInChart h c z v v)
    rw [HE,Hinitial]
    rfl
  calc
    |realMetricInChart h c z v w| = |realMetricInChart h c (η (z,v) 1).1 (η (z,v) 1).2
        (fderiv ℝ (fun b => (η (z,b) 1).1) v w)| :=
      congrArg abs (chartGeodesicFamily_gauss h hh c B hB hε η hη hi hs hz hv w).symm
    _ ≤ chartVectorNorm h c (η (z,v) 1).1 (η (z,v) 1).2 *
        chartVectorNorm h c (η (z,v) 1).1 (fderiv ℝ (fun b => (η (z,b) 1).1) v w) :=
      realMetricInChart_abs_le_chartVectorNorm h c (η (z,v) 1).1 (η (z,v) 1).2 _
    _ = _ := congrArg (fun s => s*chartVectorNorm h c (η (z,v) 1).1
      (fderiv ℝ (fun b => (η (z,b) 1).1) v w)) Hnorm

theorem chartGeodesicFamily_regularized_radius_bound
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (B : Set (ComplexVector n)) (hB : IsOpen B) {ρ ε d : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (η : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
    (hη : ContDiffOn ℝ 2 (Function.uncurry η)
      ((B ×ˢ Metric.ball (0 : ComplexVector n) ρ) ×ˢ Set.Ioo (-ε) (1+ε)))
    (hi : ∀ p ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ, η p 0 = p)
    (hs : ∀ p ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ,
      ∀ u ∈ Set.Ioo (-ε) (1+ε), (η p u).1 ∈ chartTarget c ∧
        HasDerivAt (η p) (chartGeodesicSpray h c (η p u)) u)
    {z v : ComplexVector n} (hz : z ∈ B) (hv : v ∈ Metric.ball (0 : ComplexVector n) ρ)
    (w : ComplexVector n) :
    |realMetricInChart h c z v w/regularizedChartRadius h c z d v| ≤
      chartVectorNorm h c (η (z,v) 1).1 (fderiv ℝ (fun b => (η (z,b) 1).1) v w) := by
  rw [abs_div,abs_of_pos (regularizedChartRadius_pos h c z hd v)]
  apply (div_le_iff₀ (regularizedChartRadius_pos h c z hd v)).mpr
  have H := chartGeodesicFamily_gauss_speed_bound h hh c B hB hε η hη hi hs hz hv w
  exact H.trans (by
    have Hnorm := chartVectorNorm_le_regularizedChartRadius h c z v d
    have Hnonneg : 0 ≤ chartVectorNorm h c (η (z,v) 1).1
        (fderiv ℝ (fun b => (η (z,b) 1).1) v w) := Real.sqrt_nonneg _
    nlinarith only [Hnorm,Hnonneg])

end Yau.LeafProofs.L23Aux
