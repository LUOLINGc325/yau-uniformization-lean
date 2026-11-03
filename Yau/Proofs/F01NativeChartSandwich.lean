import Yau.Proofs.F01DilatedBackgroundGeometry
import Yau.Proofs.F01ChartMetricOrder
import Yau.Proofs.F01RelativeScalarSandwich

/-! Actual metric comparison gives one Euclidean chart sandwich
before the compared field, center and spatial scale. Time slices can
therefore use the same constant throughout a fixed comparison horizon. -/
noncomputable section
open Set Metric
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem dilated_native_metric_sandwich (A : BoundedChartFamily g) {C : ℝ} (hC : 1 ≤ C) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (k : HermitianField M) (ρ : ℝ), 0 < ρ → ρ ≤ A.radius →
      (∀ x, (gMat k x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat k x).PosSemidef) →
      ∀ (a : M.Carrier) (z : Space n), z ∈ ball 0 1 →
        (pullbackMatrix k (A.chart a) (ρ • z) - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
        ((D : ℂ) • 1 - pullbackMatrix k (A.chart a) (ρ • z)).PosSemidef := by
  obtain ⟨D, hD, hChart⟩ := dilated_background_uniform_sandwich A
  have hCp : 0 < C := zero_lt_one.trans_le hC
  refine ⟨C * D, by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)], ?_⟩
  intro k ρ hρ hρr hRelative a z hz
  have hh := relative_scalar_matrix_sandwich
    (H := pullbackMatrix g (A.chart a) (ρ • z)) (K := pullbackMatrix k (A.chart a) (ρ • z))
    (inv_nonneg.mpr hCp.le) hCp.le (hChart ρ hρ hρr a z hz).1 (hChart ρ hρ hρr a z hz).2
    (metric_lower_order_in_chart g k (A.chart a) (ρ • z) (hRelative (A.chart a (ρ • z))).1)
    (metric_upper_order_in_chart g k (A.chart a) (ρ • z) (hRelative (A.chart a (ρ • z))).2)
  have hi : C⁻¹ * D⁻¹ = (C * D)⁻¹ := by rw [mul_inv_rev]; ring
  rw [hi] at hh
  exact hh

end Yau.NodeProofs.F01Aux
