import Yau.Proofs.F01NormalizedInitialFlowMatrix
import Yau.Proofs.F01DilatedBackgroundGeometry
import Yau.Proofs.F01ClampedTransformedRange

/-! One numerical transformed-matrix range is fixed before all actual
flow realizations, chart centers, and admissible parabolic scales. The only
flow comparison used is its genuine coarse native metric sandwich. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_normalized_transformed_range
    (α : HermitianField M) (hα : MetricSmooth α) (A : BoundedChartFamily α)
    {C : ℝ} (hC : 1 ≤ C) :
    ∃ ell upper : ℝ, 0 < ell ∧ ell ≤ upper ∧
      ∀ (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T ρ : ℝ),
      0 < ρ → ρ ≤ A.radius → ρ ^ 2 ≤ T →
      SmoothSpaceTime U (Icc 0 T) → h 0 = α →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef ∧
        ((C : ℂ) • gMat α x - gMat (h s) x).PosSemidef) →
      ∀ a : M.Carrier, ∀ p ∈ ball (0 : Space n) 1 ×ˢ Icc (-1) 1,
        (((clampedBackground (fun z => pullbackMatrix α (A.chart a) (ρ • z)) p +
            complexHessianMap (hessian (forwardZeroSpaceTime
              (parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2))) p) : Sym n) : Mat n) -
          ell • (1 : Mat n)).PosSemidef ∧
        (upper • (1 : Mat n) -
          ((clampedBackground (fun z => pullbackMatrix α (A.chart a) (ρ • z)) p +
            complexHessianMap (hessian (forwardZeroSpaceTime
              (parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2))) p) : Sym n) : Mat n)).PosSemidef := by
  obtain ⟨D, hD, hd⟩ := dilated_background_uniform_sandwich A
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hBpos : 0 < C * D := mul_pos hCpos hDpos
  have hB1 : 1 ≤ C * D := by nlinarith
  refine ⟨(C * D)⁻¹, C * D, inv_pos.mpr hBpos, ?_, ?_⟩
  · have hi : (C * D)⁻¹ ≤ (1 : ℝ) := by
      simpa only [inv_one] using (inv_le_inv₀ hBpos zero_lt_one).mpr hB1
    exact hi.trans hB1
  intro h U T ρ hρ hρr hρT hU hh0 hpot hflow a p hp
  have hz := spatialDilation_mem_ball hρ hρr hp.1
  have htime : ρ ^ 2 * max p.2 0 ∈ Icc 0 T :=
    ⟨mul_nonneg (sq_nonneg _) (le_max_right _ _),
      (mul_le_of_le_one_right (sq_nonneg ρ) (max_le hp.2.2 zero_le_one)).trans hρT⟩
  have hnative := hflow (A.chart a (ρ • p.1)) (ρ ^ 2 * max p.2 0) htime
  have hlocal := relative_scalar_matrix_sandwich (inv_nonneg.mpr hCpos.le) hCpos.le
    (hd ρ hρ hρr a p.1 hp.1).1 (hd ρ hρ hρr a p.1 hp.1).2
    (metric_lower_order_in_chart α (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • p.1) hnative.1)
    (metric_upper_order_in_chart α (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • p.1) hnative.2)
  have he : C⁻¹ * D⁻¹ = (C * D)⁻¹ := by rw [mul_inv_rev]; ring
  rw [he] at hlocal
  have hreal := iota_scalar_matrix_sandwich hlocal.1 hlocal.2
  rw [normalized_initial_transformed_flow_matrix α hα A h U hρ hρr hρT hU hh0 hpot a hp]
  exact hreal

end Yau.NodeProofs.F01Aux
