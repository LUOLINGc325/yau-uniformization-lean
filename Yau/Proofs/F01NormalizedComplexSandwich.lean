import Yau.Proofs.F01NormalizedComplexFlowMatrix
import Yau.Proofs.F01PotentialSpatialLinearization
import Yau.Proofs.F01DilatedBackgroundGeometry
import Yau.Proofs.F01ChartMetricOrder

/-! The genuine native metric comparison gives a complex Euclidean
sandwich for the very matrix used in the differentiated scalar equation.
Its single constant precedes all flows, centers and scales. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalized_native_complex_sandwich
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {C : ℝ} (hC : 1 ≤ C) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T ρ : ℝ),
      0 < ρ → ρ ≤ A.radius → ρ ^ 2 ≤ T →
      SmoothSpaceTime U (Icc 0 T) → h 0 = g →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) →
      ∀ (a : M.Carrier) (p : Point n), p ∈ cylinder (ball 0 1) (-1) 1 →
        let H := chartPotentialMatrix (normalizedComplexBackground A a ρ)
          (forwardZeroSpaceTime (parabolicRescalePotential ρ
            (fun q : Point n => U (A.chart a q.1) q.2))) p
        (H - ((D⁻¹ : ℝ) : ℂ) • 1).PosSemidef ∧
          ((D : ℂ) • 1 - H).PosSemidef := by
  obtain ⟨D, hD, hChart⟩ := dilated_background_uniform_sandwich A
  have hCp : 0 < C := zero_lt_one.trans_le hC
  refine ⟨C * D, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)]
  · intro h U T ρ hρ hρr hρT hU hh0 hpot hflow a p hp
    dsimp only
    have he : chartPotentialMatrix (normalizedComplexBackground A a ρ)
        (forwardZeroSpaceTime (parabolicRescalePotential ρ
          (fun q : Point n => U (A.chart a q.1) q.2))) p =
        pullbackMatrix (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • p.1) :=
      normalized_complex_flow_matrix hg A h U hρ hρr hρT hU hh0 hpot a hp
    rw [he]
    have ht : ρ ^ 2 * max p.2 0 ∈ Icc 0 T :=
      ⟨mul_nonneg (sq_nonneg _) (le_max_right _ _),
        (mul_le_of_le_one_right (sq_nonneg ρ) (max_le hp.2.2 zero_le_one)).trans hρT⟩
    have hn := hflow (A.chart a (ρ • p.1)) _ ht
    have hh := relative_scalar_matrix_sandwich
      (H := pullbackMatrix g (A.chart a) (ρ • p.1))
      (K := pullbackMatrix (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • p.1))
      (inv_nonneg.mpr hCp.le) hCp.le
      (hChart ρ hρ hρr a p.1 hp.1).1 (hChart ρ hρ hρr a p.1 hp.1).2
      (metric_lower_order_in_chart g (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • p.1) hn.1)
      (metric_upper_order_in_chart g (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • p.1) hn.2)
    have hi : C⁻¹ * D⁻¹ = (C * D)⁻¹ := by rw [mul_inv_rev]; ring
    rw [hi] at hh
    exact hh

end Yau.NodeProofs.F01Aux
