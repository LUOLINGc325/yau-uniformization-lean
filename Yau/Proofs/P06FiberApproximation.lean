import Yau.Proofs.P06FiberApproximationMeasurable
import Yau.Proofs.P06FiberApproximationBounds

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.NodeProofs.P06Aux.FiberApprox
open Yau Yau.LeafProofs Clip P06ClipBernstein
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

/-- One explicit sequence simultaneously has the correct support, regularity,
sharp derivative bound, and the strong global L² limit. -/
theorem exists_zeroFixedBernstein_approximation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (h11 : RealOneOne A)
    (F : ℝ → ℝ) (hF : LipschitzWith 1 F) (h0 : F 0 = 0) :
    ∃ R : ℝ, 0 < R ∧
      (∀ x i, (whiteHermitian g.form A h11 x).eigenvalues i ∈ Icc (-R) R) ∧
      L2RealForm g.form μ (functionalForm g.form A F) ∧
      (∀ j, (zeroFixedBernstein R F j).eval 0 = 0 ∧
        (∀ x ∈ Icc (-R) R, |(zeroFixedBernstein R F j).derivative.eval x| ≤ 1) ∧
        SmoothRealForm (FiberPoly.polynomialForm g.form A h11 (zeroFixedBernstein R F j)) ∧
        CompactlySupportedRealForm (FiberPoly.polynomialForm g.form A h11 (zeroFixedBernstein R F j)) ∧
        L2RealForm g.form μ (FiberPoly.polynomialForm g.form A h11 (zeroFixedBernstein R F j))) ∧
      Tendsto (fun j => formL2DistanceSq g.form μ
        (FiberPoly.polynomialForm g.form A h11 (zeroFixedBernstein R F j))
        (functionalForm g.form A F)) atTop (𝓝 0) := by
  obtain ⟨R, hR, hs⟩ := exists_global_spectral_bound g A hA hcA h11
  have ht := zeroFixedBernstein_uniform hR hF h0
  refine ⟨R, hR, hs, functionalForm_l2 g μ hμ A hA hcA h11 _ F hF h0 hs ht, ?_, ?_⟩
  · intro j
    have hp := zeroFixedBernstein_zero R F j
    exact ⟨hp, fun _ hx => zeroFixedBernstein_derivative_bound hR hF j hx,
      FiberPoly.polynomialForm_smooth g A hA h11 _,
      FiberPoly.polynomialForm_compactlySupported g.form A h11 _ hp hcA,
      FiberPoly.polynomialForm_l2 g μ hμ A hA h11 _ hp hcA⟩
  · exact polynomialForm_l2_distance_tendsto g μ hμ A hA hcA h11 _ F hF h0 hR.le hs
      (zeroFixedBernstein_zero R F)
      (fun j _ hx => zeroFixedBernstein_derivative_bound hR hF j hx) ht

theorem functionalForm_interval (g : HermitianField M) (A : RealForm M 2) (C : ℝ) :
    functionalForm g A (intervalClip C) = intervalForm g C A := rfl

theorem functionalForm_positive (g : HermitianField M) (A : RealForm M 2) :
    functionalForm g A (fun r => max 0 r) = positiveForm g A := by
  unfold functionalForm positiveForm relativePositivePart matrixPositivePart
  congr 1
  funext x
  congr 1
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  congr 1
  funext r
  simp only [_root_.posPart_def, max_comm]

/-- The genuine interval clip belongs to the frozen raw L² space. -/
theorem intervalForm_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (h11 : RealOneOne A)
    {C : ℝ} (hC : 0 ≤ C) : L2RealForm g.form μ (intervalForm g.form C A) := by
  obtain ⟨R, hR, hs⟩ := exists_global_spectral_bound g A hA hcA h11
  exact functionalForm_l2 g μ hμ A hA hcA h11 (zeroFixedBernstein R (intervalClip C))
    (intervalClip C) (intervalClip_lipschitz C) (intervalClip_zero hC) hs
    (zeroFixedBernstein_uniform hR (intervalClip_lipschitz C) (intervalClip_zero hC))

/-- The genuine positive part belongs to the frozen raw L² space. -/
theorem positiveForm_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (h11 : RealOneOne A) :
    L2RealForm g.form μ (positiveForm g.form A) := by
  have hF : LipschitzWith 1 (fun r : ℝ => max 0 r) := LipschitzWith.id.const_max 0
  obtain ⟨R, hR, hs⟩ := exists_global_spectral_bound g A hA hcA h11
  rw [← functionalForm_positive]
  exact functionalForm_l2 g μ hμ A hA hcA h11 (zeroFixedBernstein R (fun r => max 0 r))
    (fun r => max 0 r) hF (by simp) hs (zeroFixedBernstein_uniform hR hF (by simp))

/-- The original interval clip preserves every genuine raw L² real (1,1) form. -/
theorem intervalForm_l2_of_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    {C : ℝ} (hC : 0 ≤ C) : L2RealForm g.form μ (intervalForm g.form C A) :=
  functionalForm_l2_of_l2 g μ A hA h11 (intervalClip C)
    (intervalClip_lipschitz C) (intervalClip_zero hC)

/-- The original positive-part projection preserves every genuine raw L² real (1,1) form. -/
theorem positiveForm_l2_of_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) :
    L2RealForm g.form μ (positiveForm g.form A) := by
  rw [← functionalForm_positive]
  exact functionalForm_l2_of_l2 g μ A hA h11 (fun r => max 0 r)
    (LipschitzWith.id.const_max 0) (by simp)

/-- Zero-fixed Bernstein polynomials converge strongly to the actual interval clip,
with no coefficient measurability hypothesis and with the same original C. -/
theorem intervalForm_approximation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (h11 : RealOneOne A)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ R : ℝ, 0 < R ∧
      (∀ x i, (whiteHermitian g.form A h11 x).eigenvalues i ∈ Icc (-R) R) ∧
      L2RealForm g.form μ (intervalForm g.form C A) ∧
      (∀ j, (zeroFixedBernstein R (intervalClip C) j).eval 0 = 0 ∧
        (∀ x ∈ Icc (-R) R, |(zeroFixedBernstein R (intervalClip C) j).derivative.eval x| ≤ 1) ∧
        SmoothRealForm (FiberPoly.polynomialForm g.form A h11 (zeroFixedBernstein R (intervalClip C) j)) ∧
        CompactlySupportedRealForm (FiberPoly.polynomialForm g.form A h11 (zeroFixedBernstein R (intervalClip C) j)) ∧
        L2RealForm g.form μ (FiberPoly.polynomialForm g.form A h11 (zeroFixedBernstein R (intervalClip C) j))) ∧
      Tendsto (fun j => formL2DistanceSq g.form μ
        (FiberPoly.polynomialForm g.form A h11 (zeroFixedBernstein R (intervalClip C) j))
        (intervalForm g.form C A)) atTop (𝓝 0) :=
  exists_zeroFixedBernstein_approximation g μ hμ A hA hcA h11
    (intervalClip C) (intervalClip_lipschitz C) (intervalClip_zero hC)

/-- The same explicit construction converges strongly to the actual positive part. -/
theorem positiveForm_approximation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (h11 : RealOneOne A) :
    ∃ R : ℝ, 0 < R ∧
      (∀ x i, (whiteHermitian g.form A h11 x).eigenvalues i ∈ Icc (-R) R) ∧
      L2RealForm g.form μ (positiveForm g.form A) ∧
      (∀ j, (zeroFixedBernstein R (fun r => max 0 r) j).eval 0 = 0 ∧
        (∀ x ∈ Icc (-R) R, |(zeroFixedBernstein R (fun r => max 0 r) j).derivative.eval x| ≤ 1) ∧
        SmoothRealForm (FiberPoly.polynomialForm g.form A h11 (zeroFixedBernstein R (fun r => max 0 r) j)) ∧
        CompactlySupportedRealForm (FiberPoly.polynomialForm g.form A h11 (zeroFixedBernstein R (fun r => max 0 r) j)) ∧
        L2RealForm g.form μ (FiberPoly.polynomialForm g.form A h11 (zeroFixedBernstein R (fun r => max 0 r) j))) ∧
      Tendsto (fun j => formL2DistanceSq g.form μ
        (FiberPoly.polynomialForm g.form A h11 (zeroFixedBernstein R (fun r => max 0 r) j))
        (positiveForm g.form A)) atTop (𝓝 0) := by
  rw [← functionalForm_positive]
  exact exists_zeroFixedBernstein_approximation g μ hμ A hA hcA h11
    (fun r => max 0 r) (LipschitzWith.id.const_max 0) (by simp)

end Yau.NodeProofs.P06Aux.FiberApprox
