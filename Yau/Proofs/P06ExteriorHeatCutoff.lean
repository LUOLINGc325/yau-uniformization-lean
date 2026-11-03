import Yau.Proofs.P06ExteriorHeatLocalGreen
import Yau.Proofs.P06MetricCutoffs
import Yau.Proofs.G04ClosedHodge
import Yau.LeafProofs.L03DiracCutoffSymbols

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ContDiff

namespace Yau.NodeProofs.P06Aux.ExteriorHeat
open Yau Yau.Blueprint Yau.LeafProofs L03
variable {n k : ℕ} {M : ComplexManifold n}

theorem closed_cutoff_exterior_eq (η : M.Carrier → ℝ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hclosed : ClosedRealForm A) :
    exteriorRealForm (multiplyRealForm η A) = exteriorCutoffError η A := by
  rw [exteriorCutoffError,G04Aux.exterior_closed_eq_zero A hA hclosed]
  have hz : multiplyRealForm η (0 : RealForm M (k+1)) = 0 := by
    funext y
    exact smul_zero (η y)
  rw [hz,sub_zero]

/-- The error is zero inside the growing inner ball by first-order locality. -/
theorem cutoff_exterior_zero_inside (g : SmoothMetric M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (hclosed : ClosedRealForm A)
    (j : ℕ) (hj : 1 ≤ j) (y : M.Carrier) (hy : y ∈ distBall g.form o j) :
    exteriorRealForm (multiplyRealForm (χ j) A) y = 0 := by
  obtain ⟨c,hc,hcut⟩ := hχ
  have hh := hcut j hj
  have he : exteriorRealForm (multiplyRealForm (χ j) A) y = exteriorRealForm A y := by
    apply exteriorRealForm_eq_at_of_eventuallyEq (smoothRealForm_multiply _ _ hh.1 hA) hA y
    filter_upwards [(L12Aux.isOpen_distBall g o j).mem_nhds hy] with z hz
    change χ j z • A z = A z
    rw [hh.2.2.2.1 z hz,one_smul]
  rw [he,G04Aux.exterior_closed_eq_zero A hA hclosed]
  rfl

/-- The actual compact derivative is supported in the outer cutoff ball. -/
theorem cutoff_exterior_support (g : SmoothMetric M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    (A : RealForm M k) (hA : SmoothRealForm A) (j : ℕ) (hj : 1 ≤ j) :
    closure {y | exteriorRealForm (multiplyRealForm (χ j) A) y ≠ 0} ⊆
      distBall g.form o (2*j) := by
  obtain ⟨c,hc,hcut⟩ := hχ
  have hh := hcut j hj
  exact (representsExterior_support_subset
    (exteriorRealForm_represents _ (smoothRealForm_multiply _ _ hh.1 hA))).trans
    ((multiplyRealForm_support_subset_scalar (χ j) A).trans hh.2.2.2.2.1)

/-- Literal gradient control gives the cutoff source bound without L² A. -/
theorem cutoff_exterior_point_bound (g : SmoothMetric M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (c : ℝ)
    (hcut : ∀ j : ℕ, 1 ≤ j → SmoothFn (χ j) ∧ HasCompactSupport (χ j) ∧
      (∀ x, 0 ≤ χ j x ∧ χ j x ≤ 1) ∧
      (∀ x ∈ distBall g.form o j, χ j x = 1) ∧
      tsupport (χ j) ⊆ distBall g.form o (2*j) ∧
      ∀ x, realGradientNormSq g.form (χ j) x ≤ (c/j)^2)
    (A : RealForm M k) (hA : SmoothRealForm A) (hclosed : ClosedRealForm A)
    (B0 : ℝ) (hb : ∀ x, formNormSq g.form A x ≤ B0^2)
    (j : ℕ) (hj : 1 ≤ j) (y : M.Carrier) :
    formNormSq g.form (exteriorRealForm (multiplyRealForm (χ j) A)) y ≤ (c/j)^2 * B0^2 := by
  rw [closed_cutoff_exterior_eq (χ j) A hA hclosed]
  have he := exteriorCutoffError_normSq_le g.form (χ j) (hcut j hj).1 A hA y
  have hg : L18Aux.scalarGradientPair g.form (χ j) (χ j) y ≤ (c/j)^2 := by
    simpa only [L18Aux.scalarGradientPair,L18Aux.chartGradientPair_eq_sum,realGradientNormSq] using
      (hcut j hj).2.2.2.2.2 y
  exact he.trans ((mul_le_mul_of_nonneg_right hg (formNormSq_nonneg g.form A y)).trans
    (mul_le_mul_of_nonneg_left (hb y) (sq_nonneg _)))

/-- The canonical cutoff heat has its genuine exterior error as adjacent-degree heat. -/
theorem closed_cutoff_heat_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (η : M.Carrier → ℝ)
    (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (A : RealForm M k) (hA : SmoothRealForm A)
    (B : RealForm M (k+1)) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (t : ℝ) (ht : 0 ≤ t) :
    inner ℝ (hodgeHeatHilbert g μ hμ k t (realizeActualForm g μ (multiplyRealForm η A)
      (smooth_compactlySupported_l2RealForm g μ hμ _ (smoothRealForm_multiply η A hη hA)
        (compactlySupportedRealForm_multiply_scalar η hcη A))))
      (realizeActualForm g μ (codifferentialRealForm g.form B) (codifferentialRealForm_l2 g μ hμ B hB hcB)) =
    inner ℝ (hodgeHeatHilbert g μ hμ (k+1) t
      (realizeActualForm g μ (exteriorRealForm (multiplyRealForm η A))
        (exteriorRealForm_l2 g μ hμ _ (smoothRealForm_multiply η A hη hA)
          (compactlySupportedRealForm_multiply_scalar η hcη A))))
      (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)) :=
  exteriorGraph_heat_core_pairing g μ hμ _ (smoothRealForm_multiply η A hη hA)
    (compactlySupportedRealForm_multiply_scalar η hcη A) B hB hcB t ht

end Yau.NodeProofs.P06Aux.ExteriorHeat
