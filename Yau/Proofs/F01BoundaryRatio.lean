import Yau.Proofs.F01SegmentFTC

/-! An explicit boundary ratio that remains defined at scale zero. The exact
FTC factorization supplies the cancellation used in the conformal Gram matrix. -/
open Set
open scoped ContDiff Interval
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def boundaryRatio (u : E → ℝ) (L c : ℝ) (z₀ : E) (δ : ℝ) (z : E) : ℝ :=
  1 - c / L * (∫ t in (0 : ℝ)..1, fderiv ℝ u (z₀ + (t * (c * δ)) • z) z)

theorem boundary_gap_factorization {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) (z₀ z : E) (L c δ : ℝ)
    (hL : L ≠ 0) (hbase : 1 - u z₀ / L = δ)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, z₀ + (t * (c * δ)) • z ∈ U) :
    1 - u (z₀ + (c * δ) • z) / L = δ * boundaryRatio u L c z₀ δ z := by
  have hFTC := scaled_segment_integral_fderiv hU hu z₀ z (c * δ) hseg
  unfold boundaryRatio
  field_simp [hL] at hbase ⊢
  simp only [mul_comm, mul_left_comm, mul_assoc] at hFTC ⊢
  nlinarith [hFTC]

theorem boundaryRatio_bounds_of_integral_budget (u : E → ℝ) (L c : ℝ)
    (z₀ : E) (δ : ℝ) (z : E)
    (hbudget : |c / L * (∫ t in (0 : ℝ)..1,
      fderiv ℝ u (z₀ + (t * (c * δ)) • z) z)| ≤ 1 / 2) :
    1 / 2 ≤ boundaryRatio u L c z₀ δ z ∧ boundaryRatio u L c z₀ δ z ≤ 3 / 2 := by
  have hb := abs_le.mp hbudget
  unfold boundaryRatio
  constructor <;> linarith

end Yau.NodeProofs.F01Aux
