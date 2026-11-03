import Yau.Proofs.C02CurvatureBasisTransform
import Yau.Proofs.C02UnitaryMatrixTrace

/-! The scalar coefficient trace in a unitary frame is the original
inverse-metric contraction. All sums remain finite in arbitrary dimension. -/

noncomputable section
open scoped Matrix
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}

theorem curvatureTrace_basisTransform (C : CurvatureArray n)
    (S : Matrix (Fin n) (Fin n) ℂ) :
    curvatureTrace (curvatureBasisTransform C S) =
      (∑ a, ∑ b, ∑ c, ∑ d, C a b c d *
        (∑ i, star (S a i) * S b i) * (∑ k, star (S c k) * S d k)).re := by
  change (∑ k, ∑ i, curvatureBasisTransform C S i i k k).re = _
  apply congrArg Complex.re
  simp only [curvatureBasisTransform, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext v0
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    arg 2
    ext v3
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext v0
    arg 2
    ext v1
    arg 2
    ext v2
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a0 _
  apply Finset.sum_congr rfl
  intro a1 _
  apply Finset.sum_congr rfl
  intro a2 _
  apply Finset.sum_congr rfl
  intro a3 _
  apply Finset.sum_congr rfl
  intro a4 _
  apply Finset.sum_congr rfl
  intro a5 _
  ring

theorem curvatureTrace_basisTransform_eq_traceWith (C : CurvatureArray n)
    (H R S : Matrix (Fin n) (Fin n) ℂ) (hS : S.conjTranspose * H * S = 1)
    (hR : ∀ a b, R a b = ∑ c, ∑ d, H⁻¹ d c * C a b c d) :
    curvatureTrace (curvatureBasisTransform C S) = traceWith H R := by
  rw [curvatureTrace_basisTransform]
  simp_rw [inverseMetric_entry_unitaryMatrix H S hS]
  rw [traceWith]
  apply congrArg Complex.re
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hR, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

end Yau.Blueprint.C02Proof
