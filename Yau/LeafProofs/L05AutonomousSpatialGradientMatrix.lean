import Yau.LeafProofs.L05ComplexRepresentation

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- A dimensional budget fixed before the actual derivative or function. -/
def spatialGradientDimensionBudget (n : ℕ) : ℝ := (Fintype.card (Yau.RIdx n) : ℝ) ^ 2 + 1

theorem spatialGradientDimensionBudget_pos (n : ℕ) : 0 < spatialGradientDimensionBudget n := by
  unfold spatialGradientDimensionBudget
  positivity

/-- The actual real orthonormal coordinate expansion of a continuous bilinear form. -/
theorem spatialGradient_bilinear_expansion {n : ℕ}
    (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) (v w : Space n) :
    B v w = ∑ i, ∑ j, B (Yau.realVec i) (Yau.realVec j) *
      inner ℝ (Yau.realVec i) v * inner ℝ (Yau.realVec j) w := by
  have hcoords (z : Space n) : (∑ i : Yau.RIdx n, inner ℝ (Yau.realVec i) z • Yau.realVec i) = z := by
    simpa only [complexVector_realOrthonormalBasis_apply] using
      (complexVector_realOrthonormalBasis n).sum_repr' z
  calc
    _ = B (∑ i : Yau.RIdx n, inner ℝ (Yau.realVec i) v • Yau.realVec i)
        (∑ j : Yau.RIdx n, inner ℝ (Yau.realVec j) w • Yau.realVec j) := by rw [hcoords, hcoords]
    _ = _ := by
      simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Actual finite entries, with the matrix type retained before choosing its norm instance. -/
def spatialGradientBilinearMatrix {n : ℕ}
    (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) : Mat n :=
  fun i j => B (Yau.realVec i) (Yau.realVec j)

/-- The Frobenius matrix controls the genuine nested operator norm, also in dimension zero. -/
theorem spatialGradient_bilinear_frobenius_bound {n : ℕ}
    (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    ‖B‖ ≤ spatialGradientDimensionBudget n *
      ‖spatialGradientBilinearMatrix B‖ := by
  let A : Mat n := spatialGradientBilinearMatrix B
  have hentry (i j : Yau.RIdx n) : |A i j| ≤ ‖A‖ := by
    have hRow := PiLp.norm_apply_le (WithLp.toLp 2 (fun k : Yau.RIdx n => A i k)) j
    have hMatrix := PiLp.norm_apply_le
      (WithLp.toLp 2 (fun l : Yau.RIdx n => WithLp.toLp 2 (fun k : Yau.RIdx n => A l k))) i
    change |A i j| ≤ ‖WithLp.toLp 2 (fun l : Yau.RIdx n => WithLp.toLp 2 (fun k : Yau.RIdx n => A l k))‖
    simpa only [Real.norm_eq_abs] using hRow.trans hMatrix
  have hcoord (v : Space n) (hv : ‖v‖ = 1) (i : Yau.RIdx n) : |inner ℝ (Yau.realVec i) v| ≤ 1 := by
    have he : ‖Yau.realVec i‖ = 1 := by
      simpa only [complexVector_realOrthonormalBasis_apply] using
        (complexVector_realOrthonormalBasis n).orthonormal.norm_eq_one i
    simpa [Real.norm_eq_abs, he, hv] using norm_inner_le_norm (𝕜 := ℝ) (Yau.realVec i) v
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg (spatialGradientDimensionBudget_pos n).le (norm_nonneg A))
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg (spatialGradientDimensionBudget_pos n).le (norm_nonneg A))
  intro w hw
  rw [Real.norm_eq_abs, spatialGradient_bilinear_expansion]
  calc
    _ ≤ ∑ i : Yau.RIdx n, |∑ j : Yau.RIdx n, A i j * inner ℝ (Yau.realVec i) v * inner ℝ (Yau.realVec j) w| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Yau.RIdx n, ∑ _j : Yau.RIdx n, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_mul]
        calc
          _ ≤ ‖A‖ * 1 * 1 := by gcongr; exact hentry i j; exact hcoord v hv i; exact hcoord w hw j
          _ = _ := by ring)
    _ ≤ spatialGradientDimensionBudget n * ‖A‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold spatialGradientDimensionBudget
      nlinarith [norm_nonneg A]

/-- This is a bound on the actual second Frechet derivative, not a supplied jet. -/
theorem spatialGradient_second_derivative_bound {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ spatialGradientDimensionBudget n * ‖secondFDerivMatrix f x‖ :=
  spatialGradient_bilinear_frobenius_bound _

end Yau.LeafProofs.L05AutonomousAux
