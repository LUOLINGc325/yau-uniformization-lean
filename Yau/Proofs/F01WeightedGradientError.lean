import Yau.Proofs.F01WeightedCovectorCauchy
import Yau.Proofs.F01CorrectedRowGradient

/-! The finite weighted gradient error for the actual masked conformal
correction.  The estimate keeps the Rayleigh logarithmic gradient explicit. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {n : ℕ}

theorem weightedCovectorSquare_mask_le (weights : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (a : Fin n) (η : Fin n → ℂ) :
    weightedCovectorSquare weights (maskedCoordinate a η) ≤
      weightedCovectorSquare weights η := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hia : i = a
  · simp only [maskedCoordinate, if_pos hia, map_zero, mul_zero]
    exact mul_nonneg (hw i) (Complex.normSq_nonneg _)
  · simp only [maskedCoordinate, if_neg hia]
    exact le_rfl

theorem weighted_gradient_correction_identity (weights : Fin n → ℝ)
    (a : Fin n) (ξ η : Fin n → ℂ) (s : ℝ) :
    weightedCovectorSquare weights (fun i => ξ i + η i) -
        weightedCovectorSquare weights (fun i => ξ i + η i - (s : ℂ) * maskedCoordinate a η i) =
      2 * s * weightedCovectorPair weights ξ (maskedCoordinate a η) +
        (2 * s - s ^ 2) * weightedCovectorSquare weights (maskedCoordinate a η) := by
  calc
    _ = ∑ i, (2 * s * (weights i * (ξ i * star (maskedCoordinate a η i)).re) +
        (2 * s - s ^ 2) * (weights i * Complex.normSq (maskedCoordinate a η i))) := by
      unfold weightedCovectorSquare
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hia : i = a
      · simp [maskedCoordinate, hia]
      · simp only [maskedCoordinate, if_neg hia, Complex.normSq_apply,
          Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.star_def, Complex.conj_re, Complex.conj_im]
        ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, weightedCovectorPair, weightedCovectorSquare,
        Finset.mul_sum]

theorem weighted_gradient_correction_le (weights : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (a : Fin n) (ξ η : Fin n → ℂ)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    weightedCovectorSquare weights (fun i => ξ i + η i) -
        weightedCovectorSquare weights (fun i => ξ i + η i - (s : ℂ) * maskedCoordinate a η i) ≤
      2 * s * Real.sqrt (weightedCovectorSquare weights ξ) *
        Real.sqrt (weightedCovectorSquare weights η) +
          2 * weightedCovectorSquare weights η := by
  rw [weighted_gradient_correction_identity]
  have hmask := weightedCovectorSquare_mask_le weights hw a η
  have hn := weightedCovectorSquare_nonneg weights hw (maskedCoordinate a η)
  have hη := weightedCovectorSquare_nonneg weights hw η
  have hp := weightedCovectorPair_le_sqrt weights hw ξ (maskedCoordinate a η)
  have hroot := Real.sqrt_le_sqrt hmask
  have hprod := mul_le_mul_of_nonneg_left hroot
    (Real.sqrt_nonneg (weightedCovectorSquare weights ξ))
  have hpair := mul_le_mul_of_nonneg_left (hp.trans hprod) (by positivity : 0 ≤ 2 * s)
  have hcoef : (2 * s - s ^ 2) * weightedCovectorSquare weights (maskedCoordinate a η) ≤
      2 * weightedCovectorSquare weights η := by
    have hfirst : (2 * s - s ^ 2) * weightedCovectorSquare weights (maskedCoordinate a η) ≤
        2 * s * weightedCovectorSquare weights (maskedCoordinate a η) := by
      nlinarith [sq_nonneg s]
    have hsecond := mul_le_mul_of_nonneg_left hmask (by positivity : 0 ≤ 2 * s)
    have hthird := mul_le_mul_of_nonneg_right hs1 hη
    nlinarith
  nlinarith [hpair, hcoef]

end Yau.NodeProofs.F01Aux
