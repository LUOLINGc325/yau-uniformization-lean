import Yau.LeafProofs.L21QuantitativeEvaluation

/-! The literal real Fréchet operator norm is controlled by a finite sum
of true coordinate-word L² energies, through order realDimension+1. -/

open MeasureTheory
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem norm_real_clm_le_sum_realVec {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : X n →L[ℝ] F) : ‖L‖ ≤ ∑ a : Yau.RIdx n, ‖L (Yau.realVec a)‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg fun a _ => norm_nonneg _)
  intro z
  have he : L z = ∑ a : Yau.RIdx n, (realBasis n).repr z a • L (Yau.realVec a) := by
    calc
      _ = L (∑ a, (realBasis n).repr z a • realBasis n a) :=
        congrArg L ((realBasis n).sum_repr z).symm
      _ = _ := by simp only [map_sum, map_smul, realBasis_apply]
  rw [he]
  calc
    _ ≤ ∑ a, ‖(realBasis n).repr z a • L (Yau.realVec a)‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖z‖ * ‖L (Yau.realVec a)‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact (PiLp.norm_apply_le ((realBasis n).repr z) a).trans_eq ((realBasis n).repr.norm_map z)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem norm_real_clm_sq_le_sum_realVec {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : X n →L[ℝ] F) :
    ‖L‖ ^ 2 ≤ (realDimension n : ℝ) * ∑ a : Yau.RIdx n, ‖L (Yau.realVec a)‖ ^ 2 := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Yau.RIdx n => (1 : ℝ))
    (fun a => ‖L (Yau.realVec a)‖)
  have hh : (∑ a : Yau.RIdx n, ‖L (Yau.realVec a)‖) ^ 2 ≤
      (realDimension n : ℝ) * ∑ a : Yau.RIdx n, ‖L (Yau.realVec a)‖ ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, realDimension] using hs
  exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun a _ => norm_nonneg _)).mpr
    (norm_real_clm_le_sum_realVec L)).trans hh

open scoped ContDiff in
theorem complex_compact_fderiv_pointwise_norm_sq_le {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (x : X n) :
    ‖fderiv ℝ f x‖ ^ 2 ≤ (realDimension n : ℝ) *
      ∑ a : Yau.RIdx n, ∑ s : Finset (Fin (realDimension n)),
        ∫ y, ‖wordDerivative f (((s.sort (· ≤ ·)).map (realIndex n).symm) ++ [a]) y‖ ^ 2 ∂Yau.lebesgueC n := by
  apply (norm_real_clm_sq_le_sum_realVec (fderiv ℝ f x)).trans
  apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro a _
  exact complex_compact_directional_pointwise_norm_sq_le hf hcf x a

end Yau.LeafProofs.L21Aux
