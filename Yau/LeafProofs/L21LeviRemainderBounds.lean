import Yau.LeafProofs.L21UniformCorrectedLevi
import Yau.LeafProofs.L21QuantitativeCoefficients

/-! The corrected weighted commutator's remaining zero-order coefficients
have bounds independent of the weight and of its boundary singularity. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem conjugateDivergence_bounds {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hJet : JetBound 2 1 A O) {x : X n} (hx : x ∈ O) (j : Fin n) :
    ‖conjugateDivergence A j x‖ ≤ (realDimension n : ℝ) ∧
      ‖fderiv ℝ (conjugateDivergence A j) x‖ ≤ (realDimension n : ℝ) := by
  let p (b : Yau.RIdx n) : X n → ℂ := fun y => star (dbarRealCoefficient A j b y)
  have hp (b : Yau.RIdx n) : ContDiffAt ℝ ∞ (p b) x :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffAt x
      ((dbarRealCoefficient_smoothOn hA j b).contDiffAt (hO.mem_nhds hx))
  have hD (b : Yau.RIdx n) : ‖fderiv ℝ (p b) x‖ ≤ 1 := by
    rw [← norm_iteratedFDeriv_one, mixedFrame_iterated_star_norm]
    exact norm_iteratedFDeriv_dbarRealCoefficient_le_one hO hA hJet 1 (by omega) x hx j b
  have hDD (b : Yau.RIdx n) : ‖fderiv ℝ (fderiv ℝ (p b)) x‖ ≤ 1 := by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ (p b)), norm_iteratedFDeriv_fderiv,
      mixedFrame_iterated_star_norm]
    exact norm_iteratedFDeriv_dbarRealCoefficient_le_one hO hA hJet 2 (by omega) x hx j b
  have hG (b : Yau.RIdx n) : DifferentiableAt ℝ (fun y => fderiv ℝ (p b) y (Yau.realVec b)) x :=
    ((hp b).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp) |>.clm_apply (differentiableAt_const _)
  have hGBound (b : Yau.RIdx n) :
      ‖fderiv ℝ (fun y => fderiv ℝ (p b) y (Yau.realVec b)) x‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    rw [fderiv_directional (((hp b).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ (p b)) x v‖ * ‖Yau.realVec b‖ :=
        (fderiv ℝ (fderiv ℝ (p b)) x v).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ (p b)) x‖ * ‖v‖) * ‖Yau.realVec b‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ (p b)) x).le_opNorm v) (norm_nonneg _)
      _ ≤ (1 * ‖v‖) * ‖Yau.realVec b‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hDD b) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by rw [mixedFrame_realVec_norm]; ring
  constructor
  · apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _b : Yau.RIdx n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro b _
        have hh := ((fderiv ℝ (p b) x).le_opNorm (Yau.realVec b)).trans
          (mul_le_mul_of_nonneg_right (hD b) (norm_nonneg _))
        simpa only [mixedFrame_realVec_norm, mul_one] using hh
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, realDimension]
  · change ‖fderiv ℝ (fun y => ∑ b : Yau.RIdx n, fderiv ℝ (p b) y (Yau.realVec b)) x‖ ≤ _
    rw [fderiv_fun_sum (A := fun b y => fderiv ℝ (p b) y (Yau.realVec b)) (fun b _ => hG b)]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun b _ => hGBound b).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, realDimension]))

theorem weightedCommutatorRemainder_norm_bound {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hJet : JetBound 2 1 A O) (d : Fin n → Fin n → Fin n → X n → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hd : ∀ x ∈ O, ∀ i j k, ‖d i j k x‖ ≤ M)
    {x : X n} (hx : x ∈ O) (i j : Fin n) :
    ‖weightedCommutatorRemainder A d i j x‖ ≤
      (n : ℝ) * M * (realDimension n : ℝ) + 4 * (n : ℝ) * (realDimension n : ℝ) := by
  have hp (a : Yau.RIdx n) := mixedFrame_row_norm
    (fun r s => (mixedFrame_jet_fderiv hJet hx r s).1) i a
  have hDdiv : ‖dbarA A i (conjugateDivergence A j) x‖ ≤
      4 * (n : ℝ) * (realDimension n : ℝ) := by
    have hh := mixedFrame_rowApply_norm (dbarRealCoefficient A i) (conjugateDivergence A j) x hp
    change ‖∑ a : Yau.RIdx n, dbarRealCoefficient A i a x *
      fderiv ℝ (conjugateDivergence A j) x (Yau.realVec a)‖ ≤ _ at hh
    rw [← dbarA_eq_real_rows] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (conjugateDivergence_bounds hO hA hJet hx j).2
      (by positivity)).trans_eq (by ring))
  have hSum : ‖∑ k, d i j k x * conjugateDivergence A k x‖ ≤
      (n : ℝ) * (M * (realDimension n : ℝ)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _k : Fin n, M * (realDimension n : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul]
        exact mul_le_mul (hd x hx i j k) (conjugateDivergence_bounds hO hA hJet hx k).1
          (norm_nonneg _) hM
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (norm_sub_le _ _).trans ((add_le_add hSum hDdiv).trans_eq (by ring))

end Yau.LeafProofs.L21Aux
