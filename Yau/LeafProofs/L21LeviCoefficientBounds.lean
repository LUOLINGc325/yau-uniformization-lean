import Yau.LeafProofs.L21LeviHessianPositive
import Yau.LeafProofs.L21MixedFrame

/-! Explicit small first-order coefficient errors in the corrected Levi
matrix. All bounds use the actual real row derivatives. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem leviFirstCoefficient_norm_bound {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {x : X n} (hx : x ∈ O) (hA0 : ∀ i k, ‖A x i k‖ ≤ 1)
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hDA : ∀ i k, ‖fderiv ℝ (fun y => A y i k) x‖ ≤ ε)
    (d : Fin n → Fin n → Fin n → X n → ℂ)
    (hd : ∀ i j k, ‖d i j k x‖ ≤ C * ε) (i j : Fin n) (b : Yau.RIdx n) :
    ‖leviFirstCoefficient A d i j b x‖ ≤
      (2 * (realDimension n : ℝ) + 2 * (n : ℝ) * C) * ε := by
  have hDiff (r k : Fin n) := ((hA r k).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hp (r : Fin n) (a : Yau.RIdx n) := mixedFrame_row_norm hA0 r a
  have hDp : ‖fderiv ℝ (fun y => star (dbarRealCoefficient A j b y)) x‖ ≤ ε := by
    rw [mixedFrame_fderiv_star_norm]
    exact (mixedFrame_row_fderiv_norm hDiff j b).trans (hDA j b.1)
  have hDir (a : Yau.RIdx n) :
      ‖fderiv ℝ (fun y => star (dbarRealCoefficient A j b y)) x (Yau.realVec a)‖ ≤ ε := by
    simpa only [mixedFrame_realVec_norm, mul_one] using
      ((fderiv ℝ (fun y => star (dbarRealCoefficient A j b y)) x).le_opNorm (Yau.realVec a)).trans
        (mul_le_mul_of_nonneg_right hDp (norm_nonneg _))
  have hHead : ‖∑ a : Yau.RIdx n, dbarRealCoefficient A i a x *
      fderiv ℝ (fun y => star (dbarRealCoefficient A j b y)) x (Yau.realVec a)‖ ≤
        (realDimension n : ℝ) * (2 * ε) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _a : Yau.RIdx n, 2 * ε := by
        apply Finset.sum_le_sum
        intro a _
        rw [norm_mul]
        exact mul_le_mul (hp i a) (hDir a) (norm_nonneg _) (by norm_num)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, realDimension]
  have hTail : ‖∑ k, d i j k x * star (dbarRealCoefficient A k b x)‖ ≤
      (n : ℝ) * (C * ε * 2) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _k : Fin n, C * ε * 2 := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul, norm_star]
        exact mul_le_mul (hd i j k) (hp k b) (norm_nonneg _) (mul_nonneg hC hε)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (norm_sub_le _ _).trans ((add_le_add hHead hTail).trans_eq (by ring))

theorem mixedFrameDerivativeSize_le_jet {O : Set (X n)}
    {A : X n → Matrix (Fin n) (Fin n) ℂ} {ε : ℝ}
    (hJet : JetBound 1 ε A O) {x : X n} (hx : x ∈ O) :
    mixedFrameDerivativeSize A x ≤ (n : ℝ) ^ 2 * ε := by
  calc
    _ ≤ ∑ _i : Fin n, ∑ _k : Fin n, ε := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      simpa only [norm_iteratedFDeriv_one] using hJet 1 le_rfl x hx i k
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Yau.LeafProofs.L21Aux
