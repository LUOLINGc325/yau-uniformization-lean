import Yau.LeafProofs.L16ExpBoundaryDefiningOperator

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

def sphereBarrier {n : ℕ} (y x : Space n) : ℝ := ‖x-y‖^2

theorem sphereBarrier_contDiff {n : ℕ} (y : Space n) :
    ContDiff ℝ ∞ (sphereBarrier y) := (contDiff_id.sub contDiff_const).norm_sq ℝ

theorem sphereBarrier_fderiv {n : ℕ} (y : Space n) :
    fderiv ℝ (sphereBarrier y) = fun x => (2 : ℝ) • innerSL ℝ (x-y) := by
  funext x
  change fderiv ℝ (fun z : Space n => ‖z-y‖^2) x = (2 : ℝ) • innerSL ℝ (x-y)
  simpa only [sphereBarrier,id_eq,ContinuousLinearMap.comp_id,two_smul] using
    (((hasFDerivAt_id x).sub_const y).norm_sq).fderiv

set_option backward.isDefEq.respectTransparency.types false in
theorem sphereBarrier_secondFDeriv {n : ℕ} (y : Space n) :
    fderiv ℝ (fderiv ℝ (sphereBarrier y)) =
      fun _ => (2 : ℝ) • L16Aux.realInnerBilinear (n := n) := by
  rw [sphereBarrier_fderiv]
  have hfun : (fun x : Space n => (2 : ℝ) • innerSL ℝ (x-y)) =
      fun x : Space n => (2 : ℝ) • L16Aux.realInnerBilinear (x-y) := by
    funext x
    ext v
    rfl
  rw [hfun]
  funext x
  have h := (((L16Aux.realInnerBilinear (n := n)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const y)).const_smul (2 : ℝ))
  change HasFDerivAt (fun z : Space n => (2 : ℝ) • L16Aux.realInnerBilinear (z-y))
    ((2 : ℝ) • (L16Aux.realInnerBilinear.comp (ContinuousLinearMap.id ℝ (Space n)))) x at h
  simpa only [ContinuousLinearMap.comp_id] using h.fderiv

theorem sphereBarrier_gradient_bound {n : ℕ} (y x : Space n) (i : Yau.RIdx n) :
    |d (sphereBarrier y) x i| ≤ 2*‖x-y‖ := by
  simp only [d,sphereBarrier_fderiv,smul_apply,smul_eq_mul,innerSL_apply_apply,abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left (by
    simpa only [L16Aux.realVec_norm,mul_one] using abs_real_inner_le_norm (x-y) (Yau.realVec i))
      (by norm_num)

/-- A safe entrywise estimate for the artificial-sphere correction. It needs
no regularity or derivative bounds of either coefficient field. -/
theorem sphereBarrier_operator_abs_bound {n : ℕ} {A : Mat n}
    {β : Yau.RIdx n → ℝ} {A₀ b₀ r : ℝ} (hA₀ : 0 ≤ A₀) (hb₀ : 0 ≤ b₀)
    (hA : ∀ i j, |A i j| ≤ A₀) (hβ : ∀ i, |β i| ≤ b₀)
    {y x : Space n} (hxy : ‖x-y‖ ≤ r) :
    |-(∑ i, ∑ j, A i j*fderiv ℝ (fderiv ℝ (sphereBarrier y)) x
        (Yau.realVec i) (Yau.realVec j)) - ∑ i, β i*d (sphereBarrier y) x i| ≤
      (∑ _i : Yau.RIdx n, ∑ _j : Yau.RIdx n, A₀*2) +
        ∑ _i : Yau.RIdx n, b₀*(2*r) := by
  have hH (i j : Yau.RIdx n) :
      |fderiv ℝ (fderiv ℝ (sphereBarrier y)) x (Yau.realVec i) (Yau.realVec j)| ≤ 2 := by
    rw [sphereBarrier_secondFDeriv]
    simp only [smul_apply,smul_eq_mul,L16Aux.realInnerBilinear_apply,abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := abs_real_inner_le_norm (Yau.realVec i) (Yau.realVec j)
    simp only [L16Aux.realVec_norm,mul_one] at h
    linarith
  have hD (i : Yau.RIdx n) : |d (sphereBarrier y) x i| ≤ 2*r :=
    (sphereBarrier_gradient_bound y x i).trans (by linarith)
  rw [sub_eq_add_neg,← neg_add,abs_neg]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [abs_mul]
    exact mul_le_mul (hA i j) (hH i j) (abs_nonneg _) hA₀
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul]
    exact mul_le_mul (hβ i) (hD i) (abs_nonneg _) hb₀

end Yau.LeafProofs.L16ExpBoundaryAux
