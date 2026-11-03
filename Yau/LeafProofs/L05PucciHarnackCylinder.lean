import Yau.LeafProofs.L05PucciHarnackAffine

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_inverse_test_jets {n : ℕ} {c : Space n} {R a T h : ℝ}
    (hR : R≠0) (hT : T≠0) {z : Point n} {psi : Point n → ℝ}
    (hpsi : ContDiffAt ℝ 2 psi z) :
    let p := harnackAffine c R a T z
    let phi := fun y => h*psi (harnackAffineInv c R a T y)
    ContDiffAt ℝ 2 phi p ∧ timeD univ phi p=(h*T⁻¹)*timeD univ psi z ∧
      hessian phi p=(h*(R⁻¹)^2) • hessian psi z := by
  intro p phi
  have hPsiInv : ContDiffAt ℝ 2 psi (harnackAffineInv c R a T p) := by
    rw [harnack_affine_inv_apply hR hT]
    exact hpsi
  have hComp : ContDiffAt ℝ 2 (fun y => psi (harnackAffineInv c R a T y)) p :=
    hPsiInv.comp p ((harnack_affineInv_contDiff c R a T).contDiffAt.of_le (by simp))
  have hPsiAdd : ContDiffAt ℝ 2 psi (harnackAffineLinear n R⁻¹ T⁻¹ p+
      (-harnackAffineLinear n R⁻¹ T⁻¹ (c,a+T))) := by
    simpa only [harnackAffineInv,sub_eq_add_neg] using hPsiInv
  have hTime := harnack_affine_pullback_timeD R⁻¹ T⁻¹
    (-harnackAffineLinear n R⁻¹ T⁻¹ (c,a+T)) p hPsiAdd
  have hHess := harnack_affine_pullback_hessian R⁻¹ T⁻¹
    (-harnackAffineLinear n R⁻¹ T⁻¹ (c,a+T)) p hPsiAdd
  change ContDiffAt ℝ 2 (fun y => h*psi (harnackAffineInv c R a T y)) p ∧ _
  refine ⟨contDiffAt_const.mul hComp,?_,?_⟩
  · rw [harnack_timeD_const_mul hComp]
    have ht : timeD univ (fun y => psi (harnackAffineInv c R a T y)) p=
        T⁻¹*timeD univ psi (harnackAffineInv c R a T p) := by
      simpa only [harnackAffineInv,sub_eq_add_neg] using hTime
    rw [ht,harnack_affine_inv_apply hR hT]
    ring
  · rw [harnack_hessian_const_mul hComp]
    have hh : hessian (fun y => psi (harnackAffineInv c R a T y)) p=
        (R⁻¹)^2 • hessian psi (harnackAffineInv c R a T p) := by
      simpa only [harnackAffineInv,sub_eq_add_neg] using hHess
    rw [hh,harnack_affine_inv_apply hR hT,smul_smul]

theorem harnack_touch_below_inverse {n : ℕ} {c : Space n} {R a T h : ℝ}
    (hR : R≠0) (hT : T≠0) (hh : 0 < h) {u psi : Point n → ℝ} {z : Point n}
    (ht : touchBelow psi (fun y => u (harnackAffine c R a T y)/h) z) :
    touchBelow (fun p => h*psi (harnackAffineInv c R a T p)) u (harnackAffine c R a T z) := by
  refine ⟨?_,?_⟩
  · change h*psi (harnackAffineInv c R a T (harnackAffine c R a T z))=u (harnackAffine c R a T z)
    rw [harnack_affine_inv_apply hR hT,ht.1]
    field_simp [hh.ne']
  · have hMap : Tendsto (harnackAffineInv c R a T) (𝓝 (harnackAffine c R a T z)) (𝓝 z) := by
      simpa only [harnack_affine_inv_apply hR hT] using
        (harnack_affineInv_contDiff c R a T).continuous.tendsto (harnackAffine c R a T z)
    filter_upwards [hMap ht.2] with p hp
    change psi (harnackAffineInv c R a T p) ≤ u (harnackAffine c R a T (harnackAffineInv c R a T p))/h at hp
    rw [harnack_affine_apply_inv hR hT] at hp
    simpa only [mul_comm] using (le_div_iff₀ hh).mp hp

theorem harnack_touch_above_inverse {n : ℕ} {c : Space n} {R a T h : ℝ}
    (hR : R≠0) (hT : T≠0) (hh : 0 < h) {u psi : Point n → ℝ} {z : Point n}
    (ht : touchAbove psi (fun y => u (harnackAffine c R a T y)/h) z) :
    touchAbove (fun p => h*psi (harnackAffineInv c R a T p)) u (harnackAffine c R a T z) := by
  refine ⟨?_,?_⟩
  · change h*psi (harnackAffineInv c R a T (harnackAffine c R a T z))=u (harnackAffine c R a T z)
    rw [harnack_affine_inv_apply hR hT,ht.1]
    field_simp [hh.ne']
  · have hMap : Tendsto (harnackAffineInv c R a T) (𝓝 (harnackAffine c R a T z)) (𝓝 z) := by
      simpa only [harnack_affine_inv_apply hR hT] using
        (harnack_affineInv_contDiff c R a T).continuous.tendsto (harnackAffine c R a T z)
    filter_upwards [hMap ht.2] with p hp
    change u (harnackAffine c R a T (harnackAffineInv c R a T p))/h ≤ psi (harnackAffineInv c R a T p) at hp
    rw [harnack_affine_apply_inv hR hT] at hp
    simpa only [mul_comm] using (div_le_iff₀ hh).mp hp

theorem harnack_affine_residual_factor {R T h t F : ℝ} (hR : R≠0) (hT : T≠0) (hh : h≠0) :
    (T/h)*((h*T⁻¹)*t-(h*(R⁻¹)^2)*F)=t-(T/R^2)*F := by
  field_simp [hR,hT,hh]

theorem harnack_super_affine_pullback {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L)
    {D Q : Set (Point n)} {u f : Point n → ℝ}
    (hSuper : viscositySuper Q (fun H _ => harnackPucciMinus ell L H) f u)
    (c : Space n) {R a T h : ℝ} (hR : 0 < R) (hT : 0 < T) (hh : 0 < h)
    (hMap : MapsTo (harnackAffine c R a T) D Q) :
    viscositySuper D
      (fun H _ => harnackPucciMinus ((T/R^2)*ell) ((T/R^2)*L) H)
      (fun z => (T/h)*f (harnackAffine c R a T z))
      (fun z => u (harnackAffine c R a T z)/h) := by
  intro z hz psi hpsi ht
  let phi := fun p => h*psi (harnackAffineInv c R a T p)
  have hJets := harnack_inverse_test_jets (c := c) (a := a) (h := h) hR.ne' hT.ne' hpsi
  have hTouch := harnack_touch_below_inverse hR.ne' hT.ne' hh ht
  have hRes := hSuper _ (hMap hz) phi hJets.1 hTouch
  change f (harnackAffine c R a T z) ≤ timeD univ phi (harnackAffine c R a T z)-
    harnackPucciMinus ell L (hessian phi (harnackAffine c R a T z)) at hRes
  rw [hJets.2.1,hJets.2.2,harnack_minus_smul hell hL (by positivity : 0 ≤ h*(R⁻¹)^2)] at hRes
  have hMul := mul_le_mul_of_nonneg_left hRes (div_nonneg hT.le hh.le)
  rw [harnack_affine_residual_factor hR.ne' hT.ne' hh.ne'] at hMul
  change (T/h)*f (harnackAffine c R a T z) ≤ timeD univ psi z-
    harnackPucciMinus ((T/R^2)*ell) ((T/R^2)*L) (hessian psi z)
  rw [harnack_minus_scale_constants hell hL (div_pos hT (sq_pos_of_ne_zero hR.ne'))]
  exact hMul

theorem harnack_sub_affine_pullback {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L)
    {D Q : Set (Point n)} {u f : Point n → ℝ}
    (hSub : viscositySub Q (fun H _ => pucciPlus ell L H) f u)
    (c : Space n) {R a T h : ℝ} (hR : 0 < R) (hT : 0 < T) (hh : 0 < h)
    (hMap : MapsTo (harnackAffine c R a T) D Q) :
    viscositySub D
      (fun H _ => pucciPlus ((T/R^2)*ell) ((T/R^2)*L) H)
      (fun z => (T/h)*f (harnackAffine c R a T z))
      (fun z => u (harnackAffine c R a T z)/h) := by
  intro z hz psi hpsi ht
  let phi := fun p => h*psi (harnackAffineInv c R a T p)
  have hJets := harnack_inverse_test_jets (c := c) (a := a) (h := h) hR.ne' hT.ne' hpsi
  have hTouch := harnack_touch_above_inverse hR.ne' hT.ne' hh ht
  have hRes := hSub _ (hMap hz) phi hJets.1 hTouch
  change timeD univ phi (harnackAffine c R a T z)-
    pucciPlus ell L (hessian phi (harnackAffine c R a T z)) ≤ f (harnackAffine c R a T z) at hRes
  rw [hJets.2.1,hJets.2.2,harnack_plus_smul hell hL (by positivity : 0 ≤ h*(R⁻¹)^2)] at hRes
  have hMul := mul_le_mul_of_nonneg_left hRes (div_nonneg hT.le hh.le)
  rw [harnack_affine_residual_factor hR.ne' hT.ne' hh.ne'] at hMul
  change timeD univ psi z-pucciPlus ((T/R^2)*ell) ((T/R^2)*L) (hessian psi z) ≤
    (T/h)*f (harnackAffine c R a T z)
  rw [harnack_plus_scale_constants hell hL (div_pos hT (sq_pos_of_ne_zero hR.ne'))]
  exact hMul

end Yau.LeafProofs.L05Aux
