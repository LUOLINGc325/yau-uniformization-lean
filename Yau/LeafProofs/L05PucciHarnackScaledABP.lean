import Yau.LeafProofs.L05PucciHarnackCylinder
import Yau.LeafProofs.L05PucciHarnackAffineMeasure

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackABPCoefficient (n : ℕ) (ell R T : ℝ) : ℝ :=
  abpC n ((T/R^2)*ell)*T /
    (harnackAffineJacobian n R T)^(1/((2*n+1 : ℕ):ℝ))

theorem harnack_abpCoefficient_pos (n : ℕ) {ell R T : ℝ}
    (hell : 0 < ell) (hR : 0 < R) (hT : 0 < T) :
    0 < harnackABPCoefficient n ell R T := by
  unfold harnackABPCoefficient
  exact div_pos (mul_pos (abpC_pos n (mul_pos (div_pos hT (sq_pos_of_ne_zero hR.ne')) hell)) hT)
    (Real.rpow_pos_of_pos (harnack_affineJacobian_pos hR hT) _)

theorem harnack_integral_scaled_source {n : ℕ} (c : Space n) {R a T : ℝ}
    (hR : 0 < R) (hT : 0 < T) (g : Point n → ℝ) :
    (∫ z in unitOpen n, (max (T*g (harnackAffine c R a T z)) 0)^(2*n+1))=
      T^(2*n+1)*(harnackAffineJacobian n R T)⁻¹*
        (∫ p in harnackOpen c R a T, (max (g p) 0)^(2*n+1)) := by
  have hMax (x : ℝ) : max (T*x) 0=T*max x 0 := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_left (mul_nonneg hT.le hx),max_eq_left hx]
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hT.le (le_of_not_ge hx)),
        max_eq_right (le_of_not_ge hx),mul_zero]
  simp_rw [hMax,mul_pow]
  rw [integral_const_mul,harnack_integral_affine_open (a := a) c hR hT
    (fun p => (max (g p) 0)^(2*n+1))]
  ring

theorem harnack_scaled_source_root {n : ℕ} {R T sourceIntegral : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hI : 0 ≤ sourceIntegral) :
    (T^(2*n+1)*(harnackAffineJacobian n R T)⁻¹*sourceIntegral)^(1/((2*n+1 : ℕ):ℝ))=
      T/(harnackAffineJacobian n R T)^(1/((2*n+1 : ℕ):ℝ))*
        sourceIntegral^(1/((2*n+1 : ℕ):ℝ)) := by
  have hJ := harnack_affineJacobian_pos (n := n) hR hT
  rw [Real.mul_rpow (mul_nonneg (pow_nonneg hT.le _) (inv_nonneg.mpr hJ.le)) hI,
    Real.mul_rpow (pow_nonneg hT.le _) (inv_nonneg.mpr hJ.le),
    one_div,Real.pow_rpow_inv_natCast hT.le (by omega),Real.inv_rpow hJ.le]
  rw [div_eq_mul_inv]

theorem harnack_scaled_abp {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) (c : Space n) {R a T : ℝ}
    (hR : 0 < R) (hT : 0 < T) {w g : Point n → ℝ}
    (hw : ContinuousOn w (harnackClosed c R a T))
    (hg : ContinuousOn g (harnackClosed c R a T))
    (hboundary : ∀ z∈harnackBoundary c R a T, w z ≤ 0)
    (hsub : viscositySub (harnackOpen c R a T) (fun H _ => pucciPlus ell L H) g w)
    {p : Point n} (hp : p∈harnackClosed c R a T) :
    w p ≤ harnackABPCoefficient n ell R T*
      (∫ z in harnackOpen c R a T, (max (g z) 0)^(2*n+1))^(1/((2*n+1 : ℕ):ℝ)) := by
  have hMap : MapsTo (harnackAffine c R a T) (unitClosed n) (harnackClosed c R a T) :=
    fun z hz => (harnack_affine_closed_mem_iff (a := a) c hR hT z).mpr hz
  have hMapOpen : MapsTo (harnackAffine c R a T) (unitOpen n) (harnackOpen c R a T) :=
    fun z hz => (harnack_affine_open_mem_iff (a := a) c hR hT z).mpr hz
  have hW : ContinuousOn (fun z => w (harnackAffine c R a T z)) (unitClosed n) :=
    hw.comp (harnack_affine_contDiff c R a T).continuous.continuousOn hMap
  have hG : ContinuousOn (fun z => T*g (harnackAffine c R a T z)) (unitClosed n) :=
    continuousOn_const.mul (hg.comp (harnack_affine_contDiff c R a T).continuous.continuousOn hMap)
  have hBd (z : Point n) (hz : z∈parabolicBoundary n) :
      w (harnackAffine c R a T z) ≤ 0 :=
    hboundary _ (harnack_affine_maps_boundary c hR hT hz)
  have hPull := harnack_sub_affine_pullback hell.le hL hsub c (a := a) hR hT
    (by norm_num : (0 : ℝ) < 1) hMapOpen
  simp only [div_one] at hPull
  have hq : 0 < T/R^2 := div_pos hT (sq_pos_of_ne_zero hR.ne')
  have hqL : (T/R^2)*ell ≤ (T/R^2)*L := mul_le_mul_of_nonneg_left hL hq.le
  have hpInv : harnackAffineInv c R a T p∈unitClosed n :=
    (harnack_affine_closed_mem_iff (a := a) c hR hT _).mp
      (by rwa [harnack_affine_apply_inv hR.ne' hT.ne'])
  have hABP := viscosity_abp_closed (mul_pos hq hell) hqL hW hG hBd hPull hpInv
  rw [harnack_affine_apply_inv hR.ne' hT.ne',harnack_integral_scaled_source c hR hT] at hABP
  have hI : 0 ≤ ∫ z in harnackOpen c R a T, (max (g z) 0)^(2*n+1) :=
    integral_nonneg (fun _ => pow_nonneg (le_max_right _ _) _)
  rw [harnack_scaled_source_root hR hT hI] at hABP
  convert hABP using 1
  unfold harnackABPCoefficient
  ring

theorem harnack_smooth_cylinder_comparison {n : ℕ} {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) (c : Space n) {R a T : ℝ}
    (hR : 0 < R) (hT : 0 < T) {u Phi : Point n → ℝ}
    (hu : ContinuousOn u (harnackClosed c R a T))
    (hPhi : ∀ z∈harnackClosed c R a T, ContDiffAt ℝ 2 Phi z)
    (hSuper : viscositySuper (harnackOpen c R a T)
      (fun H _ => harnackPucciMinus ell L H) (fun _ => 0) u)
    (hRes : ∀ z∈harnackOpen c R a T,
      timeD univ Phi z-harnackPucciMinus ell L (hessian Phi z) ≤ 0)
    (hBd : ∀ z∈harnackBoundary c R a T, Phi z ≤ u z) :
    ∀ z∈harnackClosed c R a T, Phi z ≤ u z := by
  have hQS : harnackOpen c R a T ⊆ harnackClosed c R a T := by
    rintro z ⟨hx,ht⟩
    exact ⟨Metric.ball_subset_closedBall hx,le_of_lt ht.1,le_of_lt ht.2⟩
  have hPhiCont : ContinuousOn Phi (harnackClosed c R a T) :=
    fun z hz => (hPhi z hz).continuousAt.continuousWithinAt
  have hSub := harnack_smooth_minus_super_sub hell.le hL
    (fun z hz => hPhi z (hQS hz)) hSuper hRes
  have hBoundary : ∀ z∈harnackBoundary c R a T, Phi z-u z ≤ 0 :=
    fun z hz => sub_nonpos.mpr (hBd z hz)
  intro z hz
  have h := harnack_scaled_abp hell hL c hR hT
    (hPhiCont.sub hu) continuousOn_const hBoundary hSub hz
  have hz0 : (Phi-u) z ≤ 0 := by
    simpa only [max_self,zero_pow (by omega : 2*n+1≠0),integral_zero,
      Real.zero_rpow (by positivity : (1 : ℝ)/((2*n+1 : ℕ):ℝ)≠0),mul_zero] using h
  exact sub_nonpos.mp hz0

end Yau.LeafProofs.L05Aux
