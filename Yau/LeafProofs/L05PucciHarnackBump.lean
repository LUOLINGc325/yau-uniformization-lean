import Yau.LeafProofs.L05PucciHarnackAlgebra

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_positivePower_hasDerivAt {m : ℕ} (hm : 1 < m) (x : ℝ) :
    HasDerivAt (fun q : ℝ => (max q 0)^m)
      ((m : ℝ)*(max x 0)^(m-1)) x := by
  have hm0 : m≠0 := by omega
  have hm1 : m-1≠0 := by omega
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hEq : (fun q : ℝ => (max q 0)^m) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with q hq
      change q<0 at hq
      simp only [max_eq_right hq.le,zero_pow hm0]
    have hd := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hEq
    simpa only [max_eq_right hx.le,zero_pow hm1,mul_zero] using hd
  · have hLeft : HasDerivWithinAt (fun q : ℝ => (max q 0)^m) 0 (Iic 0) 0 := by
      apply (hasDerivAt_const 0 (0 : ℝ)).hasDerivWithinAt.congr
      · intro q hq
        change q≤0 at hq
        simp only [max_eq_right hq,zero_pow hm0]
      · simp [hm0]
    have hRight : HasDerivWithinAt (fun q : ℝ => (max q 0)^m) 0 (Ici 0) 0 := by
      have hd := ((hasDerivAt_id (0 : ℝ)).pow m).hasDerivWithinAt (s := Ici 0)
      have hd0 : HasDerivWithinAt (fun q : ℝ => q^m) 0 (Ici 0) 0 := by
        convert! hd using 1
        simp only [id_eq,zero_pow hm1,mul_zero,mul_one]
      apply hd0.congr
      · intro q hq
        change 0≤q at hq
        rw [max_eq_left hq]
      · simp
    have hd := hLeft.union hRight
    simpa only [Iic_union_Ici,hasDerivWithinAt_univ,max_self,zero_pow hm1,mul_zero] using hd
  · have hEq : (fun q : ℝ => (max q 0)^m) =ᶠ[𝓝 x] (fun q => q^m) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with q hq
      change 0<q at hq
      rw [max_eq_left hq.le]
    simpa only [max_eq_left hx.le,mul_one,id_eq] using
      ((hasDerivAt_id x).pow m).congr_of_eventuallyEq hEq

def harnackPositiveCube (q : ℝ) : ℝ := (max q 0)^3

theorem harnack_positiveCube_hasDerivAt (q : ℝ) :
    HasDerivAt harnackPositiveCube (3*(max q 0)^2) q := by
  exact harnack_positivePower_hasDerivAt (by norm_num : 1<3) q

theorem harnack_positiveSquare_contDiff :
    ContDiff ℝ 1 (fun q : ℝ => (max q 0)^2) := by
  have hD (q : ℝ) : HasDerivAt (fun x : ℝ => (max x 0)^2) (2*max q 0) q := by
    simpa using harnack_positivePower_hasDerivAt (by norm_num : 1<2) q
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun q => (hD q).differentiableAt,?_⟩
  have he : deriv (fun q : ℝ => (max q 0)^2)=(fun q => 2*max q 0) := by
    funext q
    exact (hD q).deriv
  rw [he]
  exact (continuous_id.max continuous_const).const_mul 2

theorem harnack_positiveCube_contDiff : ContDiff ℝ 2 harnackPositiveCube := by
  change ContDiff ℝ ((1 : ℕ∞ω)+1) harnackPositiveCube
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun q => (harnack_positiveCube_hasDerivAt q).differentiableAt,by simp,?_⟩
  have he : deriv harnackPositiveCube=(fun q => 3*(max q 0)^2) := by
    funext q
    exact (harnack_positiveCube_hasDerivAt q).deriv
  rw [he]
  exact contDiff_const.mul harnack_positiveSquare_contDiff

theorem harnack_positiveCube_deriv_hasDerivAt (q : ℝ) :
    HasDerivAt (deriv harnackPositiveCube) (6*max q 0) q := by
  have he : deriv harnackPositiveCube=(fun x => 3*(max x 0)^2) := by
    funext x
    exact (harnack_positiveCube_hasDerivAt x).deriv
  rw [he]
  convert! (harnack_positivePower_hasDerivAt (by norm_num : 1<2) q).const_mul 3 using 1
  simp only [Nat.cast_ofNat]
  ring

/-- The quintic step is written as two positive-part polynomials; its
first two derivatives therefore agree at both joins. -/
def harnackStep (q : ℝ) : ℝ :=
  harnackPositiveCube q*(10-15*q+6*q^2)-
    harnackPositiveCube (q-1)*(10+15*(q-1)+6*(q-1)^2)

theorem harnack_step_contDiff : ContDiff ℝ 2 harnackStep := by
  unfold harnackStep
  apply ContDiff.sub
  · exact harnack_positiveCube_contDiff.mul (by fun_prop)
  · exact (harnack_positiveCube_contDiff.comp (contDiff_id.sub contDiff_const)).mul (by fun_prop)

theorem harnack_step_eq_zero {q : ℝ} (hq : q≤0) : harnackStep q=0 := by
  simp [harnackStep,harnackPositiveCube,max_eq_right hq,max_eq_right (by linarith : q-1≤0)]

theorem harnack_step_eq_polynomial {q : ℝ} (hq : q ∈ Icc 0 1) :
    harnackStep q=10*q^3-15*q^4+6*q^5 := by
  rw [harnackStep]
  simp only [harnackPositiveCube,max_eq_left hq.1,max_eq_right (sub_nonpos.mpr hq.2),
    zero_pow (by decide : 3≠0),zero_mul,sub_zero]
  ring

theorem harnack_step_eq_one {q : ℝ} (hq : 1≤q) : harnackStep q=1 := by
  simp only [harnackStep,harnackPositiveCube,max_eq_left (by linarith : 0≤q),
    max_eq_left (sub_nonneg.mpr hq)]
  ring

theorem harnack_step_hasDerivAt (q : ℝ) : HasDerivAt harnackStep
    (3*(max q 0)^2*(10-15*q+6*q^2)+harnackPositiveCube q*(-15+12*q)-
      (3*(max (q-1) 0)^2*(10+15*(q-1)+6*(q-1)^2)+
        harnackPositiveCube (q-1)*(15+12*(q-1)))) q := by
  have hD1 : HasDerivAt (fun x : ℝ => 10-15*x+6*x^2) (-15+12*q) q := by
    convert! ((hasDerivAt_const q 10).sub ((hasDerivAt_id q).const_mul 15)).add
      (((hasDerivAt_id q).pow 2).const_mul 6) using 1
    simp only [id_eq]
    ring
  have hD2 : HasDerivAt (fun x : ℝ => 10+15*(x-1)+6*(x-1)^2) (15+12*(q-1)) q := by
    convert! ((hasDerivAt_const q 10).add (((hasDerivAt_id q).sub_const 1).const_mul 15)).add
      ((((hasDerivAt_id q).sub_const 1).pow 2).const_mul 6) using 1
    simp only [id_eq]
    ring
  have hShift : HasDerivAt (fun x : ℝ => harnackPositiveCube (x-1))
      (3*(max (q-1) 0)^2) q := by
    simpa only [Function.comp_def,id_eq,mul_one] using
      (harnack_positiveCube_hasDerivAt (q-1)).comp q ((hasDerivAt_id q).sub_const 1)
  exact ((harnack_positiveCube_hasDerivAt q).mul hD1).sub
    (hShift.mul hD2)

theorem harnack_step_deriv_eq_zero_of_nonpos {q : ℝ} (hq : q≤0) : deriv harnackStep q=0 := by
  rw [(harnack_step_hasDerivAt q).deriv]
  simp [harnackPositiveCube,max_eq_right hq,max_eq_right (by linarith : q-1≤0)]

theorem harnack_step_deriv_eq_zero_of_one_le {q : ℝ} (hq : 1≤q) : deriv harnackStep q=0 := by
  rw [(harnack_step_hasDerivAt q).deriv]
  simp only [harnackPositiveCube,max_eq_left (by linarith : 0≤q),max_eq_left (sub_nonneg.mpr hq)]
  ring

theorem harnack_step_deriv_eq_polynomial {q : ℝ} (hq : q ∈ Icc 0 1) :
    deriv harnackStep q=30*q^2*(1-q)^2 := by
  rw [(harnack_step_hasDerivAt q).deriv]
  simp only [harnackPositiveCube,max_eq_left hq.1,max_eq_right (sub_nonpos.mpr hq.2),
    zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),zero_mul]
  ring

theorem harnack_step_deriv_bounds (q : ℝ) : 0≤deriv harnackStep q ∧ deriv harnackStep q≤15/8 := by
  by_cases hq0 : q≤0
  · rw [harnack_step_deriv_eq_zero_of_nonpos hq0]
    norm_num
  by_cases hq1 : 1≤q
  · rw [harnack_step_deriv_eq_zero_of_one_le hq1]
    norm_num
  have hq : q ∈ Icc 0 1 := ⟨(not_le.mp hq0).le,(not_le.mp hq1).le⟩
  rw [harnack_step_deriv_eq_polynomial hq]
  constructor
  · positivity
  · have hprod : 0≤q*(1-q) := mul_nonneg hq.1 (sub_nonneg.mpr hq.2)
    have hprod1 : q*(1-q)≤1/4 := by nlinarith [sq_nonneg (q-1/2)]
    nlinarith [sq_nonneg (q*(1-q))]

theorem harnack_step_bounds (q : ℝ) : 0≤harnackStep q ∧ harnackStep q≤1 := by
  have hMono : Monotone harnackStep := monotone_of_deriv_nonneg
    (harnack_step_contDiff.differentiable (by norm_num)) (fun x => (harnack_step_deriv_bounds x).1)
  by_cases hq0 : q≤0
  · rw [harnack_step_eq_zero hq0]
    norm_num
  by_cases hq1 : 1≤q
  · rw [harnack_step_eq_one hq1]
    norm_num
  have h0 := hMono (not_le.mp hq0).le
  have h1 := hMono (not_le.mp hq1).le
  rw [harnack_step_eq_zero (le_refl 0)] at h0
  rw [harnack_step_eq_one (le_refl 1)] at h1
  exact ⟨h0,h1⟩

end Yau.LeafProofs.L05Aux
