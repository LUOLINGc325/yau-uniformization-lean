import Yau.LeafProofs.L05ABPQuadraticPolynomial

noncomputable section

open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem joint_bilinear_split {n : ℕ}
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (hB : ∀ v w, B v w=B w v)
    (zeta : Space n) (tau : ℝ) :
    B (zeta,tau) (zeta,tau)=B (zeta,0) (zeta,0)+
      2*tau*B (zeta,0) (0,1)+B (0,1) (0,1)*tau^2 := by
  have he : (zeta,tau)=(zeta,0)+tau • ((0,1) : Point n) := by ext <;> simp
  rw [he]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [hB ((0,1) : Point n) (zeta,0)]
  ring

theorem joint_bilinear_mixed_young {n : ℕ} {eta : ℝ} (heta : 0<eta)
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (zeta : Space n) (tau : ℝ) :
    tau*B (zeta,0) (0,1) ≤ eta*‖zeta‖^2+‖B‖^2/(4*eta)*tau^2 := by
  have hop : |B (zeta,0) (0,1)|≤‖B‖*‖zeta‖ := by
    simpa only [Real.norm_eq_abs,Prod.norm_def,norm_zero,norm_one,max_eq_left (norm_nonneg zeta),
      max_eq_right (by norm_num : (0:ℝ)≤1),mul_one] using B.le_opNorm₂ (zeta,0) (0,1)
  have hmul : tau*B (zeta,0) (0,1)≤‖B‖*‖zeta‖*|tau| := by
    calc
      _ ≤ |tau*B (zeta,0) (0,1)| := le_abs_self _
      _ = |tau| * |B (zeta,0) (0,1)| := abs_mul _ _
      _ ≤ |tau| * (‖B‖*‖zeta‖) := mul_le_mul_of_nonneg_left hop (abs_nonneg _)
      _ = _ := by ring
  have hyoung : ‖B‖*‖zeta‖*|tau|≤eta*‖zeta‖^2+‖B‖^2/(4*eta)*tau^2 := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0<4*eta)).mp
    have hs := sq_nonneg (2*eta*‖zeta‖-‖B‖*|tau|)
    simp only [sub_sq,mul_pow,sq_abs] at hs
    have he : (eta*‖zeta‖^2+‖B‖^2/(4*eta)*tau^2)*(4*eta)=
        (4*eta^2*‖zeta‖^2+‖B‖^2*tau^2) := by field_simp
    rw [he]
    nlinarith
  exact hmul.trans hyoung

theorem quadratic_penalty_expand {n : ℕ} {delta : ℝ} (hdelta : 0<delta)
    (p zeta Y : Space n) :
    inner ℝ p zeta-‖zeta-Y+delta • p‖^2/(2*delta)=
      inner ℝ p Y-(delta/2)*‖p‖^2-‖zeta-Y‖^2/(2*delta) := by
  rw [norm_add_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_right,
    real_inner_comm p (zeta-Y),inner_sub_right]
  field_simp
  ring

theorem quadratic_spatial_domination {n : ℕ} {delta eta : ℝ}
    (hdelta : 0<delta) (heta : 0<eta) (hsmall : 8*delta*eta<1)
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hneg : ∀ v : Space n, 0≤-B (v,0) (v,0))
    (hlow : ∀ v : Space n, delta*(-B (v,0) (v,0))≤‖v‖^2)
    (zeta Y : Space n) :
    (1/2 : ℝ)*B (zeta,0) (zeta,0)+2*eta*‖zeta‖^2-‖zeta-Y‖^2/(2*delta) ≤
      ((1-8*delta*eta)/4)*B (Y,0) (Y,0)+4*eta*‖Y‖^2 := by
  let r := zeta-Y
  have hnorm : 0≤2*‖Y‖^2+2*‖r‖^2-‖zeta‖^2 := by
    have he : zeta=Y+r := by dsimp [r]; abel
    rw [he,norm_add_sq_real]
    have hs := sq_nonneg ‖Y-r‖
    rw [norm_sub_sq_real] at hs
    linarith
  have hp : 0≤2*(-B (zeta,0) (zeta,0))+2*(-B (r,0) (r,0))-(-B (Y,0) (Y,0)) := by
    have hs := hneg (zeta+r)
    have he : ((Y,0) : Point n)=(zeta,0)-(r,0) := by ext <;> simp [r]
    rw [he]
    change 0≤2*(-B (zeta,0) (zeta,0))+2*(-B (r,0) (r,0))-
      (-B ((zeta,0)-(r,0)) ((zeta,0)-(r,0)))
    have ha : ((zeta+r,0) : Point n)=(zeta,0)+(r,0) := by ext <;> simp
    rw [ha] at hs
    simp only [map_add,add_apply] at hs
    simp only [map_sub,sub_apply]
    linarith
  have h1 : 0≤((1-(1-8*delta*eta))/2)*(-B (zeta,0) (zeta,0)) :=
    mul_nonneg (by nlinarith [mul_pos hdelta heta]) (hneg zeta)
  have h2 : 0≤((1-8*delta*eta)/4)*
      (2*(-B (zeta,0) (zeta,0))+2*(-B (r,0) (r,0))-(-B (Y,0) (Y,0))) :=
    mul_nonneg (by linarith) hp
  have h3 : 0≤((1-8*delta*eta)/(2*delta))*(‖r‖^2-delta*(-B (r,0) (r,0))) :=
    mul_nonneg (div_nonneg (by linarith) (by positivity)) (sub_nonneg.mpr (hlow r))
  have h4 : 0≤2*eta*(2*‖Y‖^2+2*‖r‖^2-‖zeta‖^2) :=
    mul_nonneg (by positivity) hnorm
  have hcert : ((1-(1-8*delta*eta))/2)*(-B (zeta,0) (zeta,0))+
      ((1-8*delta*eta)/4)*(2*(-B (zeta,0) (zeta,0))+2*(-B (r,0) (r,0))-(-B (Y,0) (Y,0)))+
      ((1-8*delta*eta)/(2*delta))*(‖r‖^2-delta*(-B (r,0) (r,0)))+
      2*eta*(2*‖Y‖^2+2*‖r‖^2-‖zeta‖^2)=
      ((1-8*delta*eta)/4)*B (Y,0) (Y,0)+4*eta*‖Y‖^2-
      ((1/2 : ℝ)*B (zeta,0) (zeta,0)+2*eta*‖zeta‖^2-‖r‖^2/(2*delta)) := by
    field_simp
    ring
  change _-‖r‖^2/(2*delta)≤_
  linarith

theorem quadratic_touch_domination {n : ℕ} {delta eta : ℝ}
    (hdelta : 0<delta) (heta : 0<eta) (hsmall : 8*delta*eta<1)
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (hB : ∀ v w, B v w=B w v)
    (hneg : ∀ v : Space n, 0≤-B (v,0) (v,0))
    (hlow : ∀ v : Space n, delta*(-B (v,0) (v,0))≤‖v‖^2)
    (c a0 : ℝ) (p zeta Y : Space n) (tau : ℝ) :
    c+inner ℝ p zeta+a0*tau+(1/2 : ℝ)*B (zeta,tau) (zeta,tau)+
        eta*(‖zeta‖^2+tau^2)-‖zeta-Y+delta • p‖^2/(2*delta) ≤
      c-(delta/2)*‖p‖^2+inner ℝ p Y+a0*tau+
        ((1-8*delta*eta)/4)*B (Y,0) (Y,0)+4*eta*‖Y‖^2+
        quadraticLiftTimeCoeff eta B*tau^2 := by
  have hm := joint_bilinear_mixed_young heta B zeta tau
  have hb : B ((0,1) : Point n) (0,1)≤‖B‖ := by
    have hh := B.le_opNorm₂ ((0,1) : Point n) (0,1)
    simp only [Prod.norm_def,norm_zero,norm_one,max_eq_right (by norm_num : (0:ℝ)≤1),
      mul_one,Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans hh
  have hbt := mul_le_mul_of_nonneg_right hb (sq_nonneg tau)
  have hp := quadratic_penalty_expand hdelta p zeta Y
  have hs := quadratic_spatial_domination hdelta heta hsmall B hneg hlow zeta Y
  rw [joint_bilinear_split B hB zeta tau]
  dsimp only [quadraticLiftTimeCoeff]
  nlinarith

end Yau.LeafProofs.L05Aux
