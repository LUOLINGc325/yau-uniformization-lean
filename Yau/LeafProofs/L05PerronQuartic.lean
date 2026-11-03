import Yau.LeafProofs.L05PerronClassical

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def perronQuartic {n : ℕ} (p q : Point n) : ℝ := qnorm2 (q-p)^2

theorem perronQuartic_smooth {n : ℕ} (p : Point n) : ContDiff ℝ ∞ (perronQuartic p) :=
  ((qnorm2_smooth n).comp (contDiff_id.sub contDiff_const)).pow 2

theorem perronQuartic_center {n : ℕ} (p : Point n) : perronQuartic p p=0 := by
  simp [perronQuartic,qnorm2]

theorem perronQuartic_distance {n : ℕ} (p q : Point n) : dist q p^4≤perronQuartic p q := by
  have hh := norm_sq_le_qnorm2 (q-p)
  calc
    _ = (‖q-p‖^2)^2 := by rw [dist_eq_norm]; ring
    _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hh 2

theorem perron_quad_hasFDerivAt {n : ℕ} (p q : Point n) :
    HasFDerivAt (fun y : Point n => qnorm2 (y-p)) ((2:ℝ) • jointInnerBilin n (q-p)) q := by
  have he : peanoPolynomial 0 p 0 0 1=(fun y : Point n => qnorm2 (y-p)) := by
    funext y
    simp [peanoPolynomial]
  rw [←he]
  simpa only [zero_add,zero_apply,mul_one,add_zero] using
    peanoPolynomial_hasFDerivAt 0 p 0 0 (by simp) 1 q

theorem perronQuartic_hasFDerivAt {n : ℕ} (p q : Point n) :
    HasFDerivAt (perronQuartic p)
      ((2*qnorm2 (q-p)) • ((2:ℝ) • jointInnerBilin n (q-p))) q := by
  convert! (perron_quad_hasFDerivAt p q).pow 2 using 1 <;> simp [perronQuartic,nsmul_eq_mul]

theorem perronQuartic_secondFDeriv_zero {n : ℕ} (p : Point n) :
    fderiv ℝ (fderiv ℝ (perronQuartic p)) p=0 := by
  have hf : fderiv ℝ (perronQuartic p)=fun q =>
      (2*qnorm2 (q-p)) • ((2:ℝ) • jointInnerBilin n (q-p)) := by
    funext q
    exact (perronQuartic_hasFDerivAt p q).fderiv
  have hs : HasFDerivAt (fun q : Point n => jointInnerBilin n (q-p)) (jointInnerBilin n) p := by
    convert! (jointInnerBilin n).hasFDerivAt.comp p ((hasFDerivAt_id p).sub_const p) using 1
  have hq : HasFDerivAt (fun q : Point n => qnorm2 (q-p)) (0 : Point n →L[ℝ] ℝ) p := by
    simpa using perron_quad_hasFDerivAt p p
  have hm := (hq.const_mul 2).smul (hs.const_smul (2:ℝ))
  have hm' : HasFDerivAt (fun q : Point n =>
      (2*qnorm2 (q-p)) • ((2:ℝ) • jointInnerBilin n (q-p)))
      (0 : Point n →L[ℝ] Point n →L[ℝ] ℝ) p := by
    convert! hm using 1 <;> simp [qnorm2,Pi.smul_apply]
  rw [hf]
  exact hm'.fderiv

theorem perronQuartic_timeD_zero {n : ℕ} (p : Point n) :
    timeD Set.univ (perronQuartic p) p=0 := by
  have hd := perronQuartic_hasFDerivAt p p
  rw [timeD_univ_eq_joint hd.differentiableAt,hd.fderiv]
  simp

theorem perronQuartic_hessian_zero {n : ℕ} (p : Point n) : hessian (perronQuartic p) p=0 := by
  rw [jet_hessian_eq_joint_at ((perronQuartic_smooth p).contDiffAt.of_le (by simp)),
    perronQuartic_secondFDeriv_zero]
  exact (selfAdjointPart ℝ).map_zero

theorem perron_timeD_add {n : ℕ} {phi s : Point n → ℝ} {p : Point n}
    (hp : ContDiffAt ℝ 2 phi p) (hs : ContDiffAt ℝ 2 s p) :
    timeD Set.univ (fun q => phi q+s q) p=timeD Set.univ phi p+timeD Set.univ s p := by
  have hpd := hp.differentiableAt (by norm_num)
  have hsd := hs.differentiableAt (by norm_num)
  change timeD Set.univ (phi+s) p=timeD Set.univ phi p+timeD Set.univ s p
  rw [timeD_univ_eq_joint (hpd.add hsd),timeD_univ_eq_joint hpd,timeD_univ_eq_joint hsd,
    fderiv_add hpd hsd]
  rfl

theorem perron_hessian_neg {n : ℕ} {s : Point n → ℝ} {p : Point n}
    (hs : ContDiffAt ℝ 2 s p) : hessian (fun q => -s q) p= -hessian s p := by
  have hh := perron_hessian_sub (phi := fun _ => 0) contDiffAt_const hs
  rw [perron_hessian_const] at hh
  simpa only [zero_sub] using hh

theorem perron_hessian_add {n : ℕ} {phi s : Point n → ℝ} {p : Point n}
    (hp : ContDiffAt ℝ 2 phi p) (hs : ContDiffAt ℝ 2 s p) :
    hessian (fun q => phi q+s q) p=hessian phi p+hessian s p := by
  have hh := perron_hessian_sub hp hs.neg
  rw [perron_hessian_neg hs] at hh
  simpa only [sub_neg_eq_add] using hh

end Yau.LeafProofs.L05Aux
