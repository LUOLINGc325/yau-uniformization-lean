import Yau.LeafProofs.L16EnergyMollification

open MeasureTheory Filter
open scoped Topology ContDiff Convolution Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem smooth_divergence_energy_identity {n : ℕ}
    {w ψ R : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hw : ContDiff ℝ ∞ w) (hP : ∀ i, ContDiff ℝ ∞ (fun p => P p i))
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hPDE : ∀ p, fderiv ℝ w p (0,1) =
      (∑ i, fderiv ℝ (fun q => P q i) p (Yau.realVec i,0))+R p) :
    (∫ p, -(1/2 : ℝ)*fderiv ℝ ψ p (0,1)*(w p)^2+
      (∑ i, P p i*(ψ p*fderiv ℝ w p (Yau.realVec i,0)+
        w p*fderiv ℝ ψ p (Yau.realVec i,0)))-R p*ψ p*w p) = 0 := by
  let T : Point n → ℝ := fun p => ψ p*(w p)^2
  let S : Yau.RIdx n → Point n → ℝ := fun i p => ψ p*w p*P p i
  have hT : ContDiff ℝ ∞ T := hψ.mul (hw.pow 2)
  have hcT : HasCompactSupport T := hcψ.mul_right
  have hS (i : Yau.RIdx n) : ContDiff ℝ ∞ (S i) := (hψ.mul hw).mul (hP i)
  have hcS (i : Yau.RIdx n) : HasCompactSupport (S i) := hcψ.mul_right.mul_right
  have hDT : Integrable (fun p => fderiv ℝ T p (0,1)) volume :=
    ((hT.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.integrable_of_hasCompactSupport
      (hcT.fderiv_apply ℝ (0,1))
  have hDS (i : Yau.RIdx n) : Integrable (fun p => fderiv ℝ (S i) p (Yau.realVec i,0)) volume :=
    (((hS i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.integrable_of_hasCompactSupport
      ((hcS i).fderiv_apply ℝ (Yau.realVec i,0))
  have hTzero := Yau.LeafProofs.L03.integral_compact_fderiv_eq_zero volume (hT.of_le (by simp)) hcT (0,1)
  have hSzero (i : Yau.RIdx n) := Yau.LeafProofs.L03.integral_compact_fderiv_eq_zero
    volume ((hS i).of_le (by simp)) (hcS i) (Yau.realVec i,0)
  have hAlgebra (p : Point n) :
      -(1/2 : ℝ)*fderiv ℝ ψ p (0,1)*(w p)^2+
        (∑ i, P p i*(ψ p*fderiv ℝ w p (Yau.realVec i,0)+
          w p*fderiv ℝ ψ p (Yau.realVec i,0)))-R p*ψ p*w p =
      -(1/2 : ℝ)*fderiv ℝ T p (0,1)+∑ i, fderiv ℝ (S i) p (Yau.realVec i,0) := by
    have hwd := hw.differentiable (by simp) p
    have hψd := hψ.differentiable (by simp) p
    have hw2d : DifferentiableAt ℝ (fun q => (w q)^2) p := hwd.pow 2
    have hψwd : DifferentiableAt ℝ (fun q => ψ q*w q) p := hψd.mul hwd
    dsimp only [T,S]
    rw [fderiv_fun_mul hψd hw2d]
    simp only [fderiv_fun_pow 2 hwd,
      fderiv_fun_mul hψwd ((hP _).differentiable (by simp) p),fderiv_fun_mul hψd hwd,
      add_apply,smul_apply,smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat,show (2 : ℕ)-1=1 by rfl,pow_one]
    rw [hPDE]
    simp only [mul_add,Finset.sum_add_distrib]
    ring_nf
    simp only [Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]
    ring
  simp_rw [hAlgebra]
  rw [integral_add (hDT.const_mul _) (integrable_finsetSum _ (fun i _ => hDS i)),
    integral_const_mul,integral_finsetSum Finset.univ (fun i _ => hDS i),hTzero]
  simp only [hSzero,Finset.sum_const_zero,mul_zero,zero_add]

end Yau.LeafProofs.L16Aux
