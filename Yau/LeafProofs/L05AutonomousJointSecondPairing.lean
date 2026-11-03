import Yau.LeafProofs.L05AutonomousSecondLimit

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

local instance autoJointSecondPairing_pointHaar (n : ℕ) :
    (volume : Measure (Point n)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

theorem autoSecond_point_translation {n : ℕ} (f : Point n → ℝ) (e : Space n) (h : ℝ) (p : Point n) :
    autoSecond f e h p=(f (p+(h • e,0))+f (p-(h • e,0))-2*f p)/h^2 := by
  rcases p with ⟨x,t⟩
  simp only [autoSecond,Prod.mk_add_mk,Prod.mk_sub_mk,add_zero,sub_zero]

theorem auto_joint_second_pairing_integrable {n : ℕ} {f phi : Point n → ℝ}
    (hf : Continuous f) (hphi : Continuous phi) (hcphi : HasCompactSupport phi)
    (e : Space n) (h : ℝ) : Integrable (fun p => phi p*autoSecond f e h p) :=
  (hphi.mul (autoSecond_continuous hf e h)).integrable_of_hasCompactSupport hcphi.mul_right

theorem auto_joint_second_pairing_expand {n : ℕ} {f phi : Point n → ℝ}
    (hf : Continuous f) (hphi : Continuous phi) (hcphi : HasCompactSupport phi)
    (e : Space n) (h : ℝ) :
    (∫ p, phi p*autoSecond f e h p)=
      ((∫ p, phi p*f (p+(h • e,0)))+(∫ p, phi p*f (p-(h • e,0)))-2*(∫ p, phi p*f p))/h^2 := by
  let v : Point n := (h • e,0)
  have hPlus : Integrable (fun p => phi p*f (p+v)) :=
    (hphi.mul (hf.comp (continuous_id.add_const _))).integrable_of_hasCompactSupport hcphi.mul_right
  have hMinus : Integrable (fun p => phi p*f (p-v)) :=
    (hphi.mul (hf.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport hcphi.mul_right
  have hBase : Integrable (fun p => phi p*f p) :=
    (hphi.mul hf).integrable_of_hasCompactSupport hcphi.mul_right
  have hFun : (fun p => phi p*autoSecond f e h p)=
      (fun p => ((phi p*f (p+v)+phi p*f (p-v))-2*(phi p*f p))/h^2) := by
    funext p
    rw [autoSecond_point_translation]
    dsimp only [v]
    ring
  have hSum : Integrable (fun p => phi p*f (p+v)+phi p*f (p-v)) := hPlus.add hMinus
  rw [hFun,integral_div,integral_sub hSum (hBase.const_mul 2),integral_add hPlus hMinus,integral_const_mul]

/-- Actual product-volume Haar translation gives the full space-time distribution pairing.
No weak Hessian, PDE, or differentiability of the original source is an input. -/
theorem auto_joint_second_pairing {n : ℕ} {f phi : Point n → ℝ}
    (hf : Continuous f) (hphi : Continuous phi) (hcf : HasCompactSupport f) (hcphi : HasCompactSupport phi)
    (e : Space n) (h : ℝ) :
    Integrable (fun p => phi p*autoSecond f e h p) ∧
      Integrable (fun p => f p*autoSecond phi e h p) ∧
      (∫ p, phi p*autoSecond f e h p)=(∫ p, f p*autoSecond phi e h p) := by
  refine ⟨auto_joint_second_pairing_integrable hf hphi hcphi e h,
    auto_joint_second_pairing_integrable hphi hf hcf e h,?_⟩
  let v : Point n := (h • e,0)
  have hPlus : (∫ p, phi p*f (p+v))=∫ p, f p*phi (p-v) := by
    have ht := integral_add_right_eq_self (μ := volume) (fun p : Point n => f p*phi (p-v)) v
    simpa only [add_sub_cancel_right,mul_comm] using ht
  have hMinus : (∫ p, phi p*f (p-v))=∫ p, f p*phi (p+v) := by
    have ht := integral_add_right_eq_self (μ := volume) (fun p : Point n => f p*phi (p+v)) (-v)
    simpa only [neg_add_cancel_right,sub_eq_add_neg,mul_comm] using ht
  have hBase : (∫ p, phi p*f p)=∫ p, f p*phi p := by
    apply integral_congr_ae
    exact ae_of_all volume fun p => mul_comm _ _
  rw [auto_joint_second_pairing_expand hf hphi hcphi,auto_joint_second_pairing_expand hphi hf hcf,hPlus,hMinus,hBase]
  ring

end Yau.LeafProofs.L05AutonomousAux
