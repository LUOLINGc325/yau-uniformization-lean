import Yau.LeafProofs.L05PucciHarnackBumpJets
import Yau.LeafProofs.L05PucciHarnackTransport

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackBump {n : ℕ} (chi s : ℝ → ℝ) (c : ℝ → Space n) (b shift : ℝ) (z : Point n) : ℝ :=
  chi z.2*Real.exp (-b*(z.2+shift))*harnackPositiveCube (s z.2-‖z.1-c z.2‖^2)

theorem harnack_bump_contDiff {n : ℕ} {chi s : ℝ → ℝ} {c : ℝ → Space n}
    (hchi : ContDiff ℝ 2 chi) (hs : ContDiff ℝ 2 s) (hc : ContDiff ℝ 2 c) (b shift : ℝ) :
    ContDiff ℝ 2 (harnackBump chi s c b shift) := by
  have hq : ContDiff ℝ 2 (fun z : Point n => s z.2-‖z.1-c z.2‖^2) :=
    (hs.comp contDiff_snd).sub ((contDiff_fst.sub (hc.comp contDiff_snd)).norm_sq ℝ)
  have hK : ContDiff ℝ 2 (fun z : Point n => chi z.2*Real.exp (-b*(z.2+shift))) := by fun_prop
  exact hK.mul (harnack_positiveCube_contDiff.comp hq)

theorem harnack_bump_timeD {n : ℕ} {chi s : ℝ → ℝ} {c : ℝ → Space n}
    (hchi : ContDiff ℝ 2 chi) (hs : ContDiff ℝ 2 s) (hc : ContDiff ℝ 2 c)
    (b shift : ℝ) (p : Point n) :
    timeD univ (harnackBump chi s c b shift) p=
      deriv chi p.2*Real.exp (-b*(p.2+shift))*harnackPositiveCube (s p.2-‖p.1-c p.2‖^2)+
      chi p.2*Real.exp (-b*(p.2+shift))*
        (3*deriv s p.2*(max (s p.2-‖p.1-c p.2‖^2) 0)^2+
          6*(max (s p.2-‖p.1-c p.2‖^2) 0)^2*inner ℝ (p.1-c p.2) (deriv c p.2)-
          b*harnackPositiveCube (s p.2-‖p.1-c p.2‖^2)) := by
  have hcD := (hc.differentiable (by norm_num) p.2).hasDerivAt
  have hsD := (hs.differentiable (by norm_num) p.2).hasDerivAt
  have hchiD := (hchi.differentiable (by norm_num) p.2).hasDerivAt
  have hY : HasDerivAt (fun t => p.1-c t) (-deriv c p.2) p.2 := by
    convert! (hasDerivAt_const p.2 p.1).sub hcD using 1
    simp only [zero_sub]
  have hQ : HasDerivAt (fun t => s t-‖p.1-c t‖^2)
      (deriv s p.2+2*inner ℝ (p.1-c p.2) (deriv c p.2)) p.2 := by
    convert! hsD.sub hY.norm_sq using 1
    rw [inner_neg_right]
    ring
  have hExp : HasDerivAt (fun t => Real.exp (-b*(t+shift)))
      ((-b)*Real.exp (-b*(p.2+shift))) p.2 := by
    convert! ((((hasDerivAt_id p.2).add_const shift).const_mul (-b)).exp) using 1
    simp only [id_eq]
    ring
  have hP := (harnack_positiveCube_hasDerivAt (s p.2-‖p.1-c p.2‖^2)).comp p.2 hQ
  have hD := (hchiD.mul hExp).mul hP
  have hDer : HasDerivAt (fun t => harnackBump chi s c b shift (p.1,t))
      (deriv chi p.2*Real.exp (-b*(p.2+shift))*harnackPositiveCube (s p.2-‖p.1-c p.2‖^2)+
      chi p.2*Real.exp (-b*(p.2+shift))*
        (3*deriv s p.2*(max (s p.2-‖p.1-c p.2‖^2) 0)^2+
          6*(max (s p.2-‖p.1-c p.2‖^2) 0)^2*inner ℝ (p.1-c p.2) (deriv c p.2)-
          b*harnackPositiveCube (s p.2-‖p.1-c p.2‖^2))) p.2 := by
    convert! hD using 1
    simp only [Function.comp_def,Pi.mul_apply]
    ring
  simpa only [timeD,Set.mem_univ,Set.ofPred_true,derivWithin_univ] using hDer.deriv

theorem harnack_bump_hessian {n : ℕ} {chi s : ℝ → ℝ} {c : ℝ → Space n}
    (b shift : ℝ) (p : Point n) :
    (hessian (harnackBump chi s c b shift) p : Mat n)=
      (chi p.2*Real.exp (-b*(p.2+shift))) •
        ((24*max (s p.2-‖p.1-c p.2‖^2) 0) • harnackRankOne (p.1-c p.2)-
          (6*(max (s p.2-‖p.1-c p.2‖^2) 0)^2) • (1 : Mat n)) := by
  have hRadial : ContDiff ℝ 2 (fun z : Point n => harnackPositiveCube (s p.2-‖z.1-c p.2‖^2)) :=
    harnack_positiveCube_contDiff.comp
      (contDiff_const.sub ((contDiff_fst.sub contDiff_const).norm_sq ℝ))
  change (hessian (fun z : Point n => (chi p.2*Real.exp (-b*(p.2+shift)))*
    harnackPositiveCube (s p.2-‖z.1-c p.2‖^2)) p : Mat n)=_
  rw [harnack_hessian_const_mul hRadial.contDiffAt,selfAdjoint.val_smul,harnack_radial_cube_hessian]

theorem harnack_bump_jets_zero_of_level_nonpos {n : ℕ} {chi s : ℝ → ℝ} {c : ℝ → Space n}
    (hchi : ContDiff ℝ 2 chi) (hs : ContDiff ℝ 2 s) (hc : ContDiff ℝ 2 c)
    (b shift : ℝ) (p : Point n) (hq : s p.2-‖p.1-c p.2‖^2≤0) :
    harnackBump chi s c b shift p=0 ∧ timeD univ (harnackBump chi s c b shift) p=0 ∧
      hessian (harnackBump chi s c b shift) p=0 := by
  have hP : harnackPositiveCube (s p.2-‖p.1-c p.2‖^2)=0 := by
    simp only [harnackPositiveCube,max_eq_right hq,zero_pow (by decide : 3≠0)]
  refine ⟨by simp only [harnackBump,hP,mul_zero],?_,?_⟩
  · rw [harnack_bump_timeD hchi hs hc]
    simp only [hP,max_eq_right hq,zero_pow (by decide : 2≠0),mul_zero,zero_mul,zero_add,sub_zero]
  · apply Subtype.ext
    rw [harnack_bump_hessian]
    simp only [max_eq_right hq,zero_pow (by decide : 2≠0),mul_zero,zero_smul,sub_zero,smul_zero,
      AddSubgroup.coe_zero]

end Yau.LeafProofs.L05Aux
