import Yau.LeafProofs.L05AutonomousLocalMaximum
import Yau.LeafProofs.L05AutonomousHarnackScaling

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The genuine local maximum estimate transports to every actual backward cylinder and its top center. -/
theorem auto_local_maximum_center (n : ℕ) (hn : 0< n) (ell L : ℝ) (hell : 0< ell) (hL : ell≤ L)
    (p : ℝ) (hp : 0< p) : ∃ C : ℝ, 0< C ∧
    ∀ (c : Space n) (R T : ℝ), 0< R → ∀ w : Point n → ℝ,
      ContinuousOn w (autoClosed c R T) →
      viscositySub (autoOpen c R T) (fun H _ => pucciPlus ell L H) (fun _ => 0) w →
      max (w (c,T)) 0≤ C*((∫ q in autoOpen c R T, (max (w q) 0)^p)/R^(2*n+2))^(1/p) := by
  obtain ⟨C,hC,hMax⟩ := auto_local_maximum n hn ell L hell hL p hp
  refine ⟨C,hC,?_⟩
  intro c R T hR w hw hsub
  have hsq : R^2≠0 := (sq_pos_of_pos hR).ne'
  have hpull := harnack_sub_affine_pullback hell.le hL hsub c hR (sq_pos_of_pos hR)
    (h := 1) zero_lt_one (autoScale_open_maps c hR T)
  have hP : viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) (fun _ => 0)
      (fun z => w (autoScale c R T z)) := by
    simpa only [autoScale,div_self hsq,one_mul,div_one,mul_zero] using hpull
  have hcont : Continuous (autoScale c R T) := (harnack_affine_contDiff c R (T-R^2) (R^2)).continuous
  have hbound := hMax (fun z => w (autoScale c R T z))
    (hw.comp hcont.continuousOn (autoScale_closed_maps c hR T)) hP
    ((0 : Space n),0) (by constructor <;> norm_num [backward,Metric.mem_ball,dist_self,Set.mem_Ioc])
  have hInt : (∫ z in unitOpen n, (max (w (autoScale c R T z)) 0)^p)=
      (∫ q in autoOpen c R T, (max (w q) 0)^p)/R^(2*n+2) := by
    have hh := harnack_integral_affine_open c (a := T-R^2) hR (sq_pos_of_pos hR)
      (fun q => (max (w q) 0)^p)
    have hset : harnackOpen c R (T-R^2) (R^2)=autoOpen c R T := by
      simp only [harnackOpen,autoOpen,sub_add_cancel]
    rw [hset,harnackAffineJacobian,← pow_add] at hh
    simpa only [autoScale,div_eq_mul_inv,mul_comm] using hh
  rw [hInt] at hbound
  simpa only [autoScale_apply,zero_smul,smul_zero,add_zero,mul_zero] using hbound

end Yau.LeafProofs.L05AutonomousAux
