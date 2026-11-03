import Yau.Proofs.F03DyadicPartition

/-! Genuine compact derivative support and global derivative constants for the fixed dyadic profile. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux

theorem dyadicProfile_deriv_zero_left {s : ℝ} (hs : s < 1) : deriv dyadicProfile s=0 := by
  have hEq : dyadicProfile =ᶠ[𝓝 s] (fun _ => (1:ℝ)) := by
    filter_upwards [eventually_lt_nhds hs] with r hr
    exact dyadicProfile_one hr.le
  rw [hEq.deriv_eq,deriv_const]

theorem dyadicProfile_deriv_zero_right {s : ℝ} (hs : 2 < s) : deriv dyadicProfile s=0 := by
  have hEq : dyadicProfile =ᶠ[𝓝 s] (fun _ => (0:ℝ)) := by
    filter_upwards [eventually_gt_nhds hs] with r hr
    exact dyadicProfile_zero hr.le
  rw [hEq.deriv_eq,deriv_const]

theorem dyadicProfile_deriv_tsupport : tsupport (deriv dyadicProfile) ⊆ Icc (1:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  refine ⟨le_of_not_gt (fun h => hs (dyadicProfile_deriv_zero_left h)),
    le_of_not_gt (fun h => hs (dyadicProfile_deriv_zero_right h))⟩

theorem dyadicProfile_derivative_bounds :
    ∃ B : ℝ,0 < B ∧ ∀ s : ℝ,|deriv dyadicProfile s| ≤ B ∧
      |deriv (deriv dyadicProfile) s| ≤ B := by
  have hc : HasCompactSupport (deriv dyadicProfile) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) dyadicProfile_deriv_tsupport
  have hd : ContDiff ℝ ∞ (deriv dyadicProfile) :=
    (contDiff_infty_iff_deriv.mp dyadicProfile_contDiff).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv dyadicProfile)) :=
    (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨C₁,hC₁⟩ := (hc.norm.isCompact_range hd.continuous.norm).bddAbove
  obtain ⟨C₂,hC₂⟩ := (hc.deriv.norm.isCompact_range hdd.continuous.norm).bddAbove
  refine ⟨1+|C₁|+|C₂|,by positivity,fun s => ?_⟩
  have h₁ := hC₁ (mem_range_self s)
  have h₂ := hC₂ (mem_range_self s)
  simp only [Real.norm_eq_abs] at h₁ h₂
  constructor <;> nlinarith [le_abs_self C₁,le_abs_self C₂,abs_nonneg C₁,abs_nonneg C₂]

theorem dyadicProfile_scaled_deriv (R s : ℝ) :
    deriv (fun z => dyadicProfile (z/R)) s=deriv dyadicProfile (s/R)/R := by
  have hD := (dyadicProfile_contDiff.differentiable (by simp) (s/R)).hasDerivAt.comp s
    ((hasDerivAt_id s).div_const R)
  simpa only [Function.comp_def,id_eq,mul_one_div] using hD.deriv

theorem dyadicProfile_scaled_secondDeriv (R s : ℝ) :
    deriv (deriv (fun z => dyadicProfile (z/R))) s=deriv (deriv dyadicProfile) (s/R)/R^2 := by
  have hd : Differentiable ℝ (deriv dyadicProfile) :=
    (contDiff_infty_iff_deriv.mp dyadicProfile_contDiff).2.differentiable (by simp)
  have hEq : deriv (fun z => dyadicProfile (z/R))=(fun z => deriv dyadicProfile (z/R)/R) :=
    funext (dyadicProfile_scaled_deriv R)
  rw [hEq]
  have hD := ((hd (s/R)).hasDerivAt.comp s ((hasDerivAt_id s).div_const R)).div_const R
  simpa only [Function.comp_def,id_eq,mul_one_div,div_div,← pow_two] using hD.deriv

end Yau.Proofs.F03Aux
