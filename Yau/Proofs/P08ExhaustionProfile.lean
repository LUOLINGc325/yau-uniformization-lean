import Yau.LeafProofs.L18
import Mathlib.Analysis.Calculus.Deriv.Support

/-! A fixed scalar bump and a uniform bound on its second derivative. The
first derivative is bounded by a constant times its nonnegative argument. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.P08Aux

/-- The same fixed profile is used at every exhaustion scale. -/
def exhaustionProfile : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem exhaustionProfile_one {s : ℝ} (hs : |s| ≤ 1) : exhaustionProfile s = 1 := by
  apply exhaustionProfile.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, exhaustionProfile] using hs

theorem exhaustionProfile_zero {s : ℝ} (hs : 2 ≤ |s|) : exhaustionProfile s = 0 := by
  apply exhaustionProfile.zero_of_le_dist
  simpa only [dist_zero_right, Real.norm_eq_abs, exhaustionProfile] using hs

/-- The scale-independent second derivative bound also controls the first
one near zero, so no annular derivative-support premise is needed. -/
theorem exists_exhaustionProfile_derivative_bound :
    ∃ C : ℝ, 0 < C ∧ (∀ s : ℝ, |deriv (deriv (exhaustionProfile : ℝ → ℝ)) s| ≤ C) ∧
      ∀ s : ℝ, 0 ≤ s → |deriv (exhaustionProfile : ℝ → ℝ) s| ≤ C * s := by
  have hd : ContDiff ℝ ∞ (deriv (exhaustionProfile : ℝ → ℝ)) :=
    (contDiff_infty_iff_deriv.mp exhaustionProfile.contDiff).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv (exhaustionProfile : ℝ → ℝ))) :=
    (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨B, hB⟩ := exhaustionProfile.hasCompactSupport.deriv.deriv.exists_bound_of_continuous
    hdd.continuous
  let C := max B 0 + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hbound (s : ℝ) : |deriv (deriv (exhaustionProfile : ℝ → ℝ)) s| ≤ C := by
    exact (show |deriv (deriv (exhaustionProfile : ℝ → ℝ)) s| ≤ B from hB s).trans
      (by dsimp only [C]; linarith [le_max_left B 0])
  refine ⟨C, hC, hbound, ?_⟩
  have hz : deriv (exhaustionProfile : ℝ → ℝ) 0 = 0 := by
    rw [exhaustionProfile.eventuallyEq_one.deriv_eq]
    simp
  intro s hs
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℝ) (s := Set.univ) (f := deriv (exhaustionProfile : ℝ → ℝ))
    (fun t _ => hd.differentiable (by simp) t)
    (fun t _ => show ‖deriv (deriv (exhaustionProfile : ℝ → ℝ)) t‖ ≤ C from hbound t)
    (convex_univ) (Set.mem_univ (0 : ℝ)) (Set.mem_univ s)
  simpa only [hz, sub_zero, Real.norm_eq_abs, abs_of_nonneg hs] using h

end Yau.NodeProofs.P08Aux
