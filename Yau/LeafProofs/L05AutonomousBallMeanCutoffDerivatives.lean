import Yau.LeafProofs.L05AutonomousBallMeanCutoff
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.Deriv.Shift

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux

theorem auto_green_bump_deriv_contDiff : ContDiff ℝ ∞ (deriv (autoGreenBump : ℝ → ℝ)) :=
  (contDiff_infty_iff_deriv.mp autoGreenBump.contDiff).2

theorem auto_green_bump_second_contDiff : ContDiff ℝ ∞ (deriv (deriv (autoGreenBump : ℝ → ℝ))) :=
  (contDiff_infty_iff_deriv.mp auto_green_bump_deriv_contDiff).2

theorem auto_green_bump_deriv_bounds : ∃ B : ℝ, 0 < B ∧ ∀ s : ℝ,
    |deriv (autoGreenBump : ℝ → ℝ) s| ≤ B ∧ |deriv (deriv (autoGreenBump : ℝ → ℝ)) s| ≤ B := by
  obtain ⟨B1,hB1⟩ := autoGreenBump.hasCompactSupport.deriv.exists_bound_of_continuous
    auto_green_bump_deriv_contDiff.continuous
  obtain ⟨B2,hB2⟩ := autoGreenBump.hasCompactSupport.deriv.deriv.exists_bound_of_continuous
    auto_green_bump_second_contDiff.continuous
  refine ⟨max 1 (max B1 B2),lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro s
  exact ⟨(show |deriv (autoGreenBump : ℝ → ℝ) s| ≤ B1 by simpa only [Real.norm_eq_abs] using hB1 s).trans
    ((le_max_left B1 B2).trans (le_max_right 1 _)),
    (show |deriv (deriv (autoGreenBump : ℝ → ℝ)) s| ≤ B2 by simpa only [Real.norm_eq_abs] using hB2 s).trans
    ((le_max_right B1 B2).trans (le_max_right 1 _))⟩

theorem auto_green_inner_hasDerivAt (eta s : ℝ) :
    HasDerivAt (autoGreenInner eta) (-(deriv (autoGreenBump : ℝ → ℝ) (s/eta))/eta) s := by
  have hb : HasDerivAt (autoGreenBump : ℝ → ℝ) (deriv (autoGreenBump : ℝ → ℝ) (s/eta)) (s/eta) :=
    (contDiff_infty_iff_deriv.mp (autoGreenBump.contDiff : ContDiff ℝ ∞ (autoGreenBump : ℝ → ℝ))).1.differentiableAt.hasDerivAt
  convert! (hb.comp s ((hasDerivAt_id s).div_const eta)).const_sub 1 using 1
  simp only [autoGreenInner,id_eq,div_eq_mul_inv]
  ring

theorem auto_green_inner_deriv (eta s : ℝ) :
    deriv (autoGreenInner eta) s=-(deriv (autoGreenBump : ℝ → ℝ) (s/eta))/eta :=
  (auto_green_inner_hasDerivAt eta s).deriv

theorem auto_green_inner_second (eta s : ℝ) :
    deriv (deriv (autoGreenInner eta)) s=-(deriv (deriv (autoGreenBump : ℝ → ℝ)) (s/eta))/eta^2 := by
  have hEq : deriv (autoGreenInner eta)=(fun t : ℝ => -(deriv (autoGreenBump : ℝ → ℝ) (t/eta))/eta) :=
    funext (auto_green_inner_deriv eta)
  rw [hEq]
  have hb : HasDerivAt (deriv (autoGreenBump : ℝ → ℝ))
      (deriv (deriv (autoGreenBump : ℝ → ℝ)) (s/eta)) (s/eta) :=
    (contDiff_infty_iff_deriv.mp auto_green_bump_deriv_contDiff).1.differentiableAt.hasDerivAt
  have h := ((hb.comp s ((hasDerivAt_id s).div_const eta)).neg.div_const eta).deriv
  convert! h using 1
  simp only [id_eq,div_eq_mul_inv,pow_two]
  ring

theorem auto_green_inner_deriv_bounds : ∃ B : ℝ, 0 < B ∧ ∀ eta : ℝ, 0 < eta → ∀ s : ℝ,
    |deriv (autoGreenInner eta) s| ≤ B/eta ∧ |deriv (deriv (autoGreenInner eta)) s| ≤ B/eta^2 := by
  obtain ⟨B,hB,hBound⟩ := auto_green_bump_deriv_bounds
  refine ⟨B,hB,?_⟩
  intro eta heta s
  rw [auto_green_inner_deriv,auto_green_inner_second]
  simp only [abs_div,abs_neg,abs_of_pos heta,abs_of_nonneg (sq_nonneg eta)]
  exact ⟨div_le_div_of_nonneg_right (hBound (s/eta)).1 heta.le,
    div_le_div_of_nonneg_right (hBound (s/eta)).2 (sq_nonneg eta)⟩

theorem auto_green_outer_eventuallyEq_inner {r eta s : ℝ} (hs : s < r) :
    autoGreenOuter r eta=ᶠ[𝓝 s] (fun t => autoGreenInner eta (r-t)) := by
  filter_upwards [isOpen_Iio.mem_nhds hs] with t ht
  exact ite_eq_left ht

theorem auto_green_outer_eventuallyEq_zero {r eta s : ℝ} (heta : 0 < eta) (hs : r ≤ s) :
    autoGreenOuter r eta=ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
  filter_upwards [isOpen_Ioi.mem_nhds (show r-eta < s by linarith)] with t ht
  exact auto_green_outer_zero heta ht.le

theorem auto_green_outer_deriv {eta : ℝ} (heta : 0 < eta) (r s : ℝ) :
    deriv (autoGreenOuter r eta) s=if s < r then -deriv (autoGreenInner eta) (r-s) else 0 := by
  by_cases hs : s < r
  · rw [ite_eq_left hs,(auto_green_outer_eventuallyEq_inner hs).deriv_eq,deriv_comp_const_sub]
  · rw [ite_eq_right hs,(auto_green_outer_eventuallyEq_zero heta (le_of_not_gt hs)).deriv_eq]
    simp only [deriv_const',deriv_const]

theorem auto_green_outer_second {eta : ℝ} (heta : 0 < eta) (r s : ℝ) :
    deriv (deriv (autoGreenOuter r eta)) s=if s < r then deriv (deriv (autoGreenInner eta)) (r-s) else 0 := by
  by_cases hs : s < r
  · rw [ite_eq_left hs,(auto_green_outer_eventuallyEq_inner hs).deriv.deriv_eq]
    have hEq : deriv (fun t : ℝ => autoGreenInner eta (r-t))=
        (fun t : ℝ => -deriv (autoGreenInner eta) (r-t)) :=
      funext fun t => deriv_comp_const_sub (autoGreenInner eta) r t
    rw [hEq]
    change deriv (fun t : ℝ => -deriv (autoGreenInner eta) (r-t)) s=deriv (deriv (autoGreenInner eta)) (r-s)
    have hD : HasDerivAt (deriv (autoGreenInner eta)) (deriv (deriv (autoGreenInner eta)) (r-s)) (r-s) :=
      (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp (auto_green_inner_contDiff eta)).2).1.differentiableAt.hasDerivAt
    have h := ((hD.comp_const_sub r s).neg).deriv
    convert! h using 1 <;> simp only [Pi.neg_apply,neg_neg]
  · rw [ite_eq_right hs,(auto_green_outer_eventuallyEq_zero heta (le_of_not_gt hs)).deriv.deriv_eq]
    simp only [deriv_const',deriv_const]

theorem auto_green_cutoff_deriv_bounds : ∃ B : ℝ, 0 < B ∧ ∀ eta : ℝ, 0 < eta → ∀ r s : ℝ,
    |deriv (autoGreenInner eta) s| ≤ B/eta ∧ |deriv (deriv (autoGreenInner eta)) s| ≤ B/eta^2 ∧
    |deriv (autoGreenOuter r eta) s| ≤ B/eta ∧ |deriv (deriv (autoGreenOuter r eta)) s| ≤ B/eta^2 := by
  obtain ⟨B,hB,hBound⟩ := auto_green_inner_deriv_bounds
  refine ⟨B,hB,?_⟩
  intro eta heta r s
  refine ⟨(hBound eta heta s).1,(hBound eta heta s).2,?_⟩
  rw [auto_green_outer_deriv heta,auto_green_outer_second heta]
  by_cases hs : s < r
  · simp only [ite_eq_left hs,abs_neg]
    exact hBound eta heta (r-s)
  · simp only [ite_eq_right hs,abs_zero]
    constructor <;> positivity

end Yau.LeafProofs.L05AutonomousAux
