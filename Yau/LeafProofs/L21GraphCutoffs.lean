import Yau.LeafProofs.L21BoundaryWeight

/-! Smooth compact cutoffs for the degenerate graph operators. The scaled
symbols are uniformly bounded and eventually zero at every interior point. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def boundaryCutoff (m : ℕ) (x : E) : ℝ :=
  Real.smoothTransition (((m : ℝ) + 1) * rho x - 1)

theorem contDiff_boundaryCutoff (m : ℕ) : ContDiff ℝ ∞ (boundaryCutoff (E := E) m) := by
  have harg : ContDiff ℝ ∞ (fun x : E => ((m : ℝ) + 1) * rho x - 1) :=
    (contDiff_const.mul (contDiff_rho (E := E))).sub contDiff_const
  exact Real.smoothTransition.contDiff.comp harg

theorem boundaryCutoff_nonneg (m : ℕ) (x : E) : 0 ≤ boundaryCutoff m x :=
  Real.smoothTransition.nonneg _

theorem boundaryCutoff_le_one (m : ℕ) (x : E) : boundaryCutoff m x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem tsupport_boundaryCutoff_subset_level (m : ℕ) :
    tsupport (boundaryCutoff (E := E) m) ⊆ {x | 1 ≤ ((m : ℝ) + 1) * rho x} := by
  apply closure_minimal ?_
    (isClosed_le continuous_const (contDiff_rho.continuous.const_mul ((m : ℝ) + 1)))
  intro x hx
  have hh : ¬(((m : ℝ) + 1) * rho x - 1 ≤ 0) := by
    intro hn
    exact hx (Real.smoothTransition.zero_of_nonpos hn)
  have hp := lt_of_not_ge hh
  change 1 ≤ ((m : ℝ) + 1) * rho x
  linarith

theorem tsupport_boundaryCutoff_subset_ball (m : ℕ) :
    tsupport (boundaryCutoff (E := E) m) ⊆ Metric.ball (0 : E) 1 := by
  intro x hx
  have hh := tsupport_boundaryCutoff_subset_level m hx
  change 1 ≤ ((m : ℝ) + 1) * rho x at hh
  have hm : 0 < (m : ℝ) + 1 := by positivity
  have hρ : 0 < rho x := by
    by_contra hn
    have hh0 := mul_nonpos_of_nonneg_of_nonpos hm.le (le_of_not_gt hn)
    linarith
  rw [Metric.mem_ball, dist_zero_right]
  dsimp only [rho] at hρ
  nlinarith [norm_nonneg x]

theorem hasCompactSupport_boundaryCutoff [FiniteDimensional ℝ E] (m : ℕ) :
    HasCompactSupport (boundaryCutoff (E := E) m) :=
  (isCompact_closedBall (0 : E) 1).of_isClosed_subset
    (isClosed_tsupport _) (fun _ hx => Metric.ball_subset_closedBall (tsupport_boundaryCutoff_subset_ball m hx))

theorem eventually_boundaryCutoff_eq_one_nhds {x : E}
    (hx : x ∈ Metric.ball (0 : E) 1) :
    ∀ᶠ m : ℕ in atTop, boundaryCutoff (E := E) m =ᶠ[𝓝 x] (fun _ => 1) := by
  have hr := rho_pos hx
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / rho x)
  have hMρ : 2 < (M : ℝ) * rho x := (div_lt_iff₀ hr).mp hM
  refine Filter.eventually_atTop.mpr ⟨M, ?_⟩
  intro m hm
  have hm' : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have harg : 1 < ((m : ℝ) + 1) * rho x - 1 := by nlinarith
  have hc : ContinuousAt (fun y : E => ((m : ℝ) + 1) * rho y - 1) x :=
    ((continuous_const.mul (contDiff_rho (E := E)).continuous).sub continuous_const).continuousAt
  have hnear : ∀ᶠ y in 𝓝 x, 1 < ((m : ℝ) + 1) * rho y - 1 := hc.eventually_const_lt harg
  filter_upwards [hnear] with y hy
  exact Real.smoothTransition.one_of_one_le hy.le

theorem eventually_boundaryCutoff_eq_one {x : E} (hx : x ∈ Metric.ball (0 : E) 1) :
    ∀ᶠ m : ℕ in atTop, boundaryCutoff m x = 1 := by
  filter_upwards [eventually_boundaryCutoff_eq_one_nhds hx] with m hm
  exact hm.eq_of_nhds

theorem eventually_fderiv_boundaryCutoff_eq_zero {x : E}
    (hx : x ∈ Metric.ball (0 : E) 1) :
    ∀ᶠ m : ℕ in atTop, fderiv ℝ (boundaryCutoff (E := E) m) x = 0 := by
  filter_upwards [eventually_boundaryCutoff_eq_one_nhds hx] with m hm
  simpa only [fderiv_const_apply] using hm.fderiv_eq (𝕜 := ℝ)

theorem tendsto_boundaryCutoff {x : E} (hx : x ∈ Metric.ball (0 : E) 1) :
    Tendsto (fun m : ℕ => boundaryCutoff m x) atTop (𝓝 1) := by
  have he : (fun m : ℕ => boundaryCutoff m x) =ᶠ[atTop] (fun _ => 1) :=
    eventually_boundaryCutoff_eq_one hx
  exact tendsto_const_nhds.congr' he.symm

theorem deriv_smoothTransition_eq_zero_of_neg {t : ℝ} (ht : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact Real.smoothTransition.zero_of_nonpos hs.le
  simpa only [deriv_const] using he.deriv_eq

theorem deriv_smoothTransition_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 t] (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact Real.smoothTransition.one_of_one_le hs.le
  simpa only [deriv_const] using he.deriv_eq

theorem exists_bound_deriv_smoothTransition :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ C := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t
  by_cases ht : t < 0
  · rw [deriv_smoothTransition_eq_zero_of_neg ht, abs_zero]
    exact le_trans zero_le_one (le_max_left _ _)
  by_cases ht1 : 1 < t
  · rw [deriv_smoothTransition_eq_zero_of_one_lt ht1, abs_zero]
    exact le_trans zero_le_one (le_max_left _ _)
  exact (hB t ⟨le_of_not_gt ht, le_of_not_gt ht1⟩).trans (le_max_right _ _)

theorem fderiv_boundaryCutoff (m : ℕ) (x : E) :
    fderiv ℝ (boundaryCutoff (E := E) m) x =
      (deriv Real.smoothTransition (((m : ℝ) + 1) * rho x - 1) * ((m : ℝ) + 1)) •
        fderiv ℝ (rho : E → ℝ) x := by
  have hdarg := ((hasFDerivAt_rho x).const_mul ((m : ℝ) + 1)).sub_const 1
  have hη : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (((m : ℝ) + 1) * rho x - 1))
      (((m : ℝ) + 1) * rho x - 1) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable (by simp) _).hasDerivAt
  have hd := hη.hasFDerivAt.comp x hdarg
  ext u
  have he := congrArg (fun L : E →L[ℝ] ℝ => L u) hd.fderiv
  change fderiv ℝ (boundaryCutoff (E := E) m) x u = _ at he
  rw [he, (hasFDerivAt_rho x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

/-- A uniform bound, together with eventual pointwise vanishing, suffices
for dominated convergence in every weighted graph norm. -/
theorem exists_bound_scaled_fderiv_boundaryCutoff :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∀ x ∈ Metric.ball (0 : E) 1,
      ‖rho x • fderiv ℝ (boundaryCutoff (E := E) m) x‖ ≤ C := by
  obtain ⟨B, hB, hbound⟩ := exists_bound_deriv_smoothTransition
  refine ⟨4 * B, by positivity, ?_⟩
  intro m x hx
  let t := ((m : ℝ) + 1) * rho x - 1
  by_cases ht : 1 < t
  · rw [fderiv_boundaryCutoff, show deriv Real.smoothTransition
        (((m : ℝ) + 1) * rho x - 1) = 0 from deriv_smoothTransition_eq_zero_of_one_lt ht]
    simp only [zero_mul, zero_smul, smul_zero, norm_zero]
    positivity
  have hρ := rho_pos hx
  have hm : 0 < (m : ℝ) + 1 := by positivity
  have hprod : ((m : ℝ) + 1) * rho x ≤ 2 := by dsimp [t] at ht; linarith
  rw [fderiv_boundaryCutoff, smul_smul, norm_smul, Real.norm_eq_abs]
  simp only [abs_mul, abs_of_pos hρ, abs_of_pos hm]
  calc
    _ = (((m : ℝ) + 1) * rho x) * |deriv Real.smoothTransition t| *
        ‖fderiv ℝ (rho : E → ℝ) x‖ := by ring
    _ ≤ 2 * B * 2 := by
      gcongr
      · exact hbound t
      · exact norm_fderiv_rho_le_two hx
    _ = 4 * B := by ring

end Yau.LeafProofs.L21Aux
