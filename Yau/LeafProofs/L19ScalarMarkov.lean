import Yau.LeafProofs.L19ScalarResolvent
import Yau.LeafProofs.L19NormalContraction

/-! The Markov property of the actual variational scalar resolvents. -/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem normalClip_mem_interval {K : ℝ} (hK : 0 ≤ K) (r : ℝ) :
    0 ≤ normalClip K r ∧ normalClip K r ≤ K :=
  ⟨le_max_left _ _, max_le hK (min_le_left _ _)⟩

theorem normalClip_distance_le {K b : ℝ} (hb : 0 ≤ b ∧ b ≤ K) (r : ℝ) :
    |normalClip K r - b| ≤ |r - b| := by
  have hK : 0 ≤ K := hb.1.trans hb.2
  rcases le_total r 0 with hr | hr
  · rw [normalClip, min_eq_right (hr.trans hK), max_eq_left hr,
      zero_sub, abs_neg, abs_of_nonneg hb.1, abs_of_nonpos (by linarith : r - b ≤ 0)]
    linarith
  · rcases le_total r K with hrK | hrK
    · rw [normalClip, min_eq_right hrK, max_eq_right hr]
    · rw [normalClip, min_eq_left hrK, max_eq_right hK,
        abs_of_nonneg (by linarith : 0 ≤ K - b), abs_of_nonneg (by linarith : 0 ≤ r - b)]
      linarith

theorem normalClip_eq_self {K r : ℝ} (hr : 0 ≤ r ∧ r ≤ K) : normalClip K r = r := by
  rw [normalClip, min_eq_right hr.2, max_eq_right hr.1]

theorem normalClipL2_eq_self_iff {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (K : ℝ) (hK : 0 ≤ K) (f : Lp ℝ 2 μ) :
    normalClipL2 μ K hK f = f ↔ ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ K := by
  constructor
  · intro hf
    have hc := normalClipL2_coe μ K hK f
    rw [hf] at hc
    filter_upwards [hc] with x hx
    rw [hx]
    exact normalClip_mem_interval hK _
  · intro hf
    apply Lp.ext
    filter_upwards [normalClipL2_coe μ K hK f, hf] with x hx hfx
    exact hx.trans (normalClip_eq_self hfx)

/-- Bounded normal intervals are closed in the actual L² topology even
when the constant upper bound itself is not globally in L². -/
theorem normalIntervalL2_isClosed {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (K : ℝ) (hK : 0 ≤ K) : IsClosed {f : Lp ℝ 2 μ | ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ K} := by
  have hc : Continuous (normalClipL2 μ K hK) :=
    (normalClip_lipschitz K).continuous_compLp (normalClip_zero hK)
  convert isClosed_eq hc continuous_id using 1
  ext f
  exact (normalClipL2_eq_self_iff μ K hK f).symm

/-- Actual scalar resolvents preserve every bounded normal interval.
Both the projection into the energy space and the strict minimization
argument have been proved for the fixed metric and volume. -/
theorem scalarResolvent_markov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h)
    (K : ℝ) (hK : 0 < K) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ K) :
    ∀ᵐ x ∂μ, 0 ≤ scalarResolvent g μ hμ h hh f x ∧ scalarResolvent g μ hμ h hh f x ≤ K := by
  let u := scalarResolventEnergy g μ hμ h hh f
  obtain ⟨v, hv, hE⟩ := scalarEnergy_normalClip g μ hμ u K hK
  have hdist : ‖scalarEnergyL2 g μ hμ v - f‖ ≤ ‖scalarEnergyL2 g μ hμ u - f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hv, hf, Lp.coeFn_sub (scalarEnergyL2 g μ hμ v) f,
      Lp.coeFn_sub (scalarEnergyL2 g μ hμ u) f] with x hvx hfx hsubv hsubu
    simp only [hsubv, hsubu, Pi.sub_apply, hvx, Real.norm_eq_abs]
    exact normalClip_distance_le hfx _
  have hEnergy : scalarClosedEnergy g μ hμ v v ≤ scalarClosedEnergy g μ hμ u u := by
    simpa only [scalarClosedEnergy, real_inner_self_eq_norm_sq] using hE
  have hobj : scalarResolventObjective g μ hμ h f v ≤ scalarResolventObjective g μ hμ h f u := by
    unfold scalarResolventObjective
    have hmul := mul_le_mul_of_nonneg_left hEnergy hh.le
    have hsq : ‖scalarEnergyL2 g μ hμ v - f‖ ^ 2 ≤ ‖scalarEnergyL2 g μ hμ u - f‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hdist
    exact add_le_add hsq hmul
  have hstrict := scalarResolventObjective_strict_minimum g μ hμ h hh f v
  change scalarResolventObjective g μ hμ h f u + min 1 h * ‖v - u‖ ^ 2 ≤
    scalarResolventObjective g μ hμ h f v at hstrict
  have hzero : ‖v - u‖ ^ 2 = 0 := by
    have hpos : 0 < min 1 h := lt_min zero_lt_one hh
    have hle : min 1 h * ‖v - u‖ ^ 2 ≤ 0 := by linarith only [hstrict, hobj]
    have hn : ‖v - u‖ ^ 2 ≤ 0 := by nlinarith only [hle, hpos]
    exact le_antisymm hn (sq_nonneg _)
  have hvu : v = u := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
  rw [hvu] at hv
  filter_upwards [hv] with x hx
  change 0 ≤ scalarEnergyL2 g μ hμ u x ∧ scalarEnergyL2 g μ hμ u x ≤ K
  rw [hx]
  exact normalClip_mem_interval hK.le _

theorem scalarResolvent_pow_markov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h)
    (K : ℝ) (hK : 0 < K) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ K) (k : ℕ) :
    ∀ᵐ x ∂μ, 0 ≤ ((scalarResolvent g μ hμ h hh) ^ k) f x ∧
      ((scalarResolvent g μ hμ h hh) ^ k) f x ≤ K := by
  induction k with
  | zero => simpa only [pow_zero, ContinuousLinearMap.one_apply] using hf
  | succ k hk =>
    rw [pow_succ']
    exact scalarResolvent_markov g μ hμ h hh K hK _ hk

/-- Strong limits of actual Euler resolvent powers retain the bounded
Markov interval.  The heat family supplies the genuine Euler limit. -/
theorem scalarResolvent_euler_limit_markov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (step : ℕ → ℝ) (hstep : ∀ j, 0 < step j)
    (power : ℕ → ℕ) (K : ℝ) (hK : 0 < K) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ K) (v : Lp ℝ 2 μ)
    (hv : Tendsto (fun j => ((scalarResolvent g μ hμ (step j) (hstep j)) ^ power j) f)
      atTop (nhds v)) :
    ∀ᵐ x ∂μ, 0 ≤ v x ∧ v x ≤ K := by
  apply (normalIntervalL2_isClosed μ K hK.le).mem_of_tendsto hv
  exact Eventually.of_forall (fun j => scalarResolvent_pow_markov g μ hμ (step j) (hstep j) K hK f hf (power j))

end Yau.LeafProofs.L19Aux
