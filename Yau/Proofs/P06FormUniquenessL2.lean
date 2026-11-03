import Yau.Proofs.P06FormUniquenessL2Energy
import Yau.Proofs.P06MetricCutoffs

/-! Uniqueness for arbitrary original L² form heat PDE solutions. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder ENNReal
namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem formUnique_cutoff_error_integral_le_global
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (W : RealForm M k) (hW : L2RealForm g.form μ W) (hsW : SmoothRealForm W)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    {a : ℝ} (hgrad : ∀ x, L18Aux.scalarGradientPair g.form η η x ≤ a) :
    (∫ x, L18Aux.scalarGradientPair g.form η η x * formNormSq g.form W x ∂μ) ≤
      a * ∫ x, formNormSq g.form W x ∂μ := by
  have hi : Integrable (fun x => L18Aux.scalarGradientPair g.form η η x * formNormSq g.form W x) μ :=
    L18Aux.smoothFn_integrable_compact g μ hμ
      (L18Aux.smoothFn_mul (L18Aux.smoothFn_scalarGradientPair g hη hη)
        (G04Aux.formInner_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g) W W hsW hsW))
      (L18Aux.scalarGradientPair_hasCompactSupport g.form η η hcη).mul_right
  rw [← integral_const_mul]
  apply integral_mono hi ((L03.formNormSq_integrable g μ W hW).const_mul a)
  intro x
  change L18Aux.scalarGradientPair g.form η η x * formNormSq g.form W x ≤
    a * formNormSq g.form W x
  exact mul_le_mul_of_nonneg_right (hgrad x) (L03.formNormSq_nonneg _ _ _)

theorem l2FormHeat_cutoff_energy_decay
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {A : RealForm M 2} {U V : ℝ → RealForm M 2}
    (hU : IsL2FormHeat g.form μ A U) (hV : IsL2FormHeat g.form μ A V)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g.form o χ)
    {T : ℝ} (hT : 0 < T) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, 1 ≤ j → ∀ t, 0 < t → t ≤ T →
      (∫ x, χ j x ^ 2 * formNormSq g.form (U t - V t) x ∂μ) ≤ D / (j : ℝ) ^ 2 := by
  obtain ⟨c, hc, hχ⟩ := hχ
  obtain ⟨K, hK, hk⟩ := l2FormHeat_difference_norm_integral_bound g μ hU hV hT
  refine ⟨2 * T * c ^ 2 * K, by positivity, ?_⟩
  intro j hj t ht htT
  have hcut := hχ j hj
  have he (s : ℝ) (hs : 0 < s) (hsT : s ≤ T) :
      (∫ x, L18Aux.scalarGradientPair g.form (χ j) (χ j) x *
        formNormSq g.form (U s - V s) x ∂μ) ≤ (c / j) ^ 2 * K := by
    apply (formUnique_cutoff_error_integral_le_global g μ hμ (U s - V s)
      (L03.l2RealForm_sub g μ _ _ (hU.2.2.2.2.1 s hs) (hV.2.2.2.2.1 s hs))
      (smoothFormTime_slice (smoothFormTime_sub hU.2.2.1 hV.2.2.1) hs)
      hcut.1 hcut.2.1 ?_).trans (mul_le_mul_of_nonneg_left (hk s hs hsT) (sq_nonneg _))
    intro x
    simpa only [L18Aux.scalarGradientPair, L18Aux.chartGradientPair_eq_sum,
      realGradientNormSq] using hcut.2.2.2.2.2 x
  have hi := l2FormHeat_difference_cutoff_tendsto_zero g μ hU hV hcut.1
    (fun x => by rw [abs_of_nonneg (hcut.2.2.1 x).1]; exact (hcut.2.2.1 x).2)
  have hh := formHeat_cutoff_energy_le_of_initial g μ hμ hU.2.2.1 hV.2.2.1
    hU.2.2.2.1 hV.2.2.2.1 hcut.1 hcut.2.1 hi (mul_nonneg (sq_nonneg _) hK) hT he t ht htT
  calc
    _ ≤ 2 * T * ((c / j) ^ 2 * K) := hh
    _ = _ := by rw [div_pow]; ring

theorem formUnique_metricCutoffFamily_tendsto_one
    (g : SmoothMetric M) (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ)
    (hχ : MetricCutoffFamily g.form o χ) (x : M.Carrier) :
    Tendsto (fun j : ℕ => χ (j + 1) x) atTop (𝓝 1) := by
  obtain ⟨c, hc, hχ⟩ := hχ
  apply tendsto_const_nhds.congr'
  obtain ⟨J, hJ⟩ := exists_nat_gt (inducedDistance g.form o x + 1)
  filter_upwards [eventually_ge_atTop J] with j hj
  have hjpos : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have hx : x ∈ distBall g.form o (j + 1 : ℕ) := by
    apply (L12Aux.mem_distBall_iff g o x hjpos).mpr
    have hcast : (J : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast (hj.trans (Nat.le_succ j))
    linarith
  exact ((hχ (j + 1) (by omega)).2.2.2.1 x hx).symm

/-- Every solution of the original L² PDE class has the same evolution.
The finite-time L² bound controls the sole IMS boundary term. -/
theorem l2FormHeat_unique
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M 2) (U V : ℝ → RealForm M 2)
    (hU : IsL2FormHeat g.form μ A U) (hV : IsL2FormHeat g.form μ A V) :
    ∀ t, 0 ≤ t → U t = V t := by
  intro t ht
  rcases eq_or_lt_of_le ht with rfl | ht
  · exact hU.2.1.trans hV.2.1.symm
  obtain ⟨o⟩ := (inferInstance : Nonempty M.Carrier)
  obtain ⟨χ, hχ⟩ := metricCutoffFamily g o
  obtain ⟨D, hD, hd⟩ := l2FormHeat_cutoff_energy_decay g μ hμ hU hV o χ hχ ht
  have hχone := formUnique_metricCutoffFamily_tendsto_one g o χ hχ
  obtain ⟨c, hc, hχ⟩ := hχ
  let W := U t - V t
  have hW : L2RealForm g.form μ W :=
    L03.l2RealForm_sub g μ _ _ (hU.2.2.2.2.1 t ht) (hV.2.2.2.2.1 t ht)
  have hsW : SmoothRealForm W :=
    smoothFormTime_slice (smoothFormTime_sub hU.2.2.1 hV.2.2.1) ht
  have hn : SmoothFn (formNormSq g.form W) :=
    G04Aux.formInner_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g) W W hsW hsW
  have hi : ∀ j : ℕ, AEStronglyMeasurable
      (fun x => χ (j + 1) x ^ 2 * formNormSq g.form W x) μ := by
    intro j
    exact (L18Aux.continuous_of_smoothFn
      (L18Aux.smoothFn_mul (L18Aux.smoothFn_pow (hχ (j + 1) (by omega)).1 2) hn)).aestronglyMeasurable
  have hb : ∀ j : ℕ, ∀ᵐ x ∂μ,
      ‖χ (j + 1) x ^ 2 * formNormSq g.form W x‖ ≤ formNormSq g.form W x := by
    intro j
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (L03.formNormSq_nonneg _ _ _))]
      have hsq : χ (j + 1) x ^ 2 ≤ 1 := by
        have hr := (hχ (j + 1) (by omega)).2.2.1 x
        nlinarith
      exact mul_le_of_le_one_left (L03.formNormSq_nonneg _ _ _) hsq)
  have hp : ∀ᵐ x ∂μ, Tendsto (fun j : ℕ => χ (j + 1) x ^ 2 * formNormSq g.form W x)
      atTop (𝓝 (formNormSq g.form W x)) := ae_of_all _ (fun x => by
    simpa only [one_pow, one_mul] using (hχone x).pow 2 |>.mul_const (formNormSq g.form W x))
  have hconv : Tendsto (fun j : ℕ => ∫ x, χ (j + 1) x ^ 2 * formNormSq g.form W x ∂μ)
      atTop (𝓝 (∫ x, formNormSq g.form W x ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence (formNormSq g.form W)
      (Eventually.of_forall hi) (Eventually.of_forall hb) (L03.formNormSq_integrable g μ W hW) hp
  have hlim : Tendsto (fun j : ℕ => D / ((j + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0) :=
    ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).const_div_atTop D
  have hzero : Tendsto (fun j : ℕ => ∫ x, χ (j + 1) x ^ 2 * formNormSq g.form W x ∂μ)
      atTop (𝓝 0) := squeeze_zero
    (fun j => integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (L03.formNormSq_nonneg _ _ _)))
    (fun j => hd (j + 1) (by omega) t ht le_rfl) hlim
  have he : (∫ x, formNormSq g.form W x ∂μ) = 0 := tendsto_nhds_unique hconv hzero
  have hae := (L03.integral_formNormSq_eq_zero_iff_ae g μ W hW).mp he
  apply L03.smoothRealForm_eq_of_ae g μ hμ (U t) (V t)
    (smoothFormTime_slice hU.2.2.1 ht) (smoothFormTime_slice hV.2.2.1 ht)
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp hx

end Yau.NodeProofs.P06Aux

namespace Yau.NodeProofs
open Yau Yau.Blueprint

/-- The full uniqueness projection of the original L² Hodge heat target. -/
theorem P06_L2_form_uniqueness_proved :
    ∀ (n : ℕ) (X : KahlerManifold n) (μ : Measure X.manifold.Carrier),
      IsRiemannianVolume X.metric.form μ →
      ∀ (A : RealForm X.manifold 2) (U V : ℝ → RealForm X.manifold 2),
        IsL2FormHeat X.metric.form μ A U → IsL2FormHeat X.metric.form μ A V →
          ∀ t, 0 < t → U t = V t := by
  intro n X μ hμ A U V hU hV t ht
  exact P06Aux.l2FormHeat_unique X.metric μ hμ A U V hU hV t ht.le

end Yau.NodeProofs
