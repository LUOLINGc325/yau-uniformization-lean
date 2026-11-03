import Yau.Blueprint.HodgeContracts
import Yau.LeafProofs.L03HodgeCaccioppoli
import Yau.LeafProofs.L19HeatLocalCaccioppoli
import Yau.Proofs.G04TraceSmooth

/-! Local calculus for the original bounded form heat class. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem smoothFormTime_slice {S : Set ℝ} {U : ℝ → RealForm M k}
    (hU : SmoothFormTime U S) {t : ℝ} (ht : t ∈ S) : SmoothRealForm (U t) := by
  intro x I
  exact (hU x I).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun z hz => ⟨hz, ht⟩)

theorem smoothFormTime_sub {S : Set ℝ} {U V : ℝ → RealForm M k}
    (hU : SmoothFormTime U S) (hV : SmoothFormTime V S) :
    SmoothFormTime (fun t => U t - V t) S := by
  intro x I
  exact (hU x I).sub (hV x I)

theorem smoothFormTime_inner {S : Set ℝ} (g : SmoothMetric M)
    {U V : ℝ → RealForm M k}
    (hU : SmoothFormTime U S) (hV : SmoothFormTime V S) :
    SmoothSpaceTime (fun y t => formInner g.form (U t) (V t) y) S := by
  intro x
  apply (contDiffOn_const.mul (L03.tensorCoefficientPairing_contDiffOn
    (fun p : ComplexVector n × ℝ => (realMetricFn g.form x p.1)⁻¹)
    (fun p => formComponents (U p.2) x p.1)
    (fun p => formComponents (V p.2) x p.1)
    (chartTarget x ×ˢ S) (fun a b =>
      (L18Aux.realMetricFn_inverse_contDiffOn g x a b).comp contDiffOn_fst
        (fun _ hp => hp.1)) (hU x) (hV x))).congr
  intro p hp
  exact L03.formInner_chartInv_eq_tensorPairing g.form (U p.2) (V p.2) x hp.1

theorem smoothFormTime_normSq {S : Set ℝ} (g : SmoothMetric M)
    {U : ℝ → RealForm M k} (hU : SmoothFormTime U S) :
    SmoothSpaceTime (fun y t => formNormSq g.form (U t) y) S :=
  smoothFormTime_inner g hU hU

theorem formSmoothInitial_coefficient_tendsto
    {U : ℝ → RealForm M k} {A : RealForm M k}
    (hU : FormSmoothInitial U A) (x : M.Carrier) (I : Fin k → RIdx n) :
    Tendsto (fun t => formComponents (U t) x (chartPt x x) I)
      (𝓝[>] 0) (𝓝 (formComponents A x (chartPt x x) I)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨τ, hτ, hτU⟩ := hU.2 x {chartPt x x} isCompact_singleton
    (singleton_subset_iff.mpr (mem_extChartAt_target x)) 0 I ε hε
  filter_upwards [Ioo_mem_nhdsGT hτ] with t ht
  have hh := hτU t ht.1 ht.2 (chartPt x x) (mem_singleton _)
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Real.dist_eq] using hh

theorem formSmoothInitial_difference_normSq_tendsto
    (g : HermitianField M) {U V : ℝ → RealForm M k} {A : RealForm M k}
    (hU : FormSmoothInitial U A) (hV : FormSmoothInitial V A) (x : M.Carrier) :
    Tendsto (fun t => formNormSq g (U t - V t) x) (𝓝[>] 0) (𝓝 0) := by
  have hc (I : Fin k → RIdx n) :
      Tendsto (fun t => formComponents (U t - V t) x (chartPt x x) I)
        (𝓝[>] 0) (𝓝 0) := by
    simpa only [formComponents, Pi.sub_apply, ContinuousAlternatingMap.sub_apply, sub_self] using
      (formSmoothInitial_coefficient_tendsto hU x I).sub
        (formSmoothInitial_coefficient_tendsto hV x I)
  have hh := (tendsto_finsetSum Finset.univ (fun I _ =>
    tendsto_finsetSum Finset.univ (fun J _ =>
      ((hc I).mul (hc J)).mul_const
        (∏ r, (realMetricFn g x (chartPt x x))⁻¹ (I r) (J r))))).const_mul
          (Nat.factorial k : ℝ)⁻¹
  simpa only [zero_mul, Finset.sum_const_zero, mul_zero, formNormSq, formInner] using hh

theorem boundedFormHeat_difference_bound (g : HermitianField M)
    {U V : ℝ → RealForm M k}
    (hU : BoundedFormHeatClass g U) (hV : BoundedFormHeatClass g V)
    {T : ℝ} (hT : 0 < T) :
    ∃ B : ℝ, 0 < B ∧ ∀ x t, 0 < t → t ≤ T →
      formNormSq g (U t - V t) x ≤ B := by
  obtain ⟨B, hB, hb⟩ := hU T hT
  obtain ⟨C, hC, hc⟩ := hV T hT
  refine ⟨2 * (B ^ 2 + C ^ 2), by positivity, ?_⟩
  intro x t ht htT
  have he : U t - V t = U t + (-1 : ℝ) • V t := by rw [neg_one_smul ℝ (V t), sub_eq_add_neg]
  rw [he]
  have hh := L03.formNormSq_add_le g (U t) ((-1 : ℝ) • V t) x
  rw [L03.formNormSq_smul_eq] at hh
  nlinarith [hb x t ht htT, hc x t ht htT]

/-- The original full smooth initial trace removes every compact initial
energy, even though the solutions need not be globally square integrable. -/
theorem boundedFormHeat_difference_cutoff_tendsto_zero
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {U V : ℝ → RealForm M k} {A : RealForm M k}
    (hU : IsBoundedFormHeat g.form A U) (hV : IsBoundedFormHeat g.form A V)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hηbound : ∀ x, |η x| ≤ 1) :
    Tendsto (fun t => ∫ x, η x ^ 2 * formNormSq g.form (U t - V t) x ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  obtain ⟨B, hB, hb⟩ := boundedFormHeat_difference_bound g.form hU.2.2.1 hV.2.2.1 zero_lt_one
  let b : M.Carrier → ℝ := (tsupport η).indicator (fun _ => B)
  have hbi : Integrable b μ :=
    (integrableOn_const hcη.isCompact.measure_ne_top).integrable_indicator (isClosed_tsupport η).measurableSet
  have hnorm := smoothFormTime_normSq g (smoothFormTime_sub hU.1 hV.1)
  have him : ∀ᶠ t in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun x => η x ^ 2 * formNormSq g.form (U t - V t) x) μ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (L18Aux.continuous_of_smoothFn
      (L18Aux.smoothFn_mul (L18Aux.smoothFn_pow hη 2)
        (L19Aux.smoothSpaceTime_slice hnorm ht))).aestronglyMeasurable
  have hib : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖η x ^ 2 * formNormSq g.form (U t - V t) x‖ ≤ b x := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    exact ae_of_all _ (fun x => by
      by_cases hx : x ∈ tsupport η
      · have hsq : η x ^ 2 ≤ 1 := by
          simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (η x)) (hηbound x) 2
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (sq_nonneg _) (L03.formNormSq_nonneg _ _ _))]
        change _ ≤ (tsupport η).indicator (fun _ => B) x
        rw [indicator_of_mem hx]
        exact (mul_le_of_le_one_left (L03.formNormSq_nonneg _ _ _) hsq).trans
          (hb x t ht.1 ht.2.le)
      · simp [b, hx, image_eq_zero_of_notMem_tsupport hx])
  have hil : ∀ᵐ x ∂μ, Tendsto
      (fun t => η x ^ 2 * formNormSq g.form (U t - V t) x)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := ae_of_all _ (fun x => by
    simpa only [mul_zero] using
      (formSmoothInitial_difference_normSq_tendsto g.form hU.2.1 hV.2.1 x).const_mul (η x ^ 2))
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence b him hib hbi hil

end Yau.NodeProofs.P06Aux
