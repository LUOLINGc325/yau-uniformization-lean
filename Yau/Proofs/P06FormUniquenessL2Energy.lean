import Yau.Proofs.P06FormUniquenessEnergy

/-! The original L² trace and local terminal energy for arbitrary form PDE
solutions. No Hilbert path representation is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder ENNReal
namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem formUnique_normSq_sub_le (g : HermitianField M)
    (A B : RealForm M k) (x : M.Carrier) :
    formNormSq g (A - B) x ≤ 2 * (formNormSq g A x + formNormSq g B x) := by
  have he : A - B = A + (-1 : ℝ) • B := by rw [neg_one_smul ℝ B, sub_eq_add_neg]
  rw [he]
  have hh := L03.formNormSq_add_le g A ((-1 : ℝ) • B) x
  rw [L03.formNormSq_smul_eq] at hh
  nlinarith

theorem formUnique_integral_normSq_sub_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B) :
    (∫ x, formNormSq g.form (A - B) x ∂μ) ≤
      2 * ((∫ x, formNormSq g.form A x ∂μ) + ∫ x, formNormSq g.form B x ∂μ) := by
  have hiA := L03.formNormSq_integrable g μ A hA
  have hiB := L03.formNormSq_integrable g μ B hB
  calc
    _ ≤ ∫ x, 2 * (formNormSq g.form A x + formNormSq g.form B x) ∂μ :=
      integral_mono (L03.formNormSq_integrable g μ _ (L03.l2RealForm_sub g μ A B hA hB))
        ((hiA.add hiB).const_mul 2) (fun x => formUnique_normSq_sub_le g.form A B x)
    _ = _ := by rw [integral_const_mul, integral_add hiA hiB]

theorem formUnique_cutoff_norm_integral_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (W : RealForm M k) (hW : L2RealForm g.form μ W) (hsW : SmoothRealForm W)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hηbound : ∀ x, |η x| ≤ 1) :
    (∫ x, η x ^ 2 * formNormSq g.form W x ∂μ) ≤ ∫ x, formNormSq g.form W x ∂μ := by
  have hn := L03.formNormSq_integrable g μ W hW
  have hp (x : M.Carrier) : η x ^ 2 * formNormSq g.form W x ≤ formNormSq g.form W x := by
    have hsq : η x ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (η x)) (hηbound x) 2
    exact mul_le_of_le_one_left (L03.formNormSq_nonneg _ _ _) hsq
  have hm : AEStronglyMeasurable (fun x => η x ^ 2 * formNormSq g.form W x) μ :=
    (L18Aux.continuous_of_smoothFn (L18Aux.smoothFn_mul (L18Aux.smoothFn_pow hη 2)
      (G04Aux.formInner_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g) W W hsW hsW))).aestronglyMeasurable
  have hi := hn.mono_nonneg hm
    (ae_of_all _ (fun x => mul_nonneg (sq_nonneg _) (L03.formNormSq_nonneg _ _ _)))
    (ae_of_all _ hp)
  exact integral_mono hi hn hp

theorem l2FormHeat_initial_normSq_tendsto
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    {A : RealForm M 2} {U : ℝ → RealForm M 2}
    (hU : IsL2FormHeat g.form μ A U) :
    Tendsto (fun t => ∫ x, formNormSq g.form (U t - A) x ∂μ) (𝓝[>] 0) (𝓝 0) := by
  have hh : Tendsto (fun t => (formL2DistanceSq g.form μ (U t) A).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hU.2.2.2.2.2.1
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [L03.formL2DistanceSq_eq_ofReal_integral g μ (U t) A (hU.2.2.2.2.1 t ht) hU.1,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => L03.formNormSq_nonneg _ _ _))]

/-- The exact L² initial convergence is sufficient to remove every compact
initial energy; no pointwise or smooth initial trace is inserted. -/
theorem l2FormHeat_difference_cutoff_tendsto_zero
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    {A : RealForm M 2} {U V : ℝ → RealForm M 2}
    (hU : IsL2FormHeat g.form μ A U) (hV : IsL2FormHeat g.form μ A V)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hηbound : ∀ x, |η x| ≤ 1) :
    Tendsto (fun t => ∫ x, η x ^ 2 * formNormSq g.form (U t - V t) x ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  have hh : Tendsto (fun t => 2 * ((∫ x, formNormSq g.form (U t - A) x ∂μ) +
      ∫ x, formNormSq g.form (V t - A) x ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_add, mul_zero] using
      ((l2FormHeat_initial_normSq_tendsto g μ hU).add
        (l2FormHeat_initial_normSq_tendsto g μ hV)).const_mul 2
  apply squeeze_zero' (Eventually.of_forall (fun t => integral_nonneg
    (fun x => mul_nonneg (sq_nonneg _) (L03.formNormSq_nonneg _ _ _)))) ?_ hh
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hu := hU.2.2.2.2.1 t ht
  have hv := hV.2.2.2.2.1 t ht
  have hcut := formUnique_cutoff_norm_integral_le g μ (U t - V t)
    (L03.l2RealForm_sub g μ _ _ hu hv)
    (smoothFormTime_slice (smoothFormTime_sub hU.2.2.1 hV.2.2.1) ht) hη hηbound
  have hs := formUnique_integral_normSq_sub_le g μ (U t - A) (V t - A)
    (L03.l2RealForm_sub g μ _ _ hu hU.1) (L03.l2RealForm_sub g μ _ _ hv hV.1)
  have he : (U t - A) - (V t - A) = U t - V t := by abel
  rw [he] at hs
  exact hcut.trans hs

theorem l2FormHeat_norm_integral_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    {A : RealForm M 2} {U : ℝ → RealForm M 2}
    (hU : IsL2FormHeat g.form μ A U) {T : ℝ} (hT : 0 < T) :
    ∃ B : ℝ, 0 < B ∧ ∀ t, 0 < t → t ≤ T →
      (∫ x, formNormSq g.form (U t) x ∂μ) ≤ B := by
  obtain ⟨B, hB, hb⟩ := hU.2.2.2.2.2.2 T hT
  refine ⟨B, hB, ?_⟩
  intro t ht htT
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb t ht htT)
  have he := ofReal_integral_eq_lintegral_ofReal
    (L03.formNormSq_integrable g μ (U t) (hU.2.2.2.2.1 t ht))
    (ae_of_all _ (fun x => L03.formNormSq_nonneg g.form (U t) x))
  rw [← he, ENNReal.toReal_ofReal (integral_nonneg (fun x => L03.formNormSq_nonneg _ _ _)),
    ENNReal.toReal_ofReal hB.le] at hh
  exact hh

theorem l2FormHeat_difference_norm_integral_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    {A : RealForm M 2} {U V : ℝ → RealForm M 2}
    (hU : IsL2FormHeat g.form μ A U) (hV : IsL2FormHeat g.form μ A V)
    {T : ℝ} (hT : 0 < T) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t, 0 < t → t ≤ T →
      (∫ x, formNormSq g.form (U t - V t) x ∂μ) ≤ D := by
  obtain ⟨B, hB, hb⟩ := l2FormHeat_norm_integral_bound g μ hU hT
  obtain ⟨C, hC, hc⟩ := l2FormHeat_norm_integral_bound g μ hV hT
  refine ⟨2 * (B + C), by positivity, ?_⟩
  intro t ht htT
  exact (formUnique_integral_normSq_sub_le g μ (U t) (V t)
    (hU.2.2.2.2.1 t ht) (hV.2.2.2.2.1 t ht)).trans
      (mul_le_mul_of_nonneg_left (add_le_add (hb t ht htT) (hc t ht htT)) (by norm_num))

/-- The terminal inequality only needs the actual PDE, joint smoothness,
and the actual compact initial energy limit. -/
theorem formHeat_cutoff_energy_le_of_initial
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {U V : ℝ → RealForm M k}
    (hsU : SmoothFormTime U (Ioi 0)) (hsV : SmoothFormTime V (Ioi 0))
    (hU : FormHeatEquation g.form U) (hV : FormHeatEquation g.form V)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hinit : Tendsto (fun t => ∫ x, η x ^ 2 * formNormSq g.form (U t - V t) x ∂μ)
      (𝓝[>] 0) (𝓝 0))
    {Q T : ℝ} (hQ : 0 ≤ Q) (hT : 0 < T)
    (herror : ∀ s, 0 < s → s ≤ T →
      (∫ x, L18Aux.scalarGradientPair g.form η η x * formNormSq g.form (U s - V s) x ∂μ) ≤ Q) :
    ∀ t, 0 < t → t ≤ T →
      (∫ x, η x ^ 2 * formNormSq g.form (U t - V t) x ∂μ) ≤ 2 * T * Q := by
  intro t ht htT
  let F := fun s => ∫ x, η x ^ 2 * formNormSq g.form (U s - V s) x ∂μ
  let D := fun s => -(∫ x, η x ^ 2 * formInner g.form
    (L03.hodgeRealForm g.form k (U s - V s)) (U s - V s) x ∂μ)
  have hd (s : ℝ) (hs : 0 < s) : HasDerivAt F (D s) s :=
    formHeat_difference_cutoff_hasDerivAt g μ hμ hsU hsV hU hV hη hcη hs
  have hlim := hinit.add_const (2 * T * Q)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa only [zero_add] using hlim)
  filter_upwards [Ioo_mem_nhdsGT ht] with s hs
  have hslab : Icc s t ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le hs.1 hr.1
  have hDF : ∀ r ∈ Icc s t, D r ≤ Q := by
    intro r hr
    exact (integral_hodge_cutoff_generator_le g μ hμ η hη hcη (U r - V r)
      (smoothFormTime_slice (smoothFormTime_sub hsU hsV) (hslab hr))).trans
        (herror r (hslab hr) (hr.2.trans htT))
  have hmono : MonotoneOn (fun r => Q * r - F r) (Icc s t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc s t)
    · intro r hr
      exact ((hasDerivAt_id r).const_mul Q |>.sub (hd r (hslab hr))).continuousAt.continuousWithinAt
    · intro r hr
      exact ((hasDerivAt_id r).const_mul Q |>.sub (hd r (hslab (interior_subset hr)))).differentiableAt.differentiableWithinAt
    · intro r hr
      have hDr : HasDerivAt (fun y => Q * y - F y) (Q - D r) r := by
        with_unfolding_all
          simpa only [id_eq, mul_one, Pi.sub_def, Pi.sub_apply] using
            ((hasDerivAt_id r).const_mul Q |>.sub (hd r (hslab (interior_subset hr))))
      rw [hDr.deriv]
      exact sub_nonneg.mpr (hDF r (interior_subset hr))
  have hh := hmono (left_mem_Icc.mpr hs.2.le) (right_mem_Icc.mpr hs.2.le) hs.2.le
  have htime : (t - s) * Q ≤ 2 * T * Q := mul_le_mul_of_nonneg_right (by linarith [hs.1]) hQ
  change F t ≤ F s + 2 * T * Q
  linarith

end Yau.NodeProofs.P06Aux
