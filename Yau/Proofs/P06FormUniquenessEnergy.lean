import Yau.Proofs.P06FormUniquenessIMS

/-! Terminal local energy for arbitrary solutions of the original form PDE. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n k : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem hodgeRealForm_sub (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) :
    L03.hodgeRealForm g.form k (A - B) =
      L03.hodgeRealForm g.form k A - L03.hodgeRealForm g.form k B := by
  have he : A - B = A + (-1 : ℝ) • B := by rw [neg_one_smul ℝ B, sub_eq_add_neg]
  rw [he, L03.hodgeRealForm_add g μ hμ A _ hA (L03.smoothRealForm_smul _ B hB),
    L03.hodgeRealForm_smul g μ hμ _ B hB,
    neg_one_smul ℝ (L03.hodgeRealForm g.form k B), sub_eq_add_neg]

/-- Differentiating the actual metric norm is a finite coefficient
calculation in a fixed tangent fibre. -/
theorem formNormSq_hasDerivAt (g : HermitianField M)
    (U : ℝ → RealForm M k) (W : RealForm M k) (x : M.Carrier) (t : ℝ)
    (hD : ∀ I, HasDerivAt (fun s => formComponents (U s) x (chartPt x x) I)
      (formComponents W x (chartPt x x) I) t) :
    HasDerivAt (fun s => formNormSq g (U s) x)
      (2 * formInner g W (U t) x) t := by
  classical
  have hh := (HasDerivAt.fun_sum (u := Finset.univ) (fun I _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun J _ =>
      ((hD I).mul (hD J)).mul_const
        (∏ r, (realMetricFn g x (chartPt x x))⁻¹ (I r) (J r))))).const_mul
          (Nat.factorial k : ℝ)⁻¹
  have hd : HasDerivAt (fun s => formNormSq g (U s) x)
      (formInner g W (U t) x + formInner g (U t) W x) t := by
    with_unfolding_all
      convert hh using 1 <;>
        simp [formNormSq, formInner, add_mul, Finset.sum_add_distrib, mul_add]
  convert hd using 1
  rw [congrFun (L03.formInner_symm g (U t) W) x]
  ring

theorem formHeat_difference_normSq_hasDerivAt
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {U V : ℝ → RealForm M k}
    (hsU : SmoothFormTime U (Ioi 0)) (hsV : SmoothFormTime V (Ioi 0))
    (hU : FormHeatEquation g.form U) (hV : FormHeatEquation g.form V)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => formNormSq g.form (U s - V s) x)
      (-formInner g.form (L03.hodgeRealForm g.form k (U t - V t)) (U t - V t) x) t := by
  let W := (- (1 / 2 : ℝ)) • L03.hodgeRealForm g.form k (U t - V t)
  have hUs := smoothFormTime_slice hsU ht
  have hVs := smoothFormTime_slice hsV ht
  have hDz := formNormSq_hasDerivAt g.form (fun s => U s - V s) W x t (fun I => by
    have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
    have hrepU := L03.hodgeRealForm_represents g μ hμ (U t) hUs x _ hz I
    have hrepV := L03.hodgeRealForm_represents g μ hμ (V t) hVs x _ hz I
    have hh := (hU x _ hz t ht I).sub (hV x _ hz t ht I)
    have hh' : HasDerivAt
        (fun s => formComponents (U s - V s) x (chartPt x x) I)
        (hodgeGeneratorComponents g.form x (formComponents (U t) x) (chartPt x x) I -
          hodgeGeneratorComponents g.form x (formComponents (V t) x) (chartPt x x) I) t := by
      with_unfolding_all
        simpa only [formComponents, Pi.sub_def, Pi.sub_apply, ContinuousAlternatingMap.sub_apply] using hh
    apply hh'.congr_deriv
    simp only [W, hodgeRealForm_sub g μ hμ _ _ hUs hVs,
      L03.formComponents_smul, Pi.smul_apply, smul_eq_mul, formComponents,
      Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
      ContinuousAlternatingMap.smul_apply] at hrepU hrepV ⊢
    dsimp only [hodgeGeneratorComponents]
    rw [← hrepU, ← hrepV]
    ring)
  convert hDz using 1
  simp only [W, L03.formInner_smul_left, Pi.smul_apply, smul_eq_mul]
  ring

theorem formHeat_difference_cutoff_hasDerivAt
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {U V : ℝ → RealForm M k}
    (hsU : SmoothFormTime U (Ioi 0)) (hsV : SmoothFormTime V (Ioi 0))
    (hU : FormHeatEquation g.form U) (hV : FormHeatEquation g.form V)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, η x ^ 2 * formNormSq g.form (U s - V s) x ∂μ)
      (-(∫ x, η x ^ 2 * formInner g.form
        (L03.hodgeRealForm g.form k (U t - V t)) (U t - V t) x ∂μ)) t := by
  let N := fun x s => formNormSq g.form (U s - V s) x
  have hN : SmoothSpaceTime N (Ioi 0) := smoothFormTime_normSq g (smoothFormTime_sub hsU hsV)
  have hηt : SmoothSpaceTime (fun x (_t : ℝ) => η x) (Ioi 0) :=
    L19Aux.LocalTime.smoothSpaceTime_spatial_const isOpen_Ioi hη
  have hv : SmoothSpaceTime (fun x s => η x ^ 2 * N x s) (Ioi 0) :=
    fun x => ((hηt x).pow 2).mul (hN x)
  have hw : SmoothSpaceTime (fun x s => η x ^ 2 * deriv (N x) s) (Ioi 0) :=
    fun x => ((hηt x).pow 2).mul (L19Aux.LocalTime.smoothSpaceTime_time_derivative isOpen_Ioi hN x)
  have hh := (L19Aux.LocalTime.smoothSpaceTime_compact_integral_hasDerivAt
    isOpen_Ioi g μ hμ hv hw hcη
    (fun x s _ hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    (fun x s _ hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    (fun x s hs => (formHeat_difference_normSq_hasDerivAt g μ hμ hsU hsV hU hV x hs).const_mul (η x ^ 2)
      |>.congr_deriv (by rw [(formHeat_difference_normSq_hasDerivAt g μ hμ hsU hsV hU hV x hs).deriv])) ht).2.2
  convert hh using 1
  rw [← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only [N]
    rw [(formHeat_difference_normSq_hasDerivAt g μ hμ hsU hsV hU hV x ht).deriv]
    ring)

/-- The terminal energy is retained when the initial compact energy is
sent to zero. The estimate applies to arbitrary original PDE solutions. -/
theorem boundedFormHeat_difference_cutoff_energy_le
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {A : RealForm M k} {U V : ℝ → RealForm M k}
    (hU : IsBoundedFormHeat g.form A U) (hV : IsBoundedFormHeat g.form A V)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hηbound : ∀ x, |η x| ≤ 1)
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
    formHeat_difference_cutoff_hasDerivAt g μ hμ hU.1 hV.1 hU.2.2.2 hV.2.2.2 hη hcη hs
  have hlim := (boundedFormHeat_difference_cutoff_tendsto_zero g μ hμ hU hV hη hcη hηbound).add_const (2 * T * Q)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa only [zero_add] using hlim)
  filter_upwards [Ioo_mem_nhdsGT ht] with s hs
  have hslab : Icc s t ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le hs.1 hr.1
  have hDF : ∀ r ∈ Icc s t, D r ≤ Q := by
    intro r hr
    exact (integral_hodge_cutoff_generator_le g μ hμ η hη hcη (U r - V r)
      (smoothFormTime_slice (smoothFormTime_sub hU.1 hV.1) (hslab hr))).trans
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
