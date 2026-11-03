import Yau.Proofs.P06ExteriorHeatLocalGreen

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ContDiff

namespace Yau.NodeProofs.P06Aux.ExteriorHeat
open Yau Yau.Blueprint Yau.LeafProofs L03
variable {n : ℕ} {M : ComplexManifold n}

/-- A compact chart test has a uniform coefficient-to-pairing bound,
for every raw form in its first slot. -/
theorem compact_chart_pairing_control (g : SmoothMetric M) (x : M.Carrier)
    (B : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (hBx : closure {y | B y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    ∃ K : Set (ComplexVector n), IsCompact K ∧ K ⊆ chartTarget x ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (F : RealForm M 2) (ε : ℝ), 0 ≤ ε →
        (∀ z ∈ K, ∀ I : Fin 2 → RIdx n, |formComponents F x z I| ≤ ε) →
        ∀ y, |formInner g.form F B y| ≤ ε*C := by
  classical
  let K := chartPt x '' closure {y | B y ≠ 0}
  have hK : IsCompact K := hcB.image_of_continuousOn (by
    have hp : ContinuousOn (chartPt x) (extChartAt (ComplexModel n) x).source := by
      simpa only [extChartAt_source] using chartPt_continuousOn x
    exact hp.mono hBx)
  have hKO : K ⊆ chartTarget x := by
    rintro z ⟨y,hy,rfl⟩
    exact (extChartAt (ComplexModel n) x).map_source (hBx hy)
  let W : ComplexVector n → ℝ := fun z => |(Nat.factorial 2 : ℝ)⁻¹| *
    ∑ I : Fin 2 → RIdx n, ∑ J : Fin 2 → RIdx n,
      |formComponents B x z J * ∏ a, (realMetricFn g.form x z)⁻¹ (I a) (J a)|
  have hW : ContinuousOn W K := by
    apply continuousOn_const.mul
    apply continuousOn_finsetSum
    intro I _
    apply continuousOn_finsetSum
    intro J _
    apply ContinuousOn.abs
    apply ((hB x J).continuousOn.mono hKO).mul
    apply continuousOn_finsetProd
    intro a _
    exact (L18Aux.realMetricFn_inverse_contDiffOn g x (I a) (J a)).continuousOn.mono hKO
  obtain ⟨c,hc⟩ := hK.bddAbove_image hW
  let C := max c 0 + 1
  have hC : 0 < C := by dsimp only [C]; linarith [le_max_right c 0]
  refine ⟨K,hK,hKO,C,hC,?_⟩
  intro F ε hε hF y
  by_cases hy : y ∈ closure {y | B y ≠ 0}
  · let z := chartPt x y
    have hzK : z ∈ K := ⟨y,hy,rfl⟩
    have hinv : chartInv x z = y := (extChartAt (ComplexModel n) x).left_inv (hBx hy)
    have hterm (I J : Fin 2 → RIdx n) :
        |formComponents F x z I * formComponents B x z J *
          ∏ a, (realMetricFn g.form x z)⁻¹ (I a) (J a)| ≤
          ε * |formComponents B x z J * ∏ a, (realMetricFn g.form x z)⁻¹ (I a) (J a)| := by
      rw [mul_assoc,abs_mul]
      exact mul_le_mul_of_nonneg_right (hF z hzK I) (abs_nonneg _)
    have hb : |formInner g.form F B y| ≤ ε * W z := by
      rw [← hinv,formInner_chartInv_eq_tensorPairing g.form F B x (hKO hzK),abs_mul]
      dsimp only [tensorCoefficientPairing]
      apply le_trans (mul_le_mul_of_nonneg_left
        ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun I _ => Finset.abs_sum_le_sum_abs _ _))) (abs_nonneg _))
      calc
        _ ≤ |(Nat.factorial 2 : ℝ)⁻¹| * ∑ I : Fin 2 → RIdx n, ∑ J : Fin 2 → RIdx n,
            ε * |formComponents B x z J * ∏ a, (realMetricFn g.form x z)⁻¹ (I a) (J a)| := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun J _ => hterm I J
        _ = ε * W z := by dsimp only [W]; simp_rw [← Finset.mul_sum]; ring
    exact hb.trans (mul_le_mul_of_nonneg_left
      ((hc ⟨z,hzK,rfl⟩).trans (by dsimp only [C]; linarith [le_max_left c 0])) hε)
  · have hBy : B y = 0 := by by_contra h; exact hy (subset_closure h)
    rw [formInner_congr_at g.form (A := F) (B' := (0 : RealForm M 2)) rfl hBy,
      formInner_zero_right]
    simpa only [Pi.zero_apply,abs_zero] using mul_nonneg hε hC.le

/-- The m=0 clause suffices for compact test integrals at a fixed positive time. -/
theorem localSmoothLimit_compact_pairing_tendsto
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Us : ℕ → ℝ → RealForm M 2) (U : ℝ → RealForm M 2)
    (hUs : ∀ j, 1 ≤ j → ∀ t, 0 < t → L2RealForm g.form μ (Us j t))
    (hU : ∀ t, 0 < t → SmoothRealForm (U t)) (hlimit : FormHeatLocalSmoothLimit Us U)
    (B : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun j => ∫ y, formInner g.form (Us j t) B y ∂μ) atTop
      (𝓝 (∫ y, formInner g.form (U t) B y ∂μ)) := by
  classical
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  obtain ⟨s,p,hp,_,hps,hsum⟩ := L18Aux.exists_finite_smooth_partition hcB
  let Bs : s → RealForm M 2 := fun i => multiplyRealForm (p i) B
  have hsmooth (i : s) : SmoothRealForm (Bs i) := smoothRealForm_multiply _ _ (hp i) hB
  have hcompact (i : s) : CompactlySupportedRealForm (Bs i) := compactlySupportedRealForm_multiply _ _ hcB
  have hsumB : (∑ i, Bs i) = B := by
    funext y
    simp only [Finset.sum_apply,Bs,multiplyRealForm]
    rw [← Finset.sum_smul]
    by_cases hy : B y = 0
    · simp only [hy,smul_zero]
    · rw [hsum y (subset_closure hy),one_smul]
  have hlocal (i : s) : Tendsto (fun j => ∫ y, formInner g.form (Us j t) (Bs i) y ∂μ) atTop
      (𝓝 (∫ y, formInner g.form (U t) (Bs i) y ∂μ)) := by
    obtain ⟨K,hK,hKO,C,hC,hbound⟩ := compact_chart_pairing_control g i (Bs i) (hsmooth i) (hcompact i)
      ((multiplyRealForm_support_subset_scalar (p i) B).trans (hps i))
    have hnorm : Tendsto (fun j => ∫ y, formInner g.form (Us j t - U t) (Bs i) y ∂μ) atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      let δ := ε / (C * (μ.real (closure {y | Bs i y ≠ 0}) + 1))
      have hδ : 0 < δ := by dsimp only [δ]; positivity
      have hev (I : Fin 2 → RIdx n) : ∀ᶠ j in atTop, ∀ z ∈ K,
          |formComponents (Us j t - U t) i z I| ≤ δ := by
        obtain ⟨J,hJ⟩ := hlimit i K hK hKO (t/2) (2*t) (half_pos ht) (by linarith) 0 I δ hδ
        filter_upwards [eventually_ge_atTop J] with j hj z hz
        have hh := hJ j hj z hz t (show t ∈ Set.Icc (t/2) (2*t) by constructor <;> linarith)
        simpa only [norm_iteratedFDeriv_zero, formComponents,Pi.sub_apply,ContinuousAlternatingMap.sub_apply,Real.norm_eq_abs] using hh.le
      have hall : ∀ᶠ j in atTop, ∀ I : Fin 2 → RIdx n, ∀ z ∈ K,
          |formComponents (Us j t - U t) i z I| ≤ δ := Filter.eventually_all.mpr hev
      filter_upwards [hall] with j hj
      have hpt := hbound (Us j t - U t) δ hδ.le (fun z hz I => hj I z hz)
      have heq : (∫ y in closure {y | Bs i y ≠ 0}, formInner g.form (Us j t - U t) (Bs i) y ∂μ) =
          ∫ y, formInner g.form (Us j t - U t) (Bs i) y ∂μ := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        rw [formInner_symm]
        apply formInner_eq_zero_of_left_eq_zero
        by_contra h
        exact hy (subset_closure h)
      have hh := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := formInner g.form (Us j t - U t) (Bs i))
        (C := δ*C) (hcompact i).measure_lt_top
        (fun y _ => by simpa only [Real.norm_eq_abs] using hpt y)
      rw [heq] at hh
      rw [dist_zero_right]
      apply hh.trans_lt
      dsimp only [δ]
      have hm : 0 ≤ μ.real (closure {y | Bs i y ≠ 0}) := ENNReal.toReal_nonneg
      have hd : 0 < C * (μ.real (closure {y | Bs i y ≠ 0}) + 1) := by positivity
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    have hi (j : ℕ) (hj : 1 ≤ j) : Integrable (formInner g.form (Us j t) (Bs i)) μ :=
      formInner_integrable g μ _ _ (hUs j hj t ht)
        (smooth_compactlySupported_l2RealForm g μ hμ _ (hsmooth i) (hcompact i))
    have hiU : Integrable (formInner g.form (U t) (Bs i)) μ := by
      rw [formInner_symm]
      exact smooth_compact_formInner_integrable g μ hμ _ _ (hsmooth i) (hU t ht) (hcompact i)
    have he : ∀ᶠ j in atTop, (∫ y, formInner g.form (Us j t - U t) (Bs i) y ∂μ) =
        (∫ y, formInner g.form (Us j t) (Bs i) y ∂μ) -
          ∫ y, formInner g.form (U t) (Bs i) y ∂μ := by
      filter_upwards [eventually_ge_atTop 1] with j hj
      rw [formInner_sub_left]
      exact integral_sub (hi j hj) hiU
    have hh := (hnorm.congr' he).add_const (∫ y, formInner g.form (U t) (Bs i) y ∂μ)
    simpa only [sub_add_cancel,zero_add] using hh
  have heq (F : RealForm M 2)
      (hF : ∀ i : s, Integrable (formInner g.form F (Bs i)) μ) :
      (∫ y, formInner g.form F B y ∂μ) = ∑ i : s, ∫ y, formInner g.form F (Bs i) y ∂μ := by
    rw [formInner_symm]
    conv_lhs => rw [← hsumB]
    simp_rw [formInner_fintypeSum_left]
    simp_rw [formInner_symm g.form (Bs _) F]
    exact integral_finset_sum _ (fun i _ => hF i)
  have hfinal := tendsto_finsetSum Finset.univ (fun i _ => hlocal i)
  have htarget := heq (U t) (fun i => by
    rw [formInner_symm]
    exact smooth_compact_formInner_integrable g μ hμ _ _ (hsmooth i) (hU t ht) (hcompact i))
  rw [← htarget] at hfinal
  apply hfinal.congr'
  filter_upwards [eventually_ge_atTop 1] with j hj
  exact (heq (Us j t) (fun i => formInner_integrable g μ _ _ (hUs j hj t ht)
    (smooth_compactlySupported_l2RealForm g μ hμ _ (hsmooth i) (hcompact i)))).symm

end Yau.NodeProofs.P06Aux.ExteriorHeat
