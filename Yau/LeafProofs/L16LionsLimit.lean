import Yau.LeafProofs.L16HilbertTimeRegularization
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! Strong smooth approximation gives the Lions closed-time Hilbert trace and
its energy identity. All convergence hypotheses are actual squared Bochner integrals. -/

open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Yau.LeafProofs.L16LionsLimit

open Yau.LeafProofs.L16HilbertTimeRegularization

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem sq_sub_le {E : Type*} [NormedAddCommGroup E] (x y u : E) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x - u‖ ^ 2 + 2 * ‖y - u‖ ^ 2 := by
  have hn : ‖x - y‖ ≤ ‖x - u‖ + ‖y - u‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (x - u) (y - u)
  nlinarith [sq_nonneg (‖x - u‖ - ‖y - u‖), norm_nonneg (x - y), norm_nonneg (x-u), norm_nonneg (y-u)]

/-- Genuine strong L² convergence implies the quantitative integral Cauchy condition. -/
theorem strongL2_integral_cauchy {E : Type*} [NormedAddCommGroup E]
    {μ : Measure ℝ} {f : ℕ → ℝ → E} {u : ℝ → E}
    (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun n => ∫ r, ‖f n r - u r‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫ r, ‖f n r - f m r‖ ^ 2 ∂μ) ≤ ε := by
  intro ε hε
  have he := (tendsto_order.1 hlim).2 (ε / 4) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨N, fun n hn m hm => ?_⟩
  have hi (n : ℕ) : Integrable (fun r => ‖f n r - u r‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm ((hf n).sub hu).aestronglyMeasurable).1 ((hf n).sub hu)
  have hij := (memLp_two_iff_integrable_sq_norm ((hf n).sub (hf m)).aestronglyMeasurable).1 ((hf n).sub (hf m))
  have hb := integral_mono hij (((hi n).const_mul 2).add ((hi m).const_mul 2))
    (fun r => sq_sub_le (f n r) (f m r) (u r))
  simp only [Pi.add_apply, Pi.sub_apply] at hb
  rw [integral_add ((hi n).const_mul 2) ((hi m).const_mul 2), integral_const_mul, integral_const_mul] at hb
  linarith [hN n hn, hN m hm]

private theorem eval_integrable {μ : Measure ℝ} {f : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun r => g r (f r)) μ := by
  have hm : AEStronglyMeasurable (fun r => g r (f r)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hg.aestronglyMeasurable.prodMk hf.aestronglyMeasurable)
  exact (hg.norm.integrable_mul hf.norm).mono' hm (ae_of_all μ fun r => (g r).le_opNorm (f r))

/-- Products of a strongly converging L² primal/dual pair converge in L¹. -/
theorem strongL2_duality_L1 {μ : Measure ℝ}
    {z : ℕ → ℝ → V} {Q : ℕ → ℝ → StrongDual ℝ V}
    {U : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hz : ∀ n, MemLp (z n) 2 μ) (hQ : ∀ n, MemLp (Q n) 2 μ)
    (hU : MemLp U 2 μ) (hR : MemLp R 2 μ)
    (hzlim : Tendsto (fun n => ∫ r, ‖z n r - U r‖ ^ 2 ∂μ) atTop (𝓝 0))
    (hQlim : Tendsto (fun n => ∫ r, ‖Q n r - R r‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ r, ‖Q n r (z n r) - R r (U r)‖ ∂μ) atTop (𝓝 0) := by
  have ha := (Real.continuous_sqrt.tendsto 0).comp hzlim
  have hb := (Real.continuous_sqrt.tendsto 0).comp hQlim
  simp only [Real.sqrt_zero] at ha hb
  have hbound (n : ℕ) :
      (∫ r, ‖Q n r (z n r) - R r (U r)‖ ∂μ) ≤
        Real.sqrt (∫ r, ‖Q n r - R r‖ ^ 2 ∂μ) * Real.sqrt (∫ r, ‖z n r - U r‖ ^ 2 ∂μ) +
        Real.sqrt (∫ r, ‖Q n r - R r‖ ^ 2 ∂μ) * Real.sqrt (∫ r, ‖U r‖ ^ 2 ∂μ) +
        Real.sqrt (∫ r, ‖R r‖ ^ 2 ∂μ) * Real.sqrt (∫ r, ‖z n r - U r‖ ^ 2 ∂μ) := by
    have h1 := (hQ n).sub hR
    have h2 := (hz n).sub hU
    have hi1 : Integrable (fun r => ‖Q n r - R r‖ * ‖z n r - U r‖) μ := h1.norm.integrable_mul h2.norm
    have hi2 : Integrable (fun r => ‖Q n r - R r‖ * ‖U r‖) μ := h1.norm.integrable_mul hU.norm
    have hi3 : Integrable (fun r => ‖R r‖ * ‖z n r - U r‖) μ := hR.norm.integrable_mul h2.norm
    have hp (r : ℝ) :
        ‖Q n r (z n r) - R r (U r)‖ ≤
        ‖Q n r - R r‖ * ‖z n r - U r‖ + ‖Q n r - R r‖ * ‖U r‖ + ‖R r‖ * ‖z n r - U r‖ := by
      have he : Q n r (z n r) - R r (U r) =
          (Q n r - R r) (z n r - U r) + (Q n r - R r) (U r) + R r (z n r - U r) := by
        simp only [sub_apply, map_sub]
        ring
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add ((Q n r - R r).le_opNorm _) ((Q n r - R r).le_opNorm _))) ((R r).le_opNorm _))
    have hi := ((eval_integrable (hz n) (hQ n)).sub (eval_integrable hU hR)).norm
    have h := integral_mono hi ((hi1.add hi2).add hi3) hp
    simp only [Pi.add_apply, Pi.sub_apply] at h
    rw [integral_add (show Integrable (fun r => ‖Q n r - R r‖ * ‖z n r - U r‖ + ‖Q n r - R r‖ * ‖U r‖) μ from hi1.add hi2) hi3, integral_add hi1 hi2] at h
    exact h.trans (add_le_add (add_le_add (integral_norm_mul_le h1 h2) (integral_norm_mul_le h1 hU))
      (integral_norm_mul_le hR h2))
  apply squeeze_zero (fun n => integral_nonneg fun _ => norm_nonneg _) hbound
  simpa only [Function.comp_def, zero_mul, mul_zero, add_zero] using
    ((hb.mul ha).add (hb.mul_const (Real.sqrt (∫ r, ‖U r‖ ^ 2 ∂μ)))).add
      (ha.const_mul (Real.sqrt (∫ r, ‖R r‖ ^ 2 ∂μ)))


/-- An a.e. pointwise limit of actual strong L² approximants is their L² limit. -/
theorem ae_eq_of_pointwise_of_strongL2 {E : Type*} [NormedAddCommGroup E]
    {μ : Measure ℝ} {f : ℕ → ℝ → E} {u v : ℝ → E}
    (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ)
    (hv : AEStronglyMeasurable v μ)
    (hp : ∀ᵐ r ∂μ, Tendsto (fun n => f n r) atTop (𝓝 (v r)))
    (hL2 : Tendsto (fun n => ∫ r, ‖f n r - u r‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    v =ᵐ[μ] u := by
  have hi (n : ℕ) : Integrable (fun r => ‖f n r - u r‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm ((hf n).sub hu).aestronglyMeasurable).1 ((hf n).sub hu)
  have hm (n : ℕ) : AEMeasurable (fun r => ENNReal.ofReal (‖f n r - u r‖ ^ 2)) μ :=
    ((((hf n).aestronglyMeasurable.sub hu.aestronglyMeasurable).norm).pow 2).aemeasurable.ennreal_ofReal
  have ht : ∀ᵐ r ∂μ, Tendsto (fun n => ENNReal.ofReal (‖f n r - u r‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (‖v r - u r‖ ^ 2))) := by
    filter_upwards [hp] with r hr
    exact ENNReal.tendsto_ofReal (((hr.sub tendsto_const_nhds).norm).pow 2)
  have hli : Tendsto (fun n => ∫⁻ r, ENNReal.ofReal (‖f n r - u r‖ ^ 2) ∂μ) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hL2
    simp only [ENNReal.ofReal_zero] at h
    convert h using 1
    funext n
    exact (ofReal_integral_eq_lintegral_ofReal (hi n) (ae_of_all μ fun r => sq_nonneg _)).symm
  have hz : (∫⁻ r, ENNReal.ofReal (‖v r - u r‖ ^ 2) ∂μ) = 0 := by
    apply le_antisymm _ bot_le
    calc
      _ = ∫⁻ r, liminf (fun n => ENNReal.ofReal (‖f n r - u r‖ ^ 2)) atTop ∂μ :=
        lintegral_congr_ae (ht.mono fun r hr => hr.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ r, ENNReal.ofReal (‖f n r - u r‖ ^ 2) ∂μ) atTop := lintegral_liminf_le' hm
      _ = 0 := hli.liminf_eq
  have hmv : AEMeasurable (fun r => ENNReal.ofReal (‖v r - u r‖ ^ 2)) μ :=
    (((hv.sub hu.aestronglyMeasurable).norm).pow 2).aemeasurable.ennreal_ofReal
  filter_upwards [(lintegral_eq_zero_iff' hmv).1 hz] with r hr
  have hs : ‖v r - u r‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.1 hr
  exact sub_eq_zero.1 (norm_eq_zero.1 (by nlinarith [norm_nonneg (v r - u r)]))

private theorem interval_integral_eq_Ioo {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ) :
    (∫ r in (0 : ℝ)..T, f r) = ∫ r in Ioo 0 T, f r := by
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioo]

/-- L¹ convergence on the open slab controls every oriented closed-time integral. -/
theorem intervalIntegral_tendsto_of_L1 {T : ℝ} {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, IntegrableOn (f n) (Ioo 0 T)) (hg : IntegrableOn g (Ioo 0 T))
    (hlim : Tendsto (fun n => ∫ r in Ioo 0 T, ‖f n r - g r‖) atTop (𝓝 0))
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => ∫ r in s..t, f n r) atTop (𝓝 (∫ r in s..t, g r)) := by
  have hsub := uIcc_subset_Icc hs ht
  have hfi (n : ℕ) : IntegrableOn (f n) (Icc 0 T) := by
    simpa only [IntegrableOn, restrict_Ioo_eq_restrict_Icc] using hf n
  have hgi : IntegrableOn g (Icc 0 T) := by
    simpa only [IntegrableOn, restrict_Ioo_eq_restrict_Icc] using hg
  have hi (n : ℕ) := ((hfi n).mono_set hsub).intervalIntegrable
  have hj := (hgi.mono_set hsub).intervalIntegrable
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun n => norm_nonneg _) _ hlim
  intro n
  rw [← intervalIntegral.integral_sub (hi n) hj]
  calc
    _ ≤ ∫ r in uIoc s t, ‖f n r - g r‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ r in Icc 0 T, ‖f n r - g r‖ :=
      setIntegral_mono_set (((hfi n).sub hgi).norm)
        (ae_of_all _ fun r => norm_nonneg _) (uIoc_subset_uIcc.trans hsub).eventuallySubset
    _ = ∫ r in Ioo 0 T, ‖f n r - g r‖ := integral_Icc_eq_integral_Ioo

/-- Smooth approximants with their actual pivot derivatives and genuine strong
L² limits produce a continuous Hilbert representative and the all-closed-time energy chain. -/
theorem smooth_approximation_trace_chain [CompleteSpace H]
    (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1) {T : ℝ} (hT : 0 < T)
    {U : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    {z : ℕ → ℝ → V} {Q : ℕ → ℝ → StrongDual ℝ V}
    (hz : ∀ n, ContDiff ℝ 1 (z n)) (hQc : ∀ n, ContinuousOn (Q n) (Icc 0 T))
    (hd : ∀ n, ∀ r ∈ Icc 0 T, hilbertEmbedding j (deriv (z n) r) = Q n r)
    (hzlim : Tendsto (fun n => ∫ r in Ioo 0 T, ‖z n r - U r‖ ^ 2) atTop (𝓝 0))
    (hQlim : Tendsto (fun n => ∫ r in Ioo 0 T, ‖Q n r - R r‖ ^ 2) atTop (𝓝 0)) :
    ∃ u : ℝ → H, ContinuousOn u (Icc 0 T) ∧
      (∀ᵐ r ∂volume.restrict (Ioo 0 T), j (U r) = u r) ∧
      TendstoUniformlyOn (fun n r => j (z n r)) u atTop (Icc 0 T) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        ‖u t‖ ^ 2 - ‖u s‖ ^ 2 = 2 * ∫ r in s..t, R r (U r)) := by
  have hzLp (n : ℕ) : MemLp (z n) 2 (volume.restrict (Ioo 0 T)) := by
    rw [restrict_Ioo_eq_restrict_Icc]
    exact continuousOn_memLp_two (hz n).continuous.continuousOn
  have hQLp (n : ℕ) : MemLp (Q n) 2 (volume.restrict (Ioo 0 T)) := by
    rw [restrict_Ioo_eq_restrict_Icc]
    exact continuousOn_memLp_two (hQc n)
  have hC : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫ r in (0 : ℝ)..T, ‖z n r - z m r‖ ^ 2) ≤ ε ∧
      (∫ r in (0 : ℝ)..T, ‖Q n r - Q m r‖ ^ 2) ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := strongL2_integral_cauchy hzLp hU hzlim ε hε
    obtain ⟨M, hM⟩ := strongL2_integral_cauchy hQLp hR hQlim ε hε
    refine ⟨max N M, fun n hn m hm => ?_⟩
    simp only [interval_integral_eq_Ioo hT.le]
    exact ⟨hN n (le_trans (le_max_left _ _) hn) m (le_trans (le_max_left _ _) hm),
      hM n (le_trans (le_max_right _ _) hn) m (le_trans (le_max_right _ _) hm)⟩
  obtain ⟨u, hu, hzu⟩ := smooth_hilbert_continuous_limit j hj hT hz hQc hd hC
  have hn (v : V) : ‖j v‖ ≤ ‖v‖ := by
    exact (j.le_opNorm v).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hj (norm_nonneg v))
  have hjuLp := hU.continuousLinearMap_comp j
  have hjzLp (n : ℕ) := (hzLp n).continuousLinearMap_comp j
  have hjlim : Tendsto (fun n => ∫ r in Ioo 0 T, ‖j (z n r) - j (U r)‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg fun r => sq_nonneg _) _ hzlim
    intro n
    apply integral_mono
    · exact (memLp_two_iff_integrable_sq_norm ((hjzLp n).sub hjuLp).aestronglyMeasurable).1 ((hjzLp n).sub hjuLp)
    · exact (memLp_two_iff_integrable_sq_norm ((hzLp n).sub hU).aestronglyMeasurable).1 ((hzLp n).sub hU)
    · intro r
      change ‖j (z n r) - j (U r)‖ ^ 2 ≤ ‖z n r - U r‖ ^ 2
      rw [← map_sub]
      exact pow_le_pow_left₀ (norm_nonneg _) (hn _) 2
  have hum : AEStronglyMeasurable u (volume.restrict (Ioo 0 T)) := by
    rw [restrict_Ioo_eq_restrict_Icc]
    exact hu.aestronglyMeasurable measurableSet_Icc
  have hp : ∀ᵐ r ∂volume.restrict (Ioo 0 T), Tendsto (fun n => j (z n r)) atTop (𝓝 (u r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hzu.tendsto_at (Ioo_subset_Icc_self hr)
  have hae := (ae_eq_of_pointwise_of_strongL2 hjzLp hjuLp hum hp hjlim).symm
  refine ⟨u, hu, hae, hzu, ?_⟩
  intro s hs t ht
  have hprod := strongL2_duality_L1 hzLp hQLp hU hR hzlim hQlim
  have hInt := intervalIntegral_tendsto_of_L1 (fun n => eval_integrable (hzLp n) (hQLp n))
    (eval_integrable hU hR) hprod hs ht
  have hEnd := (((hzu.tendsto_at ht).norm).pow 2).sub (((hzu.tendsto_at hs).norm).pow 2)
  have he (n : ℕ) : ‖j (z n t)‖ ^ 2 - ‖j (z n s)‖ ^ 2 = 2 * ∫ r in s..t, Q n r (z n r) := by
    rw [← intervalIntegral.integral_const_mul]
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => hasDerivAt_energy j (hz n) (hd n r (uIcc_subset_Icc hs ht hr)))
      ((((hQc n).clm_apply (hz n).continuous.continuousOn).const_mul (2 : ℝ)).mono
        (uIcc_subset_Icc hs ht)).intervalIntegrable).symm
  exact tendsto_nhds_unique hEnd (by simpa only [he] using hInt.const_mul 2)

end Yau.LeafProofs.L16LionsLimit
