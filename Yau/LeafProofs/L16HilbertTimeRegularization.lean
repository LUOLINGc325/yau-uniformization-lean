import Yau.LeafProofs.L03
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Temporal regularization of a local Banach-valued weak derivative and the
classical smooth estimate used in the Hilbert triple trace construction. -/

open MeasureTheory Set Filter
open scoped Topology ContDiff InnerProductSpace Convolution

noncomputable section

namespace Yau.LeafProofs.L16HilbertTimeRegularization

section Banach
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The weak derivative identity is imposed only on tests supported inside `J`. -/
def LocalWeakDerivative (J : Set ℝ) (L : V →L[ℝ] E) (U : ℝ → V) (F : ℝ → E) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ J →
    (∫ s, deriv η s • L (U s)) = -(∫ s, η s • F s)

omit [CompleteSpace V] in
/-- A smooth compact kernel regularizes an arbitrary complete Banach-valued L² field. -/
theorem mollify_contDiff (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (U : ℝ → V) (hU : MemLp U 2 volume) :
    ContDiff ℝ ∞ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) :=
  hcρ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ
    (hU.locallyIntegrable (by norm_num))

/-- Convolution transports a local distributional derivative at every point whose
translated kernel support lies in the open region of the weak identity. -/
theorem localWeakDerivative_mollify (J : Set ℝ) (_hJ : IsOpen J)
    (L : V →L[ℝ] E) (U : ℝ → V) (F : ℝ → E)
    (hU : MemLp U 2 volume) (_hcU : HasCompactSupport U)
    (_hF : MemLp F 2 volume) (_hcF : HasCompactSupport F)
    (hweak : LocalWeakDerivative J L U F)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (t : ℝ) (ht : {s | t - s ∈ tsupport ρ} ⊆ J) :
    L (deriv (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) t) =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) t := by
  let ψ : ℝ → ℝ := fun s => ρ (t - s)
  have hψ : ContDiff ℝ ∞ ψ := hρ.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ := hcρ.comp_homeomorph (Homeomorph.subLeft t)
  have hsψ : tsupport ψ ⊆ J := by
    change tsupport (ρ ∘ (Homeomorph.subLeft t)) ⊆ J
    rw [tsupport_comp_eq_preimage]
    exact ht
  have hdψ (s : ℝ) : deriv ψ s = -(deriv ρ (t - s)) := by
    have hdρ : HasDerivAt ρ (deriv ρ (t - s)) (t - s) :=
      (hρ.differentiable (by simp)).differentiableAt.hasDerivAt
    simpa only [ψ, Function.comp_def, zero_sub, mul_neg_one] using
      (hdρ.comp s ((hasDerivAt_const s t).sub (hasDerivAt_id s))).deriv
  have hid := hweak ψ hψ hcψ hsψ
  simp_rw [hdψ, neg_smul] at hid
  rw [integral_neg] at hid
  have heq : (∫ s, deriv ρ (t - s) • L (U s)) = ∫ s, ρ (t - s) • F s :=
    neg_injective hid
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have hder := hcρ.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ1
    (hU.locallyIntegrable (by norm_num)) t
  have hi : Integrable (fun s => deriv ρ (t - s) • U s) volume := by
    simpa only [ContinuousLinearMap.lsmul_apply] using
      ((hcρ.deriv).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
        (hρ1.continuous_deriv le_rfl) (hU.locallyIntegrable (by norm_num)) t).integrable_swap
  rw [hder.deriv, convolution_lsmul_swap, convolution_lsmul_swap]
  rw [← L.integral_comp_comm hi]
  simpa only [map_smul] using heq

/-- The existing strong L² theorem applies without any finite dimensionality
assumption on the Banach-valued field. -/
theorem mollify_L2_tendsto (ρ : ℝ → ℝ) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρ1 : (∫ s, ρ s) = 1)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1)
    (ht : Tendsto ε atTop (𝓝 0)) (U : ℝ → V) (hU : MemLp U 2 volume)
    (hcU : HasCompactSupport U) :
    Tendsto (fun n => ∫ s,
      ‖(L03.rescaledFriedrichsMollifier ρ (ε n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) s - U s‖ ^ 2)
      atTop (𝓝 0) :=
  L03.rescaledFriedrichsMollifier_convolution_L2_tendsto_of_memLp volume ρ hρ hcρ hρ0 hρ1
    ε hε hε1 ht U hU hcU

/-- Normalized scalar temporal convolution is an L² contraction, using the
proved general Banach-valued probability convolution theorem. -/
theorem mollify_L2_bound (ρ : ℝ → ℝ) (hρ0 : ∀ s, 0 ≤ ρ s)
    (hρ1 : (∫ s, ρ s) = 1) (U : ℝ → V) (hU : MemLp U 2 volume)
    (hcU : HasCompactSupport U) :
    MemLp (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) 2 volume ∧
      (∫ s, ‖(ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) s‖ ^ 2) ≤ ∫ s, ‖U s‖ ^ 2 :=
  L03.probability_convolution_L2_bound volume ρ hρ0 hρ1 U
    (L03.memLp_two_compact_integrable volume U hU hcU)
    ((memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU)

/-- The transport theorem applies to the actual rescaled Friedrichs kernels. -/
theorem localWeakDerivative_rescaled_mollify (J : Set ℝ) (hJ : IsOpen J)
    (L : V →L[ℝ] E) (U : ℝ → V) (F : ℝ → E)
    (hU : MemLp U 2 volume) (hcU : HasCompactSupport U)
    (hF : MemLp F 2 volume) (hcF : HasCompactSupport F)
    (hweak : LocalWeakDerivative J L U F)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ)
    (ht : {s | t - s ∈ tsupport (L03.rescaledFriedrichsMollifier ρ ε)} ⊆ J) :
    L (deriv (L03.rescaledFriedrichsMollifier ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) t) =
      (L03.rescaledFriedrichsMollifier ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) t :=
  localWeakDerivative_mollify J hJ L U F hU hcU hF hcF hweak _
    (L03.rescaledFriedrichsMollifier_contDiff_top ρ ε hρ)
    (L03.rescaledFriedrichsMollifier_compact ρ hε.ne' hcρ) t ht

end Banach


section Hilbert
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The genuine Hilbert triple map, defined from the value projection. -/
def hilbertEmbedding (j : V →L[ℝ] H) : V →L[ℝ] StrongDual ℝ V :=
  ((ContinuousLinearMap.compL ℝ V H ℝ).flip j).comp ((innerSL ℝ).comp j)

@[simp] theorem hilbertEmbedding_apply (j : V →L[ℝ] H) (v w : V) :
    hilbertEmbedding j v w = inner ℝ (j v) (j w) := rfl

/-- The classical energy derivative follows from the actual curve derivative. -/
theorem hasDerivAt_energy (j : V →L[ℝ] H) {z : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hz : ContDiff ℝ 1 z) {t : ℝ} (hR : hilbertEmbedding j (deriv z t) = R t) :
    HasDerivAt (fun r => ‖j (z r)‖ ^ 2) (2 * R t (z t)) t := by
  have hd : HasDerivAt z (deriv z t) t := (hz.differentiable (by simp)).differentiableAt.hasDerivAt
  have h := (j.hasFDerivAt.comp_hasDerivAt t hd).norm_sq
  have he : R t (z t) = inner ℝ (j (z t)) (j (deriv z t)) := by
    rw [← hR, hilbertEmbedding_apply, real_inner_comm]
  simpa only [Function.comp_def, he] using h

/-- Cauchy--Schwarz for the actual squared Bochner norms. -/
theorem integral_norm_mul_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure ℝ} {f : ℝ → E} {g : ℝ → F}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ r, ‖f r‖ * ‖g r‖ ∂μ) ≤
      Real.sqrt (∫ r, ‖f r‖ ^ 2 ∂μ) * Real.sqrt (∫ r, ‖g r‖ ^ 2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp (fun r => ‖f r‖) (ENNReal.ofReal 2) μ by simpa using hf.norm)
    (show MemLp (fun r => ‖g r‖) (ENNReal.ofReal 2) μ by simpa using hg.norm)
  simpa only [norm_norm, Real.rpow_two, ← Real.sqrt_eq_rpow] using h

/-- Continuous curves on a compact time interval belong to the genuine Bochner L² space. -/
theorem continuousOn_memLp_two {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {T : ℝ} (hf : ContinuousOn f (Icc 0 T)) :
    MemLp f 2 (volume.restrict (Icc 0 T)) := by
  have ha : AEStronglyMeasurable f (volume.restrict (Icc 0 T)) :=
    hf.aestronglyMeasurable measurableSet_Icc
  exact (memLp_two_iff_integrable_sq_norm ha).mpr (hf.norm.pow 2).integrableOn_Icc

/-- The smooth Hilbert triple estimate, including both endpoints. -/
theorem smooth_hilbert_sup_estimate (j : V →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    {z : ℝ → V} {R : ℝ → StrongDual ℝ V} (hz : ContDiff ℝ 1 z)
    (hRc : ContinuousOn R (Icc 0 T))
    (hR : ∀ r ∈ Icc 0 T, hilbertEmbedding j (deriv z r) = R r)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖j (z t)‖ ^ 2 ≤ T⁻¹ * (∫ r in (0 : ℝ)..T, ‖j (z r)‖ ^ 2) +
      2 * Real.sqrt (∫ r in (0 : ℝ)..T, ‖z r‖ ^ 2) *
        Real.sqrt (∫ r in (0 : ℝ)..T, ‖R r‖ ^ 2) := by
  let y : ℝ → ℝ := fun r => ‖j (z r)‖ ^ 2
  have hy : Continuous y := (j.continuous.comp hz.continuous).norm.pow 2
  have hzC : ContinuousOn z (Icc 0 T) := hz.continuous.continuousOn
  have hpC : ContinuousOn (fun r => R r (z r)) (Icc 0 T) := hRc.clm_apply hzC
  have hprodC : ContinuousOn (fun r => ‖z r‖ * ‖R r‖) (Icc 0 T) := hzC.norm.mul hRc.norm
  have hprod : IntegrableOn (fun r => ‖z r‖ * ‖R r‖) (Icc 0 T) volume :=
    hprodC.integrableOn_Icc
  have hcs : (∫ r in Icc (0 : ℝ) T, ‖z r‖ * ‖R r‖) ≤
      Real.sqrt (∫ r in (0 : ℝ)..T, ‖z r‖ ^ 2) * Real.sqrt (∫ r in (0 : ℝ)..T, ‖R r‖ ^ 2) := by
    have hc := integral_norm_mul_le (continuousOn_memLp_two hzC) (continuousOn_memLp_two hRc)
    simpa only [intervalIntegral.integral_of_le hT.le, integral_Icc_eq_integral_Ioc] using hc
  obtain ⟨s, hs, hsmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT.le) hy.continuousOn
  have hsavg : y s ≤ T⁻¹ * ∫ r in (0 : ℝ)..T, y r := by
    have hm := intervalIntegral.integral_mono_on hT.le
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => y s) volume 0 T)
      (hy.intervalIntegrable 0 T) (fun r hr => hsmin hr)
    rw [intervalIntegral.integral_const] at hm
    simp only [sub_zero, smul_eq_mul] at hm
    exact (le_inv_mul_iff₀ hT).mpr hm
  have hst : uIcc s t ⊆ Icc 0 T := uIcc_subset_Icc hs ht
  have hFTC : (∫ r in s..t, 2 * R r (z r)) = y t - y s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => hasDerivAt_energy j hz (hR r (hst hr)))
      ((hpC.const_mul (2 : ℝ)).mono hst).intervalIntegrable
  have hosc : y t - y s ≤
      2 * (∫ r in Icc (0 : ℝ) T, ‖z r‖ * ‖R r‖) := by
    rw [← hFTC, intervalIntegral.integral_const_mul]
    have hbound : ‖∫ r in s..t, R r (z r)‖ ≤ ∫ r in Icc (0 : ℝ) T, ‖z r‖ * ‖R r‖ := by
      calc
        _ ≤ ∫ r in uIoc s t, ‖R r (z r)‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ r in uIoc s t, ‖z r‖ * ‖R r‖ := by
          apply integral_mono
          · exact (hpC.norm.integrableOn_Icc).mono_set (uIoc_subset_uIcc.trans hst)
          · exact hprod.mono_set (uIoc_subset_uIcc.trans hst)
          · intro r
            simpa only [mul_comm] using (R r).le_opNorm (z r)
        _ ≤ ∫ r in Icc (0 : ℝ) T, ‖z r‖ * ‖R r‖ :=
          setIntegral_mono_set hprod (Filter.Eventually.of_forall fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (uIoc_subset_uIcc.trans hst).eventuallySubset
    have hl := le_abs_self (∫ r in s..t, R r (z r))
    rw [← Real.norm_eq_abs] at hl
    nlinarith
  dsimp only [y] at hsavg hosc
  nlinarith [hcs]

/-- A quantitative version for an embedding of norm at most one. -/
theorem smooth_hilbert_sup_estimate_of_L2_le (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) {z : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hz : ContDiff ℝ 1 z) (hRc : ContinuousOn R (Icc 0 T))
    (hR : ∀ r ∈ Icc 0 T, hilbertEmbedding j (deriv z r) = R r)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hz2 : (∫ r in (0 : ℝ)..T, ‖z r‖ ^ 2) ≤ ε)
    (hR2 : (∫ r in (0 : ℝ)..T, ‖R r‖ ^ 2) ≤ ε)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖j (z t)‖ ^ 2 ≤ (T⁻¹ + 2) * ε := by
  have hn (v : V) : ‖j v‖ ≤ ‖v‖ := by
    calc
      _ ≤ ‖j‖ * ‖v‖ := j.le_opNorm v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hj (norm_nonneg v)
      _ = _ := one_mul _
  have hj2 : (∫ r in (0 : ℝ)..T, ‖j (z r)‖ ^ 2) ≤ ε := by
    refine (intervalIntegral.integral_mono_on hT.le
      (((j.continuous.comp hz.continuous).norm.pow 2).intervalIntegrable 0 T)
      ((hz.continuous.norm.pow 2).intervalIntegrable 0 T) ?_).trans hz2
    intro r _
    exact pow_le_pow_left₀ (norm_nonneg _) (hn (z r)) 2
  have hs : Real.sqrt (∫ r in (0 : ℝ)..T, ‖z r‖ ^ 2) *
      Real.sqrt (∫ r in (0 : ℝ)..T, ‖R r‖ ^ 2) ≤ ε := by
    calc
      _ ≤ Real.sqrt ε * Real.sqrt ε :=
        mul_le_mul (Real.sqrt_le_sqrt hz2) (Real.sqrt_le_sqrt hR2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = ε := Real.mul_self_sqrt hε
  have h := smooth_hilbert_sup_estimate j hT hz hRc hR ht
  have hm := mul_le_mul_of_nonneg_left hj2 (inv_nonneg.mpr hT.le)
  nlinarith

/-- Differences of genuine smooth Hilbert triple curves satisfy the uniform
estimate using their actual squared L² differences. -/
theorem smooth_hilbert_difference_bound (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) {z w : ℝ → V} {R S : ℝ → StrongDual ℝ V}
    (hz : ContDiff ℝ 1 z) (hw : ContDiff ℝ 1 w)
    (hRc : ContinuousOn R (Icc 0 T)) (hSc : ContinuousOn S (Icc 0 T))
    (hR : ∀ r ∈ Icc 0 T, hilbertEmbedding j (deriv z r) = R r)
    (hS : ∀ r ∈ Icc 0 T, hilbertEmbedding j (deriv w r) = S r)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hzw2 : (∫ r in (0 : ℝ)..T, ‖z r - w r‖ ^ 2) ≤ ε)
    (hRS2 : (∫ r in (0 : ℝ)..T, ‖R r - S r‖ ^ 2) ≤ ε)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖j (z t) - j (w t)‖ ^ 2 ≤ (T⁻¹ + 2) * ε := by
  have hd (r : ℝ) (hr : r ∈ Icc 0 T) :
      hilbertEmbedding j (deriv (z - w) r) = (R - S) r := by
    rw [deriv_sub (hz.differentiable (by simp)).differentiableAt
      (hw.differentiable (by simp)).differentiableAt, map_sub, hR r hr, hS r hr]
    rfl
  simpa only [Pi.sub_apply, map_sub] using
    smooth_hilbert_sup_estimate_of_L2_le j hj hT (hz.sub hw) (hRc.sub hSc) hd hε hzw2 hRS2 ht

/-- Squared L² Cauchy convergence in the energy and dual spaces gives actual
uniform Cauchy convergence of the value curves on the closed interval. -/
theorem smooth_hilbert_uniformCauchy (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) {z : ℕ → ℝ → V} {R : ℕ → ℝ → StrongDual ℝ V}
    (hz : ∀ n, ContDiff ℝ 1 (z n)) (hRc : ∀ n, ContinuousOn (R n) (Icc 0 T))
    (hR : ∀ n, ∀ r ∈ Icc 0 T, hilbertEmbedding j (deriv (z n) r) = R n r)
    (hC : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫ r in (0 : ℝ)..T, ‖z n r - z m r‖ ^ 2) ≤ ε ∧
      (∫ r in (0 : ℝ)..T, ‖R n r - R m r‖ ^ 2) ≤ ε) :
    UniformCauchySeqOn (fun n r => j (z n r)) atTop (Icc 0 T) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro δ hδ
  have hK : 0 < T⁻¹ + 2 := by positivity
  let ε : ℝ := δ ^ 2 / (2 * (T⁻¹ + 2))
  have hε : 0 < ε := div_pos (sq_pos_of_pos hδ) (mul_pos (by norm_num) hK)
  obtain ⟨N, hN⟩ := hC ε hε
  refine ⟨N, fun n hn m hm t ht => ?_⟩
  have hb := smooth_hilbert_difference_bound j hj hT (hz n) (hz m) (hRc n) (hRc m)
    (hR n) (hR m) hε.le (hN n hn m hm).1 (hN n hn m hm).2 ht
  have he : (T⁻¹ + 2) * ε = δ ^ 2 / 2 := by dsimp only [ε]; field_simp
  rw [he] at hb
  rw [dist_eq_norm]
  nlinarith [sq_nonneg (‖j (z n t) - j (z m t)‖ - δ)]

/-- Completeness supplies the continuous H-valued uniform limit, without an
assumed rough trace or rough energy identity. -/
theorem smooth_hilbert_continuous_limit [CompleteSpace H]
    (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) {z : ℕ → ℝ → V} {R : ℕ → ℝ → StrongDual ℝ V}
    (hz : ∀ n, ContDiff ℝ 1 (z n)) (hRc : ∀ n, ContinuousOn (R n) (Icc 0 T))
    (hR : ∀ n, ∀ r ∈ Icc 0 T, hilbertEmbedding j (deriv (z n) r) = R n r)
    (hC : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫ r in (0 : ℝ)..T, ‖z n r - z m r‖ ^ 2) ≤ ε ∧
      (∫ r in (0 : ℝ)..T, ‖R n r - R m r‖ ^ 2) ≤ ε) :
    ∃ u : ℝ → H, ContinuousOn u (Icc 0 T) ∧
      TendstoUniformlyOn (fun n r => j (z n r)) u atTop (Icc 0 T) := by
  have hu := smooth_hilbert_uniformCauchy j hj hT hz hRc hR hC
  have hp : ∀ r ∈ Icc 0 T, ∃ v : H, Tendsto (fun n => j (z n r)) atTop (𝓝 v) :=
    fun r hr => cauchySeq_tendsto_of_complete (hu.cauchySeq hr)
  choose v hv using hp
  let u : ℝ → H := fun r => if hr : r ∈ Icc 0 T then v r hr else 0
  have ht : TendstoUniformlyOn (fun n r => j (z n r)) u atTop (Icc 0 T) :=
    hu.tendstoUniformlyOn_of_tendsto (fun r hr => by simpa only [u, dite_eq_left hr] using hv r hr)
  exact ⟨u, ht.continuousOn (Filter.Eventually.of_forall
    (fun n => (j.continuous.comp (hz n).continuous).continuousOn)).frequently, ht⟩

end Hilbert
end Yau.LeafProofs.L16HilbertTimeRegularization
