import Yau.LeafProofs.L16LionsTimeTrace

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
namespace Yau.LeafProofs.L16LionsMovingTest
open Yau.LeafProofs.L16HilbertTimeRegularization Yau.LeafProofs.L16LionsLimit
  Yau.LeafProofs.L16LionsApproximation
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem dualEval_integrable {μ : Measure ℝ} {U : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hU : MemLp U 2 μ) (hR : MemLp R 2 μ) : Integrable (fun t => R t (U t)) μ := by
  have hm := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hR.aestronglyMeasurable.prodMk hU.aestronglyMeasurable)
  exact (hR.norm.integrable_mul hU.norm).mono' hm (ae_of_all _ fun t => (R t).le_opNorm (U t))

private theorem sum_L1_tendsto {μ : Measure ℝ} {f g : ℕ → ℝ → ℝ} {a b : ℝ → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : ∀ n, Integrable (g n) μ)
    (ha : Integrable a μ) (hb : Integrable b μ)
    (hfa : Tendsto (fun n => ∫ t, ‖f n t-a t‖ ∂μ) atTop (𝓝 0))
    (hgb : Tendsto (fun n => ∫ t, ‖g n t-b t‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, ‖(f n t+g n t)-(a t+b t)‖ ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) ?_
    (by simpa only [zero_add] using hfa.add hgb)
  intro n
  have h := integral_mono (((hf n).add (hg n)).sub (ha.add hb)).norm
    (((hf n).sub ha).norm.add ((hg n).sub hb).norm) (fun t => by
      change ‖f n t+g n t-(a t+b t)‖ ≤ ‖f n t-a t‖+‖g n t-b t‖
      rw [show f n t+g n t-(a t+b t) = (f n t-a t)+(g n t-b t) by ring]
      exact norm_add_le _ _)
  have hAdd := integral_add ((hf n).sub ha).norm ((hg n).sub hb).norm
  change (∫ t, ‖f n t-a t‖+‖g n t-b t‖ ∂μ) =
    (∫ t, ‖f n t-a t‖ ∂μ)+(∫ t, ‖g n t-b t‖ ∂μ) at hAdd
  change (∫ t, ‖(f n t+g n t)-(a t+b t)‖ ∂μ) ≤
    (∫ t, ‖f n t-a t‖+‖g n t-b t‖ ∂μ) at h
  exact h.trans_eq hAdd

/-- Actual smooth approximants transport the time-varying energy-space test
    identity to their genuine strong L² limits and uniform Hilbert limit. -/
theorem moving_test_of_smooth_approximation (j : V →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    {U : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    {z : ℕ → ℝ → V} {Q : ℕ → ℝ → StrongDual ℝ V} {u : ℝ → H}
    (hz : ∀ n, ContDiff ℝ 1 (z n)) (hQc : ∀ n, ContinuousOn (Q n) (Icc 0 T))
    (hd : ∀ n, ∀ t ∈ Icc 0 T, hilbertEmbedding j (deriv (z n) t) = Q n t)
    (hzlim : Tendsto (fun n => ∫ t in Ioo 0 T, ‖z n t-U t‖^2) atTop (𝓝 0))
    (hQlim : Tendsto (fun n => ∫ t in Ioo 0 T, ‖Q n t-R t‖^2) atTop (𝓝 0))
    (hUnif : TendstoUniformlyOn (fun n t => j (z n t)) u atTop (Icc 0 T))
    {Φ : ℝ → V} (hΦ : ContDiff ℝ 1 Φ) {s t : ℝ}
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    inner ℝ (u t) (j (Φ t))-inner ℝ (u s) (j (Φ s)) =
      ∫ r in s..t, R r (Φ r)+inner ℝ (j (U r)) (j (deriv Φ r)) := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 T)
  let S : ℝ → StrongDual ℝ V := fun r => hilbertEmbedding j (deriv Φ r)
  have hSc : Continuous S := (hilbertEmbedding j).continuous.comp hΦ.continuous_deriv_one
  have hΦLp : MemLp Φ 2 μ := by
    dsimp only [μ]
    rw [restrict_Ioo_eq_restrict_Icc]
    exact continuousOn_memLp_two hΦ.continuous.continuousOn
  have hSLp : MemLp S 2 μ := by
    dsimp only [μ]
    rw [restrict_Ioo_eq_restrict_Icc]
    exact continuousOn_memLp_two hSc.continuousOn
  have hzLp (n : ℕ) : MemLp (z n) 2 μ := by
    dsimp only [μ]
    rw [restrict_Ioo_eq_restrict_Icc]
    exact continuousOn_memLp_two (hz n).continuous.continuousOn
  have hQLp (n : ℕ) : MemLp (Q n) 2 μ := by
    dsimp only [μ]
    rw [restrict_Ioo_eq_restrict_Icc]
    exact continuousOn_memLp_two (hQc n)
  have hZeroΦ : Tendsto (fun _ : ℕ => ∫ r, ‖Φ r-Φ r‖^2 ∂μ) atTop (𝓝 0) := by simp
  have hZeroS : Tendsto (fun _ : ℕ => ∫ r, ‖S r-S r‖^2 ∂μ) atTop (𝓝 0) := by simp
  have hFirst := strongL2_duality_L1 (fun _ => hΦLp) hQLp hΦLp hR hZeroΦ hQlim
  have hSecond := strongL2_duality_L1 hzLp (fun _ => hSLp) hU hSLp hzlim hZeroS
  let f : ℕ → ℝ → ℝ := fun n r => Q n r (Φ r)+S r (z n r)
  let g : ℝ → ℝ := fun r => R r (Φ r)+S r (U r)
  have hf (n : ℕ) : Integrable (f n) μ :=
    (dualEval_integrable hΦLp (hQLp n)).add (dualEval_integrable (hzLp n) hSLp)
  have hg : Integrable g μ :=
    (dualEval_integrable hΦLp hR).add (dualEval_integrable hU hSLp)
  have hL1 : Tendsto (fun n => ∫ r, ‖f n r-g r‖ ∂μ) atTop (𝓝 0) :=
    sum_L1_tendsto (fun n => dualEval_integrable hΦLp (hQLp n))
      (fun n => dualEval_integrable (hzLp n) hSLp)
      (dualEval_integrable hΦLp hR) (dualEval_integrable hU hSLp) hFirst hSecond
  have hInt := intervalIntegral_tendsto_of_L1 hf hg hL1 hs ht
  have hEnd : Tendsto (fun n => inner ℝ (j (z n t)) (j (Φ t))-
      inner ℝ (j (z n s)) (j (Φ s))) atTop
      (𝓝 (inner ℝ (u t) (j (Φ t))-inner ℝ (u s) (j (Φ s)))) :=
    ((hUnif.tendsto_at ht).inner tendsto_const_nhds).sub
      ((hUnif.tendsto_at hs).inner tendsto_const_nhds)
  have hSmooth (n : ℕ) :
      inner ℝ (j (z n t)) (j (Φ t))-inner ℝ (j (z n s)) (j (Φ s)) = ∫ r in s..t, f n r := by
    have hDerivative (r : ℝ) (hr : r ∈ uIcc s t) :
        HasDerivAt (fun r => inner ℝ (j (z n r)) (j (Φ r))) (f n r) r := by
      have hzD := j.hasFDerivAt.comp_hasDerivAt r
        ((hz n).differentiable (by simp)).differentiableAt.hasDerivAt
      have hΦD := j.hasFDerivAt.comp_hasDerivAt r
        (hΦ.differentiable (by simp)).differentiableAt.hasDerivAt
      have h := hzD.inner ℝ hΦD
      have hQValue : Q n r (Φ r) = inner ℝ (j (deriv (z n) r)) (j (Φ r)) := by
        rw [← hd n r (uIcc_subset_Icc hs ht hr),hilbertEmbedding_apply]
      have hSValue : S r (z n r) = inner ℝ (j (z n r)) (j (deriv Φ r)) := by
        simp only [S,hilbertEmbedding_apply,real_inner_comm]
      simpa only [f,hQValue,hSValue,Function.comp_def,add_comm] using h
    have hfc : ContinuousOn (f n) (Icc 0 T) :=
      ((hQc n).clm_apply hΦ.continuous.continuousOn).add
        (hSc.continuousOn.clm_apply (hz n).continuous.continuousOn)
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hDerivative
      (hfc.mono (uIcc_subset_Icc hs ht)).intervalIntegrable).symm
  have hProduct := tendsto_nhds_unique hEnd (by simpa only [hSmooth] using hInt)
  simpa only [g,S,hilbertEmbedding_apply,real_inner_comm] using hProduct

/-- The original weak time equation implies the full moving-test product
    formula, together with its actual continuous trace and energy chain. -/
theorem hilbert_time_trace_moving_test [CompleteSpace V] [CompleteSpace H]
    (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1) {T : ℝ} (hT : 0 < T)
    {U : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv φ t • hilbertEmbedding j (U t)) =
        -(∫ t in Ioo 0 T, φ t • R t)) :
    ∃ u : ℝ → H, ContinuousOn u (Icc 0 T) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 T), j (U t) = u t) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        ‖u t‖^2-‖u s‖^2 = 2*∫ r in s..t, R r (U r)) ∧
      ∀ Φ : ℝ → V, ContDiff ℝ 1 Φ → ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        inner ℝ (u t) (j (Φ t))-inner ℝ (u s) (j (Φ s)) =
          ∫ r in s..t, R r (Φ r)+inner ℝ (j (U r)) (j (deriv Φ r)) := by
  have hz (k : ℕ) := (reflectedSmooth_contDiff hT hU k).of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hQc (k : ℕ) := (reflectedDualSmooth_contDiff hT hR k).continuous.continuousOn
    (s := Icc 0 T)
  have hd (k : ℕ) (r : ℝ) (hr : r ∈ Icc 0 T) :=
    reflectedSmooth_derivative (hilbertEmbedding j) hT hU hR hw k hr
  have hzlim := reflectedSmooth_L2_tendsto hT hU
  have hQlim := reflectedDualSmooth_L2_tendsto hT hR
  obtain ⟨u,hu,hae,hUnif,hChain⟩ := smooth_approximation_trace_chain j hj hT hU hR
    hz hQc hd hzlim hQlim
  refine ⟨u,hu,hae,hChain,?_⟩
  intro Φ hΦ s hs t ht
  exact moving_test_of_smooth_approximation j hT hU hR hz hQc hd hzlim hQlim hUnif hΦ hs ht

end Yau.LeafProofs.L16LionsMovingTest
