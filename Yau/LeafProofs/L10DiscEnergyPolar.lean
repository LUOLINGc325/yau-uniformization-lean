import Yau.LeafProofs.L10DiscBoundaryBridge

/-! Polar integration and compact parameter integrals on the genuine closed disc. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace Yau.LeafProofs

theorem discEnergy_continuousOn_angularIntegral {a b c d : ℝ} (hcd : c ≤ d)
    {H : ℝ × ℝ → ℝ} (hH : ContinuousOn H (Icc a b ×ˢ Icc c d)) :
    ContinuousOn (fun r => ∫ θ in c..d, H (r, θ)) (Icc a b) := by
  rw [show (fun r => ∫ θ in c..d, H (r, θ)) =
      (fun r => ∫ θ in Ioc c d, H (r, θ)) by
        funext r; exact intervalIntegral.integral_of_le hcd]
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hH
  apply continuousOn_of_dominated (bound := fun _ : ℝ => C)
  · intro r hr
    exact ((hH.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => ⟨hr, Ioc_subset_Icc_self hθ⟩)).aestronglyMeasurable
        measurableSet_Ioc)
  · intro r hr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact hC (r, θ) ⟨hr, Ioc_subset_Icc_self hθ⟩
  · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact hH.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr, Ioc_subset_Icc_self hθ⟩)

/-- Polar integration includes the origin and uses only closed-disc continuity. -/
theorem discEnergy_integral_polar {h : ℂ → ℝ}
    (hh : ContinuousOn h (Metric.closedBall (0 : ℂ) 1)) :
    (∫ z in Metric.ball (0 : ℂ) 1, h z) =
      ∫ r in (0 : ℝ)..1, ∫ θ in (-Real.pi)..Real.pi,
        r * h (r • L08_unitCircle θ) := by
  let A := Metric.ball (0 : ℂ) 1
  let D := Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi
  let G : ℝ × ℝ → ℝ := fun p => p.1 * h (Complex.polarCoord.symm p)
  have hpcont : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hG : ContinuousOn G (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) := by
    apply continuousOn_fst.mul (hh.comp hpcont.continuousOn ?_)
    intro p hp
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm,
      abs_of_nonneg hp.1.1] using hp.1.2
  have hInt : IntegrableOn G D volume :=
    (hG.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hchange : (∫ z in A, h z) = ∫ p in D, G p := by
    rw [← integral_indicator Metric.isOpen_ball.measurableSet,
      ← Complex.integral_comp_polarCoord_symm]
    change (∫ p in polarCoord.target,
      p.1 * A.indicator h (Complex.polarCoord.symm p)) = ∫ p in D, G p
    have hT : MeasurableSet polarCoord.target := measurableSet_Ioi.prod measurableSet_Ioo
    have hD : MeasurableSet D := measurableSet_Ioo.prod measurableSet_Ioo
    rw [← integral_indicator hT, ← integral_indicator hD]
    apply integral_congr_ae
    filter_upwards with p
    by_cases hpT : p ∈ polarCoord.target
    · have hp0 : 0 < p.1 := hpT.1
      by_cases hpA : Complex.polarCoord.symm p ∈ A
      · have hpD : p ∈ D := by
          refine ⟨⟨hp0, ?_⟩, hpT.2⟩
          simpa only [A, Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
            abs_of_pos hp0] using hpA
        rw [indicator_of_mem hpT, indicator_of_mem hpD, indicator_of_mem hpA]
      · have hpD : p ∉ D := by
          intro hpD
          apply hpA
          simpa only [A, Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
            abs_of_pos hp0] using hpD.1.2
        rw [indicator_of_mem hpT, indicator_of_notMem hpD, indicator_of_notMem hpA,
          mul_zero]
    · have hpD : p ∉ D := fun hpD => hpT ⟨hpD.1.1, hpD.2⟩
      rw [indicator_of_notMem hpT, indicator_of_notMem hpD]
  rw [hchange, Measure.volume_eq_prod, setIntegral_prod _ hInt]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  dsimp only
  rw [intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    ← setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ _
  simp only [G, Complex.polarCoord_symm_apply, L08_unitCircle,
    Complex.exp_ofReal_mul_I, Complex.real_smul]

/-- Differentiation under the compact angular integral needs only the original
closed radial strip and actual derivatives at its interior points. -/
theorem discEnergy_hasDerivAt_angularIntegral
    {H H' : ℝ × ℝ → ℝ}
    (hH : ContinuousOn H (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi))
    (hH' : ContinuousOn H' (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi))
    (hderiv : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Icc (-Real.pi) Real.pi,
      HasDerivAt (fun s => H (s, θ)) (H' (r, θ)) r)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => ∫ θ in (-Real.pi)..Real.pi, H (s, θ))
      (∫ θ in (-Real.pi)..Real.pi, H' (r, θ)) r := by
  have hle : -Real.pi ≤ Real.pi := neg_le_self Real.pi_pos.le
  have hmeas {G : ℝ × ℝ → ℝ}
      (hG : ContinuousOn G (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi))
      {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
      AEStronglyMeasurable (fun θ => G (s, θ))
        (volume.restrict (uIoc (-Real.pi) Real.pi)) := by
    rw [uIoc_of_le hle]
    exact (hG.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => ⟨hs, Ioc_subset_Icc_self hθ⟩)).aestronglyMeasurable
        measurableSet_Ioc
  have hint : IntervalIntegrable (fun θ => H (r, θ)) volume (-Real.pi) Real.pi :=
    (hH.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => ⟨Ioo_subset_Icc_self hr, hθ⟩)).intervalIntegrable_of_Icc hle
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hH'
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (0 : ℝ) 1) (bound := fun _ => C) (isOpen_Ioo.mem_nhds hr)
    ?_ hint (hmeas hH' (Ioo_subset_Icc_self hr)) ?_ intervalIntegrable_const ?_).2
  · filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    exact hmeas hH (Ioo_subset_Icc_self hs)
  · filter_upwards with θ hθ s hs
    exact hC (s, θ) ⟨Ioo_subset_Icc_self hs, (by simpa only [uIcc_of_le hle] using uIoc_subset_uIcc hθ)⟩
  · filter_upwards with θ hθ s hs
    apply hderiv s hs θ
    simpa only [uIcc_of_le hle] using uIoc_subset_uIcc hθ

end Yau.LeafProofs
