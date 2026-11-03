import Yau.Proofs.D04CircleUpper

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem radialConvolution_le_of_EReal_upper
    {t : ℝ} (ht : 0 < t) {x : ComplexVector n} {u : ComplexVector n → EReal}
    (hfinite : ∀ᵐ y ∂volume.restrict (Metric.closedBall x (2 * t)), u y ≠ ⊥ ∧ u y ≠ ⊤)
    (hi : IntegrableOn (fun y => (u y).toReal) (Metric.closedBall x (2 * t)) volume)
    {A : ℝ} (hupper : ∀ y ∈ Metric.closedBall x (2 * t), u y ≤ (A : EReal)) :
    (∫ y, radialKernel t (x - y) * (u y).toReal) ≤ A := by
  let K : Set (ComplexVector n) := Metric.closedBall x (2 * t)
  have hK : IsCompact K := isCompact_closedBall x (2 * t)
  obtain ⟨B, hB⟩ := (radialKernel_hasCompactSupport (n := n) ht).exists_bound_of_continuous
    (contDiff_radialKernel t).continuous
  have hweighted : IntegrableOn (fun y => radialKernel t (x - y) * (u y).toReal) K volume :=
    hi.bdd_mul ((contDiff_radialKernel t).continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall fun y => hB (x - y))
  have hconst : IntegrableOn (fun y => radialKernel t (x - y) * A) K volume :=
    (((contDiff_radialKernel t).continuous.comp
      (continuous_const.sub continuous_id)).mul continuous_const).continuousOn.integrableOn_compact hK
  have hmass : (∫ y : ComplexVector n, radialKernel t (x - y)) = 1 := by
    have h := ((volume : Measure (ComplexVector n)).measurePreserving_sub_left x).integral_comp
      (MeasurableEquiv.subLeft x).measurableEmbedding (radialKernel t)
    exact h.trans (integral_radialKernel ht)
  have hmassK : (∫ y in K, radialKernel t (x - y)) = 1 := by
    have h := radialConvolution_eq_restrict ht (fun _ : ComplexVector n => (1 : ℝ)) x
    simp only [mul_one] at h
    exact h.symm.trans hmass
  rw [radialConvolution_eq_restrict ht]
  calc
    _ ≤ ∫ y in K, radialKernel t (x - y) * A := by
      apply integral_mono_ae hweighted hconst
      filter_upwards [hfinite, ae_restrict_mem hK.measurableSet] with y hy hyK
      have hyA : (u y).toReal ≤ A := by
        apply EReal.coe_le_coe_iff.mp
        rw [EReal.coe_toReal hy.2 hy.1]
        exact hupper y hyK
      exact mul_le_mul_of_nonneg_left hyA (radialKernel_nonneg ht _)
    _ = A := by rw [integral_mul_const, hmassK, one_mul]

theorem radialConvolution_tendsto_of_localL1
    {O : Set (ComplexVector n)} {u : ℕ → ComplexVector n → EReal}
    (hL1 : ∀ j, CoordinateLocallyL1 O (u j)) {f : ComplexVector n → ℝ}
    (hf : ∀ S : Set (ComplexVector n), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector n), IsCompact S → S ⊆ O →
      Tendsto (fun j => ∫ y in S, |(u j y).toReal - f y|) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) {x : ComplexVector n} (hx : x ∈ radialDomain O t) :
    Tendsto (fun j => ∫ y, radialKernel t (x - y) * (u j y).toReal) atTop
      (𝓝 (∫ y, radialKernel t (x - y) * f y)) := by
  have huni := radialConvolution_uniform_on_compact_of_localL1 hL1 hf hconv ht
    isCompact_singleton (Set.singleton_subset_iff.mpr hx)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (huni ε hε)
  exact ⟨J, fun j hj => by simpa only [Real.dist_eq] using hJ j hj x (mem_singleton x)⟩

/-- The USC representative of the same real local L¹ limit satisfies the
original complex-line circle-majorant predicate in every complex dimension.
The circle is translated before averaging the centers; finite-a.e. data is
used explicitly before passing each upper bound to the real pairing. -/
theorem uscRepresentative_isPshOn
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {u : ℕ → ComplexVector n → EReal}
    (hu : ∀ j, IsPshOn (u j) O ∧ CoordinateLocallyL1 O (u j))
    {f : ComplexVector n → ℝ}
    (hf : ∀ S : Set (ComplexVector n), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector n), IsCompact S → S ⊆ O →
      Tendsto (fun j => ∫ y in S, |(u j y).toReal - f y|) atTop (𝓝 0)) :
    IsPshOn (uscRepresentative O f) O := by
  refine ⟨fun x hx => uscRepresentative_lt_top hO f hx,
    (upperSemicontinuous_uscRepresentative hO hf).upperSemicontinuousOn O, ?_⟩
  intro z w hdisc φ hφ hmajor
  by_contra hnot
  have hlt : (circleAverage φ : EReal) < uscRepresentative O f z := lt_of_not_ge hnot
  obtain ⟨q, hq, hqv⟩ := EReal.exists_between_coe_real hlt
  have hqreal : circleAverage φ < q := EReal.coe_lt_coe_iff.mp hq
  let ε : ℝ := (q - circleAverage φ) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  obtain ⟨δ, hδ, hboundary⟩ := eventually_shifted_circle_upper hO hu hf hconv z w hφ
    (fun θ _ => hmajor θ) hε
  have hshift : ∀ᶠ a : ComplexVector n in 𝓝 0,
      ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, z + ζ • w - a ∈ O := by
    apply (isCompact_closedBall (0 : ℂ) 1).eventually_forall_of_forall_eventually
    intro ζ hζ
    have hc : Continuous (fun p : ComplexVector n × ℂ => z + p.2 • w - p.1) := by fun_prop
    apply (hc.tendsto (0, ζ)).eventually
    apply hO.mem_nhds
    simpa only [sub_zero] using hdisc ζ
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hζ)
  obtain ⟨η, hη, hηshift⟩ := Metric.mem_nhds_iff.mp hshift
  have htend : Tendsto (fun k => 2 * natRadius k) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_natRadius
  obtain ⟨k, hk⟩ := ((tendsto_order.mp htend).2 (min δ η) (lt_min hδ hη)).exists
  have hkδ : 2 * natRadius k < δ := hk.trans_le (min_le_left _ _)
  have hkη : 2 * natRadius k < η := hk.trans_le (min_le_right _ _)
  have hallshift (a : ComplexVector n) (ha : ‖a‖ ≤ 2 * natRadius k)
      (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) : z + ζ • w - a ∈ O :=
    hηshift (by simpa only [Metric.mem_ball, dist_zero_right] using ha.trans_lt hkη)
      ζ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hζ)
  have hzD : z ∈ radialDomain O (natRadius k) := by
    intro y hy
    have ha : ‖z - y‖ ≤ 2 * natRadius k := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hy
    simpa only [zero_smul, add_zero, sub_sub_cancel] using hallshift (z - y) ha 0 (by simp)
  have hupper : ∀ᶠ j in atTop, ∀ y ∈ Metric.closedBall z (2 * natRadius k),
      u j y ≤ ((circleAverage φ + ε : ℝ) : EReal) := by
    filter_upwards [hboundary] with j hj
    intro y hy
    have ha : ‖z - y‖ ≤ 2 * natRadius k := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hy
    have hdiscy (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) : y + ζ • w ∈ O := by
      have h := hallshift (z - y) ha ζ hζ
      convert h using 1; abel_nf
    have h := intervalMajorant_submean (hu j).1 y w hdiscy (hφ.add continuous_const)
      (fun θ hθ => by
        have hb := hj (z - y) (ha.trans_lt hkδ) θ hθ
        convert hb using 1; abel_nf)
    change u j y ≤ (circleAverage (fun θ => φ θ + ε) : EReal) at h
    rw [circleAverage_add_const hφ ε] at h
    exact h
  have hconvpoint := radialConvolution_tendsto_of_localL1 (fun j => (hu j).2) hf hconv
    (natRadius_pos k) hzD
  have hconvupper : (∫ y, radialKernel (natRadius k) (z - y) * f y) ≤ circleAverage φ + ε := by
    apply le_of_tendsto hconvpoint
    filter_upwards [hupper] with j hj
    obtain ⟨hfinite, hi⟩ := (hu j).2 (Metric.closedBall z (2 * natRadius k))
      (isCompact_closedBall z (2 * natRadius k)) hzD
    exact radialConvolution_le_of_EReal_upper (natRadius_pos k) hfinite hi hj
  have hvle := iInf_le (fun m => radialRegularization O f (natRadius m) z) k
  rw [radialRegularization, ite_eq_left hzD] at hvle
  have hvupper := hvle.trans (EReal.coe_le_coe_iff.mpr hconvupper)
  have hstrict : ((circleAverage φ + ε : ℝ) : EReal) < uscRepresentative O f z :=
    (EReal.coe_lt_coe_iff.mpr (by dsimp only [ε]; linarith)).trans hqv
  exact (not_le_of_gt hstrict) hvupper

end Yau.Proofs.D04Aux
