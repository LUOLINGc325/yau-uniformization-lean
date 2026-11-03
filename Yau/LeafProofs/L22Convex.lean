import Yau.LeafProofs.L22Basic

noncomputable section

open scoped Topology ContDiff Manifold Matrix ComplexOrder
open MeasureTheory Set

namespace Yau.LeafProofs.L22Aux

variable {n : ℕ}

theorem circleAverage_eq_setAverage (f : ℝ → ℝ) :
    circleAverage f = ⨍ θ in Ioc (0 : ℝ) (2 * Real.pi), f θ := by
  rw [setAverage_eq, Real.volume_real_Ioc_of_le (by positivity), sub_zero]
  rw [circleAverage, intervalIntegral.integral_of_le (by positivity), smul_eq_mul]

/-- Jensen's inequality for the actual normalized angular measure appearing
in the frozen definition of classical plurisubharmonicity. -/
theorem circleAverage_jensen_pair {Φ : ℝ × ℝ → ℝ}
    (hΦ : ConvexOn ℝ univ Φ) (hΦc : Continuous Φ)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Φ (circleAverage f, circleAverage g) ≤
      circleAverage (fun θ => Φ (f θ, g θ)) := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfi : IntegrableOn f (Ioc 0 (2 * Real.pi)) :=
    hf.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hgi : IntegrableOn g (Ioc 0 (2 * Real.pi)) :=
    hg.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hΦi : IntegrableOn (fun θ => Φ (f θ, g θ)) (Ioc 0 (2 * Real.pi)) :=
    (hΦc.comp (hf.prodMk hg)).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hJ := hΦ.map_set_average_le hΦc.continuousOn isClosed_univ
    (by simpa only [Real.volume_Ioc, sub_zero, ne_eq, ENNReal.ofReal_eq_zero] using
      (not_le.mpr hp) : (volume : Measure ℝ) (Ioc 0 (2 * Real.pi)) ≠ 0)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top :
      (volume : Measure ℝ) (Ioc 0 (2 * Real.pi)) ≠ ⊤)
    (Filter.Eventually.of_forall (fun θ => mem_univ (f θ, g θ)))
    (hfi.prodMk hgi) hΦi
  rw [average_pair hfi hgi] at hJ
  simpa only [← circleAverage_eq_setAverage] using hJ

theorem setAverage_pi {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ i, Continuous (f i)) :
    (⨍ θ in Ioc (0 : ℝ) (2 * Real.pi), fun i => f i θ) =
      fun i => circleAverage (f i) := by
  have hfi (i : ι) : IntegrableOn (f i) (Ioc 0 (2 * Real.pi)) :=
    (hf i).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  ext i
  rw [setAverage_eq]
  change (volume.real (Ioc (0 : ℝ) (2 * Real.pi)))⁻¹ *
    (∫ θ in Ioc (0 : ℝ) (2 * Real.pi), fun j => f j θ) i = _
  rw [eval_integral hfi, ← smul_eq_mul, ← setAverage_eq,
    ← circleAverage_eq_setAverage]

/-- The finite-family form is independent of the cardinality of the active
branches, as required when regularized maxima are glued on a locally finite
cover. -/
theorem circleAverage_jensen_pi {ι : Type*} [Fintype ι]
    {Φ : (ι → ℝ) → ℝ} (hΦ : ConvexOn ℝ univ Φ) (hΦc : Continuous Φ)
    (f : ι → ℝ → ℝ) (hf : ∀ i, Continuous (f i)) :
    Φ (fun i => circleAverage (f i)) ≤
      circleAverage (fun θ => Φ (fun i => f i θ)) := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfc : Continuous (fun θ i => f i θ) := continuous_pi hf
  have hfi : IntegrableOn (fun θ i => f i θ) (Ioc 0 (2 * Real.pi)) :=
    hfc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hΦi : IntegrableOn (fun θ => Φ (fun i => f i θ)) (Ioc 0 (2 * Real.pi)) :=
    (hΦc.comp hfc).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hJ := hΦ.map_set_average_le hΦc.continuousOn isClosed_univ
    (by simpa only [Real.volume_Ioc, sub_zero, ne_eq, ENNReal.ofReal_eq_zero] using
      (not_le.mpr hp) : (volume : Measure ℝ) (Ioc 0 (2 * Real.pi)) ≠ 0)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top :
      (volume : Measure ℝ) (Ioc 0 (2 * Real.pi)) ≠ ⊤)
    (Filter.Eventually.of_forall (fun θ => mem_univ (fun i => f i θ))) hfi hΦi
  rw [setAverage_pi f hf, ← circleAverage_eq_setAverage] at hJ
  exact hJ

/-- A continuous convex aggregator which is increasing in each argument
preserves the exact complex-affine-disc submean predicate. This covers the
analytic part of a regularized maximum independently of its construction. -/
theorem complexLinePshOn_convex_pair {O : Set (ComplexVector n)}
    {f g : ComplexVector n → ℝ} (hf : LeafCandidates.ComplexLinePshOn O f)
    (hg : LeafCandidates.ComplexLinePshOn O g) {Φ : ℝ × ℝ → ℝ}
    (hΦ : ConvexOn ℝ univ Φ) (hΦc : Continuous Φ)
    (hΦmono : Monotone Φ) :
    LeafCandidates.ComplexLinePshOn O (fun z => Φ (f z, g z)) := by
  refine ⟨hΦc.comp_continuousOn (hf.1.prodMk hg.1), ?_⟩
  intro z w hdisc
  exact (hΦmono ⟨hf.2 z w hdisc, hg.2 z w hdisc⟩).trans
    (circleAverage_jensen_pair hΦ hΦc
      (continuous_affine_circle hf.1 z w hdisc)
      (continuous_affine_circle hg.1 z w hdisc))

theorem complexLinePshOn_convex_pi {ι : Type*} [Fintype ι]
    {O : Set (ComplexVector n)} {f : ι → ComplexVector n → ℝ}
    (hf : ∀ i, LeafCandidates.ComplexLinePshOn O (f i))
    {Φ : (ι → ℝ) → ℝ} (hΦ : ConvexOn ℝ univ Φ) (hΦc : Continuous Φ)
    (hΦmono : Monotone Φ) :
    LeafCandidates.ComplexLinePshOn O (fun z => Φ (fun i => f i z)) := by
  refine ⟨hΦc.comp_continuousOn (continuousOn_pi.mpr (fun i => (hf i).1)), ?_⟩
  intro z w hdisc
  exact (hΦmono (fun i => (hf i).2 z w hdisc)).trans
    (circleAverage_jensen_pi hΦ hΦc _
      (fun i => continuous_affine_circle (hf i).1 z w hdisc))

end Yau.LeafProofs.L22Aux
