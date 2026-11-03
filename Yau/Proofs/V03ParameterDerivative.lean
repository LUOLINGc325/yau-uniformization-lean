import Yau.Proofs.V03ParameterIntegral

/-! Differentiation of parameter integrals with compactly derived derivative
bounds. The derivative is an actual supplied HasFDerivAt, not a free bound. -/

open scoped Topology
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem differentiableAt_intervalIntegral_of_joint_compact
    {K : Set P} (hK : IsCompact K) {x : P} (hx : K ∈ 𝓝 x)
    {a b : ℝ} (hab : a ≤ b) {f : P → ℝ → F} {f' : P → ℝ → P →L[ℂ] F}
    (hf : ContinuousOn (fun p : P × ℝ => f p.1 p.2) (K ×ˢ Set.Icc a b))
    (hf' : ContinuousOn (fun p : P × ℝ => f' p.1 p.2) (K ×ˢ Set.Icc a b))
    (hd : ∀ y ∈ K, ∀ t ∈ Set.Icc a b, HasFDerivAt (fun z => f z t) (f' y t) y) :
    DifferentiableAt ℂ (fun y => ∫ t in a..b, f y t) x := by
  have htime : ∀ y ∈ K, ContinuousOn (f y) (Set.Icc a b) := by
    intro y hy
    exact hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hy, ht⟩)
  have htime' : ∀ y ∈ K, ContinuousOn (f' y) (Set.Icc a b) := by
    intro y hy
    exact hf'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hy, ht⟩)
  obtain ⟨C, hC⟩ :=
    ((hK.prod (isCompact_Icc : IsCompact (Set.Icc a b))).image_of_continuousOn hf').isBounded.exists_norm_le
  have hmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (f y) (volume.restrict (Set.Ioc a b)) := by
    filter_upwards [hx] with y hy
    exact ((htime y hy).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hint : Integrable (f x) (volume.restrict (Set.Ioc a b)) :=
    ((htime x (mem_of_mem_nhds hx)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hmeas' : AEStronglyMeasurable (f' x) (volume.restrict (Set.Ioc a b)) :=
    ((htime' x (mem_of_mem_nhds hx)).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ∀ y ∈ K, ‖f' y t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro y hy
    exact hC (f' y t) ⟨(y, t), ⟨hy, Set.Ioc_subset_Icc_self ht⟩, rfl⟩
  have hderiv : ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      ∀ y ∈ K, HasFDerivAt (fun z => f z t) (f' y t) y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact fun y hy => hd y hy t (Set.Ioc_subset_Icc_self ht)
  have hI := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (μ := volume.restrict (Set.Ioc a b)) hx hmeas hint hmeas' hbound (integrable_const C) hderiv
  simpa only [intervalIntegral.integral_of_le hab] using hI.differentiableAt

end Yau.Blueprint.V03Proof
