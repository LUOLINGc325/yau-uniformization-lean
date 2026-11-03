import Yau.Proofs.F03MinimalBoundedEvolution

/-! The genuine compact-continuous delta trace of the same increasing limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000

theorem dirichletMinimalKernelCandidate_nonneg_compact_initial
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : Continuous f) (hcf : HasCompactSupport f)
    (hn : ∀ z, 0 ≤ f z) (y : M.Carrier) :
    Tendsto (fun t => ∫ z, dirichletMinimalKernelCandidate g hK μ hμ O hO t y z*f z ∂μ)
      (𝓝[>] 0) (𝓝 (f y)) := by
  have hc := smoothExhaustion_eventually_contains_compact hO
    (hcf.union (isCompact_singleton : IsCompact ({y} : Set M.Carrier)))
  obtain ⟨j,hj⟩ := hc.exists
  have hfo : tsupport f ⊆ O j := fun z hz => hj (Or.inl hz)
  have hy : y ∈ O j := hj (Or.inr (mem_singleton y))
  have hLower : Tendsto (fun t => ∫ z,
      dirichletKernelCandidate g hK μ hμ (O j) (hO.1 j).1 t y z*f z ∂μ)
      (𝓝[>] 0) (𝓝 (f y)) := by
    apply (dirichletKernelCandidate_compact_initial g hK μ hμ (O j) (hO.1 j).1 f hf hcf hfo y hy).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply integral_congr_ae
    exact ae_of_all μ (fun z => congrArg (fun v : ℝ => v*f z)
      (dirichletKernelCandidate_symm g hK μ hμ (O j) (hO.1 j).1 ht z y))
  have hUpper : Tendsto (fun t => ∫ z,
      dirichletKernelCandidate g hK μ hμ univ isOpen_univ t y z*f z ∂μ)
      (𝓝[>] 0) (𝓝 (f y)) := by
    apply (dirichletKernelCandidate_compact_initial g hK μ hμ univ isOpen_univ f hf hcf
      (subset_univ _) y (mem_univ y)).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply integral_congr_ae
    exact ae_of_all μ (fun z => congrArg (fun v : ℝ => v*f z)
      (dirichletKernelCandidate_symm g hK μ hμ univ isOpen_univ ht z y))
  obtain ⟨B,hB⟩ := hf.bounded_above_of_compact_support hcf
  have hbound : ∃ B : ℝ, ∀ z, |f z| ≤ B := ⟨B,fun z => by
    simpa only [Real.norm_eq_abs] using hB z⟩
  have hfLj := continuous_compact_scalarL2 g μ hμ (O j) hf hcf
  have hfLu := continuous_compact_scalarL2 g μ hμ univ hf hcf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper
  · filter_upwards [self_mem_nhdsWithin] with t ht
    apply integral_mono
      (dirichletKernelCandidate_source_integrable g hK μ hμ (O j) (hO.1 j).1 ht y hy f hfLj)
      (dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO f
        hf.aestronglyMeasurable hbound ht y)
    intro z
    exact mul_le_mul_of_nonneg_right
      (dirichletExhaustionKernels_le_limit g hK μ hμ O hO ht y z j) (hn z)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    apply integral_mono
      (dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO f
        hf.aestronglyMeasurable hbound ht y)
      (dirichletKernelCandidate_source_integrable g hK μ hμ univ isOpen_univ ht y (mem_univ y) f hfLu)
    intro z
    exact mul_le_mul_of_nonneg_right
      (dirichletMinimalKernelCandidate_le_univ g hK μ hμ O hO ht y z) (hn z)

theorem dirichletMinimalKernelCandidate_compact_initial
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : Continuous f) (hcf : HasCompactSupport f) (y : M.Carrier) :
    Tendsto (fun t => ∫ z, dirichletMinimalKernelCandidate g hK μ hμ O hO t z y*f z ∂μ)
      (𝓝[>] 0) (𝓝 (f y)) := by
  let p := fun z => |f z|+f z
  let a := fun z => |f z|
  have hp : Continuous p := hf.abs.add hf
  have ha : Continuous a := hf.abs
  have hcp : HasCompactSupport p := hcf.abs.add hcf
  have hca : HasCompactSupport a := hcf.abs
  have hpn : ∀ z, 0 ≤ p z := fun z => by dsimp [p];linarith only [neg_abs_le (f z)]
  have hlim := (dirichletMinimalKernelCandidate_nonneg_compact_initial g hK μ hμ O hO p hp hcp hpn y).sub
    (dirichletMinimalKernelCandidate_nonneg_compact_initial g hK μ hμ O hO a ha hca
      (fun z => abs_nonneg (f z)) y)
  have hvalue : p y-a y=f y := by dsimp [p,a];ring
  rw [hvalue] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  obtain ⟨P,hP⟩ := hp.bounded_above_of_compact_support hcp
  obtain ⟨A,hA⟩ := ha.bounded_above_of_compact_support hca
  have hiP := dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO p
    hp.aestronglyMeasurable ⟨P,fun z => by simpa only [Real.norm_eq_abs] using hP z⟩ ht y
  have hiA := dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO a
    ha.aestronglyMeasurable ⟨A,fun z => by simpa only [Real.norm_eq_abs] using hA z⟩ ht y
  rw [← integral_sub hiP hiA]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [dirichletMinimalKernelCandidate_symm g hK μ hμ O hO ht z y]
  dsimp [p,a]
  ring

end Yau.Proofs.F03Aux
