import Yau.Proofs.D02RieszMeasureLimit
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory Filter Set Function
open scoped Topology ContDiff CompactlySupported

noncomputable section
namespace Yau.NodeProofs.D02RieszAux

/-- The continuity-set conclusion of Portmanteau also holds for finite
measures, including the zero limiting measure. -/
theorem finiteMeasure_tendsto_null_frontier {ν : ℕ → FiniteMeasure ℂ} {μ : FiniteMeasure ℂ}
    (h : Tendsto ν atTop (𝓝 μ)) {E : Set ℂ} (hE : (μ : Measure ℂ) (frontier E) = 0) :
    Tendsto (fun j ↦ (ν j : Measure ℂ) E) atTop (𝓝 ((μ : Measure ℂ) E)) := by
  have hNN : Tendsto (fun j ↦ ν j E) atTop (𝓝 (μ E)) := by
    by_cases hμ : μ = 0
    · subst μ
      have ht : Tendsto (fun j ↦ ν j E) atTop (𝓝 (0 : NNReal)) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using h.mass)
          (fun _ ↦ bot_le) (fun j ↦ (ν j).apply_le_mass E)
      simpa using ht
    · have hn := FiniteMeasure.tendsto_normalize_of_tendsto h hμ
      have hzero : (μ.normalize : Measure ℂ) (frontier E) = 0 := by
        rw [μ.toMeasure_normalize_eq_of_nonzero hμ]
        simp [hE]
      have hzeroNN : μ.normalize (frontier E) = 0 := by
        exact (μ.normalize.null_iff_toMeasure_null _).mpr hzero
      have hprob := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn hzeroNN
      convert h.mass.mul hprob using 1 <;>
        simp only [← FiniteMeasure.self_eq_mass_mul_normalize]
  simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
    (ENNReal.tendsto_coe.mpr hNN)

/-- Multiplication by a continuous nonnegative compact cutoff localizes a
measure without changing its mass where that cutoff is identically one. -/
theorem withDensity_cutoff_apply {ν : Measure ℂ} {χ : ℂ → ℝ} {E : Set ℂ}
    (hE : MeasurableSet E) (hone : ∀ z ∈ E, χ z = 1) :
    ν.withDensity (fun z ↦ ENNReal.ofReal (χ z)) E = ν E := by
  rw [withDensity_apply _ hE]
  calc
    _ = ∫⁻ _ in E, (1 : ENNReal) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hE] with z hz
      rw [hone z hz]
      simp
    _ = ν E := by simp

/-- A cutoff gives genuine weak convergence of finite measures from local
vague convergence on the original open domain. -/
theorem cutoff_weak_convergence {U : Set ℂ} {ν : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hν : ∀ j K, IsCompact K → K ⊆ U → ν j K < ⊤)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤)
    (hvague : ∀ f : C_c(ℂ, ℝ), tsupport f ⊆ U →
      Tendsto (fun j ↦ ∫ z, f z ∂ν j) atTop (𝓝 (∫ z, f z ∂μ)))
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ U) (hχ0 : ∀ z, 0 ≤ χ z) :
    let ν' := fun j ↦ (ν j).withDensity (fun z ↦ ENNReal.ofReal (χ z))
    let μ' := μ.withDensity (fun z ↦ ENNReal.ofReal (χ z))
    ∃ (νf : ℕ → FiniteMeasure ℂ) (μf : FiniteMeasure ℂ),
      (∀ j, (νf j : Measure ℂ) = ν' j) ∧ (μf : Measure ℂ) = μ' ∧
      Tendsto νf atTop (𝓝 μf) := by
  dsimp only
  have hn (j : ℕ) : IsFiniteMeasure ((ν j).withDensity (fun z ↦ ENNReal.ofReal (χ z))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_test (hν j) hχ hχc hχU).hasFiniteIntegral
  have hm : IsFiniteMeasure (μ.withDensity (fun z ↦ ENNReal.ofReal (χ z))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_test hμ hχ hχc hχU).hasFiniteIntegral
  let νf : ℕ → FiniteMeasure ℂ := fun j ↦ ⟨_, hn j⟩
  let μf : FiniteMeasure ℂ := ⟨_, hm⟩
  refine ⟨νf, μf, fun _ ↦ rfl, rfl, ?_⟩
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  let g : C_c(ℂ, ℝ) := ⟨⟨fun z ↦ χ z * f z, hχ.mul f.continuous⟩, hχc.mul_right⟩
  have hgU : tsupport g ⊆ U := tsupport_mul_subset_left.trans hχU
  have heq (σ : Measure ℂ) :
      (∫ z, f z ∂σ.withDensity (fun z ↦ ENNReal.ofReal (χ z))) = ∫ z, g z ∂σ := by
    rw [integral_withDensity_eq_integral_toReal_smul hχ.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ by simp only [ENNReal.toReal_ofReal (hχ0 z), smul_eq_mul]; rfl
  change Tendsto (fun j ↦ ∫ z, f z ∂(ν j).withDensity (fun z ↦ ENNReal.ofReal (χ z))) atTop
    (𝓝 (∫ z, f z ∂μ.withDensity (fun z ↦ ENNReal.ofReal (χ z))))
  simpa only [heq] using hvague g hgU

/-- Local vague convergence gives convergence of every relatively compact
continuity set, with no global local-finiteness assumption at the domain boundary. -/
theorem tendsto_mass_of_null_frontier {U E : Set ℂ} (hU : IsOpen U)
    {ν : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hν : ∀ j K, IsCompact K → K ⊆ U → ν j K < ⊤)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤)
    (hvague : ∀ f : C_c(ℂ, ℝ), tsupport f ⊆ U →
      Tendsto (fun j ↦ ∫ z, f z ∂ν j) atTop (𝓝 (∫ z, f z ∂μ)))
    (hEc : IsCompact (closure E)) (hEU : closure E ⊆ U) (hE : MeasurableSet E)
    (hzero : μ (frontier E) = 0) :
    Tendsto (fun j ↦ ν j E) atTop (𝓝 (μ E)) := by
  obtain ⟨χ, hχ, hχc, hχU, hχ01, hχone⟩ := exists_smooth_cutoff hU hEc hEU
  obtain ⟨νf, μf, hνf, hμf, hweak⟩ := cutoff_weak_convergence hν hμ hvague
    hχ.continuous hχc hχU (fun z ↦ (hχ01 z).1)
  have hfrontier : (μf : Measure ℂ) (frontier E) = 0 := by
    rw [hμf, withDensity_cutoff_apply isClosed_frontier.measurableSet
      (fun z hz ↦ hχone z (frontier_subset_closure hz)), hzero]
  have ht := finiteMeasure_tendsto_null_frontier hweak hfrontier
  have hνE (j : ℕ) : (νf j : Measure ℂ) E = ν j E := by
    rw [hνf j, withDensity_cutoff_apply hE (fun z hz ↦ hχone z (subset_closure hz))]
  have hμE : (μf : Measure ℂ) E = μ E := by
    rw [hμf, withDensity_cutoff_apply hE (fun z hz ↦ hχone z (subset_closure hz))]
  simpa only [hνE, hμE] using ht

end Yau.NodeProofs.D02RieszAux
