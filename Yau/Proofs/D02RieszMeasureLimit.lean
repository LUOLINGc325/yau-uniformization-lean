import Yau.Proofs.D02RieszApprox
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.Order.LiminfLimsup

open MeasureTheory Filter Set Function
open scoped Topology ContDiff CompactlySupported

noncomputable section
namespace Yau.NodeProofs.D02RieszAux

/-- Interior compact support is sufficient for integrability; no finiteness at
boundary points of the open domain is imposed. -/
theorem integrable_test {U : Set ℂ} {ν : Measure ℂ}
    (hν : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ν K < ⊤)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ U) : Integrable f ν := by
  apply (hf.continuousOn.integrableOn_of_subset_isCompact hfc
    (isClosed_tsupport f).measurableSet Subset.rfl (hν _ hfc hfU).ne).integrable_of_forall_notMem_eq_zero
  exact fun z hz ↦ image_eq_zero_of_notMem_tsupport hz

/-- A sequence of positive measures whose smooth interior test pairings
converge has convergent pairings on every continuous interior compact test. -/
theorem exists_pairing_limit {U : Set ℂ} (hU : IsOpen U) (ν : ℕ → Measure ℂ)
    (hν : ∀ j K, IsCompact K → K ⊆ U → ν j K < ⊤)
    (hsmooth : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∃ a : ℝ, Tendsto (fun j ↦ ∫ z, φ z ∂ν j) atTop (𝓝 a))
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ U) :
    ∃ a : ℝ, Tendsto (fun j ↦ ∫ z, f z ∂ν j) atTop (𝓝 a) := by
  apply cauchySeq_tendsto_of_complete
  obtain ⟨K, hK, hKU, hfK, happrox⟩ := exists_smooth_approx hU hf hfc hfU
  obtain ⟨χ, hχ, hχc, hχU, hχ01, hχone⟩ := exists_smooth_cutoff hU hK hKU
  obtain ⟨a, ha⟩ := hsmooth χ hχ hχc hχU
  obtain ⟨B, hB⟩ := ha.bddAbove_range
  let C := max B 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hχbound (j : ℕ) : (∫ z, χ z ∂ν j) ≤ C :=
    (hB ⟨j, rfl⟩).trans (by dsimp [C]; linarith [le_max_left B 0])
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ := ε / (4 * C)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g, hg, hgc, hgK, hgf⟩ := happrox δ hδ
  obtain ⟨b, hb⟩ := hsmooth g hg hgc (hgK.trans hKU)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hb.cauchySeq (ε / 2) (half_pos hε)
  have herr (j : ℕ) : dist (∫ z, f z ∂ν j) (∫ z, g z ∂ν j) ≤ δ * C := by
    rw [Real.dist_eq, ← integral_sub
      (integrable_test (hν j) hf hfc hfU)
      (integrable_test (hν j) hg.continuous hgc (hgK.trans hKU))]
    have hnorm : |∫ z, f z - g z ∂ν j| ≤ ∫ z, δ * χ z ∂ν j := by
      change ‖∫ z, f z - g z ∂ν j‖ ≤ _
      apply norm_integral_le_of_norm_le ((integrable_test (hν j) hχ.continuous hχc hχU).const_mul δ)
      apply Filter.Eventually.of_forall
      intro z
      by_cases hz : z ∈ K
      · rw [hχone z hz, mul_one, Real.norm_eq_abs, abs_sub_comm]
        exact hgf z
      · have hzf : z ∉ tsupport f := fun hz' ↦ hz (hfK hz')
        have hzg : z ∉ tsupport g := fun hz' ↦ hz (hgK hz')
        rw [image_eq_zero_of_notMem_tsupport hzf, image_eq_zero_of_notMem_tsupport hzg,
          sub_self, norm_zero]
        exact mul_nonneg hδ.le (hχ01 z).1
    have hnorm' : |∫ z, f z - g z ∂ν j| ≤ δ * (∫ z, χ z ∂ν j) := by
      simpa only [Real.norm_eq_abs, integral_const_mul] using hnorm
    exact hnorm'.trans (mul_le_mul_of_nonneg_left (hχbound j) hδ.le)
  refine ⟨N, fun i hi j hj ↦ ?_⟩
  have htri := dist_triangle4 (∫ z, f z ∂ν i) (∫ z, g z ∂ν i)
    (∫ z, g z ∂ν j) (∫ z, f z ∂ν j)
  have hmid := hN i hi j hj
  have hright : dist (∫ z, g z ∂ν j) (∫ z, f z ∂ν j) ≤ δ * C := by
    simpa only [dist_comm] using herr j
  have hδC : δ * C = ε / 4 := by dsimp [δ]; field_simp
  linarith [herr i]

/-- Extension by zero identifies compactly supported tests on the open-domain
subtype with ordinary planar tests supported inside that domain. -/
def extendTest {U : Set ℂ} (hU : IsOpen U) (f : C_c(U, ℝ)) : C_c(ℂ, ℝ) where
  toFun := Subtype.val.extend f 0
  continuous_toFun := HasCompactSupport.continuous_extend_zero hU f.continuous f.hasCompactSupport
  hasCompactSupport' := f.hasCompactSupport.extend_zero continuous_subtype_val

@[simp] theorem extendTest_apply {U : Set ℂ} (hU : IsOpen U) (f : C_c(U, ℝ)) (z : U) :
    extendTest hU f z = f z := by
  exact Subtype.val_injective.extend_apply _ _ _

theorem extendTest_tsupport_subset {U : Set ℂ} (hU : IsOpen U) (f : C_c(U, ℝ)) :
    tsupport (extendTest hU f) ⊆ U := by
  exact (f.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans
    (Subtype.coe_image_subset _ _)

@[simp] theorem extendTest_of_notMem {U : Set ℂ} (hU : IsOpen U) (f : C_c(U, ℝ))
    {z : ℂ} (hz : z ∉ U) : extendTest hU f z = 0 := by
  apply Function.extend_apply'
  rintro ⟨x, rfl⟩
  exact hz x.property

@[simp] theorem extendTest_add {U : Set ℂ} (hU : IsOpen U) (f g : C_c(U, ℝ)) :
    extendTest hU (f + g) = extendTest hU f + extendTest hU g := by
  ext z
  change extendTest hU (f + g) z = extendTest hU f z + extendTest hU g z
  by_cases hz : z ∈ U
  · rw [extendTest_apply hU (f + g) ⟨z, hz⟩, extendTest_apply hU f ⟨z, hz⟩,
      extendTest_apply hU g ⟨z, hz⟩]
    rfl
  · simp [extendTest_of_notMem hU _ hz]

@[simp] theorem extendTest_smul {U : Set ℂ} (hU : IsOpen U) (r : ℝ) (f : C_c(U, ℝ)) :
    extendTest hU (r • f) = r • extendTest hU f := by
  ext z
  change extendTest hU (r • f) z = r * extendTest hU f z
  by_cases hz : z ∈ U
  · rw [extendTest_apply hU (r • f) ⟨z, hz⟩, extendTest_apply hU f ⟨z, hz⟩]
    rfl
  · simp [extendTest_of_notMem hU _ hz]

/-- Restriction of a planar interior test to the open-domain subtype. -/
def restrictTest {U : Set ℂ} (f : C_c(ℂ, ℝ)) (hfU : tsupport f ⊆ U) : C_c(U, ℝ) where
  toFun := fun z ↦ f z
  continuous_toFun := f.continuous.comp continuous_subtype_val
  hasCompactSupport' := by
    apply (Topology.IsInducing.subtypeVal.isCompact_preimage' f.hasCompactSupport
      (by simpa only [Subtype.range_val] using hfU)).of_isClosed_subset (isClosed_tsupport _)
    exact tsupport_comp_subset_preimage f continuous_subtype_val

@[simp] theorem extendTest_restrictTest {U : Set ℂ} (hU : IsOpen U)
    (f : C_c(ℂ, ℝ)) (hfU : tsupport f ⊆ U) :
    extendTest hU (restrictTest f hfU) = f := by
  ext z
  by_cases hz : z ∈ U
  · exact show extendTest hU (restrictTest f hfU) (⟨z, hz⟩ : U) = f z by
      rw [extendTest_apply]; rfl
  · rw [extendTest_of_notMem hU _ hz, image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hfU h))]

/-- Riesz–Markov constructs the actual limiting positive measure from smooth
pairings. The finiteness conclusion concerns interior compacts only. -/
theorem exists_measure_of_smooth_pairings {U : Set ℂ} (hU : IsOpen U) (ν : ℕ → Measure ℂ)
    (hν : ∀ j K, IsCompact K → K ⊆ U → ν j K < ⊤)
    (hsmooth : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∃ a : ℝ, Tendsto (fun j ↦ ∫ z, φ z ∂ν j) atTop (𝓝 a)) :
    ∃ μ : Measure ℂ,
      (∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤) ∧ μ Uᶜ = 0 ∧
      ∀ f : C_c(ℂ, ℝ), tsupport f ⊆ U →
        Tendsto (fun j ↦ ∫ z, f z ∂ν j) atTop (𝓝 (∫ z, f z ∂μ)) := by
  classical
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hlim : ∀ f : C_c(U, ℝ), ∃ a : ℝ,
      Tendsto (fun j ↦ ∫ z, extendTest hU f z ∂ν j) atTop (𝓝 a) := by
    intro f
    exact exists_pairing_limit hU ν hν hsmooth (extendTest hU f).continuous
      (extendTest hU f).hasCompactSupport (extendTest_tsupport_subset hU f)
  choose L hL using hlim
  have hi (j : ℕ) (f : C_c(U, ℝ)) : Integrable (extendTest hU f) (ν j) :=
    integrable_test (hν j) (extendTest hU f).continuous (extendTest hU f).hasCompactSupport
      (extendTest_tsupport_subset hU f)
  let Λ : C_c(U, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := L
      map_add' := by
        intro f g
        apply tendsto_nhds_unique (hL (f + g))
        convert (hL f).add (hL g) using 1
        funext j
        rw [extendTest_add]
        exact integral_add (hi j f) (hi j g)
      map_smul' := by
        intro r f
        apply tendsto_nhds_unique (hL (r • f))
        convert (hL f).const_smul r using 1
        funext j
        rw [extendTest_smul]
        exact integral_smul r (extendTest hU f)
      monotone' := by
        intro f g hfg
        apply le_of_tendsto_of_tendsto (hL f) (hL g)
        apply Filter.Eventually.of_forall
        intro j
        apply integral_mono (hi j f) (hi j g)
        intro z
        by_cases hz : z ∈ U
        · rw [extendTest_apply hU f ⟨z, hz⟩, extendTest_apply hU g ⟨z, hz⟩]
          exact hfg ⟨z, hz⟩
        · simp [extendTest_of_notMem hU _ hz] }
  let ρ : Measure U := RealRMK.rieszMeasure Λ
  let μ : Measure ℂ := ρ.map Subtype.val
  refine ⟨μ, ?_, ?_, ?_⟩
  · intro K hK hKU
    rw [show μ K = ρ (Subtype.val ⁻¹' K) from
      Measure.map_apply measurable_subtype_coe hK.measurableSet]
    apply IsCompact.measure_lt_top
    exact Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa only [Subtype.range_val] using hKU)
  · rw [show μ Uᶜ = ρ (Subtype.val ⁻¹' Uᶜ) from
      Measure.map_apply measurable_subtype_coe hU.measurableSet.compl]
    simp
  · intro f hfU
    let g := restrictTest f hfU
    have hrep : (∫ z, f z ∂μ) = L g := by
      rw [show (∫ z, f z ∂μ) = ∫ z : U, f z ∂ρ from
        integral_map_of_stronglyMeasurable measurable_subtype_coe f.continuous.stronglyMeasurable]
      exact RealRMK.integral_rieszMeasure Λ g
    rw [hrep]
    simpa only [g, extendTest_restrictTest hU f hfU] using hL g

end Yau.NodeProofs.D02RieszAux
