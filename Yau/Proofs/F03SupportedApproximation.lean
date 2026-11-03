import Yau.LeafProofs.L19SmoothDensity

/-! Actual compact smooth approximation with support in the given open set. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.Proofs.F03Aux
open Yau
open LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

/-- The native smooth approximation can retain its actual support, which is
needed for the supported Dirichlet core. -/
theorem exists_supported_smooth_approx_of_continuous
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {f : M.Carrier → ℝ} (hcf : HasCompactSupport f) (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : M.Carrier → ℝ, SmoothFn k ∧ HasCompactSupport k ∧ tsupport k ⊆ tsupport f ∧
      eLpNorm (f - k) 2 μ ≤ ENNReal.ofReal ε := by
  let := LeafProofs.L12Aux.manifold_realSmooth M
  let : LocallyCompactSpace M.Carrier := LeafProofs.L12Aux.manifold_locallyCompact M
  have : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  by_cases hfzero : f =ᵐ[μ] 0
  · refine ⟨0, smoothFn_const 0, HasCompactSupport.zero, by simp, ?_⟩
    rw [eLpNorm_congr_ae (by simpa using hfzero)]
    simp
  have hs₁ : μ (tsupport f) ≠ ⊤ := hcf.measure_lt_top.ne
  have hs₂ : 0 < (μ (tsupport f)).toReal := by
    rw [← Measure.measure_support_eq_zero_iff _] at hfzero
    exact ENNReal.toReal_pos (pos_mono (subset_tsupport f) (pos_of_ne_zero hfzero)).ne' hs₁
  let δ := ε * (μ (tsupport f)).toReal ^ (-(1 / (2 : ℝ)))
  have hδ : 0 < δ := by positivity
  have hδbound : ENNReal.ofReal δ * μ (tsupport f) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hs₁, ENNReal.ofReal_rpow_of_pos hs₂,
      ← ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_le_ofReal_iff hε.le]
    dsimp [δ]
    rw [mul_assoc, ← Real.rpow_add hs₂, neg_add_cancel, Real.rpow_zero, mul_one]
  obtain ⟨k, hkapprox, hksupp⟩ := hf.exists_contMDiff_approx
    𝓘(ℝ, ComplexVector n) ⊤ (ε := fun _ => δ) continuous_const (fun _ => hδ)
  refine ⟨k, smoothFn_of_contMDiff_real k.contMDiff, hcf.mono hksupp,
    closure_mono hksupp, ?_⟩
  apply (eLpNorm_sub_le_of_dist_bdd μ (by simp : (2 : ℝ≥0∞) ≠ ⊤)
    hcf.measurableSet.nullMeasurableSet hδ.le
    (hf.sub k.contMDiff.continuous).aestronglyMeasurable (fun x => ?_)
    (subset_tsupport f) (hksupp.trans (subset_tsupport f))).trans hδbound
  rw [dist_comm]
  exact (hkapprox x).le

/-- Continuous approximation is performed on O itself and extended by zero.
Compact support in the subtype becomes compact support strictly inside O. -/
theorem exists_supported_continuous_approx
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O : Set M.Carrier} (hO : IsOpen O) {f : M.Carrier → ℝ}
    (hf : MemLp f 2 (μ.restrict O)) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : M.Carrier → ℝ, Continuous F ∧ HasCompactSupport F ∧ tsupport F ⊆ O ∧
      eLpNorm (f - F) 2 (μ.restrict O) ≤ ENNReal.ofReal ε := by
  let : LocallyCompactSpace M.Carrier := LeafProofs.L12Aux.manifold_locallyCompact M
  let : LocallyCompactSpace O := hO.locallyCompactSpace
  have : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  let ν : Measure O := μ.comap ((↑) : O → M.Carrier)
  have : ν.Regular := Measure.Regular.comap' μ hO.isOpenEmbedding_subtypeVal
  have hmp : MeasurePreserving ((↑) : O → M.Carrier) ν (μ.restrict O) :=
    ⟨measurable_subtype_coe, map_comap_subtype_coe hO.measurableSet μ⟩
  have hfs : MemLp (fun x : O => f x) 2 ν := hf.comp_measurePreserving hmp
  obtain ⟨v, hvc, hvnorm, hvcont, _⟩ := hfs.exists_hasCompactSupport_eLpNorm_sub_le
    (by simp) (ENNReal.ofReal_pos.mpr hε).ne'
  let F : M.Carrier → ℝ := Subtype.val.extend v 0
  have hFc : Continuous F := HasCompactSupport.continuous_extend_zero hO hvcont hvc
  have hcF : HasCompactSupport F := hvc.extend_zero continuous_subtype_val
  have hsF : tsupport F ⊆ O := by
    apply (hvc.tsupport_extend_zero_subset continuous_subtype_val).trans
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  refine ⟨F, hFc, hcF, hsF, ?_⟩
  rw [← eLpNorm_comp_measurePreserving
    (hf.aestronglyMeasurable.sub hFc.aestronglyMeasurable.restrict) hmp]
  convert hvnorm using 1
  apply congrArg (fun q : O → ℝ => eLpNorm q 2 ν)
  funext x
  simp only [Function.comp_def, Pi.sub_apply, F,
    Subtype.val_injective.extend_apply]

/-- Genuine L² data on O admit smooth compact supported approximations in
the exact restricted measure. No density or boundary trace is assumed. -/
theorem exists_supported_smooth_approx
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O : Set M.Carrier} (hO : IsOpen O) {f : M.Carrier → ℝ}
    (hf : MemLp f 2 (μ.restrict O)) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : M.Carrier → ℝ, SmoothFn k ∧ HasCompactSupport k ∧ tsupport k ⊆ O ∧
      eLpNorm (f - k) 2 (μ.restrict O) ≤ ENNReal.ofReal ε := by
  have hε₂ : 0 < ε / 2 := by positivity
  obtain ⟨F, hFc, hcF, hsF, hfnorm⟩ := exists_supported_continuous_approx g μ hμ hO hf hε₂
  obtain ⟨k, hks, hkc, hksupp, hknorm⟩ :=
    exists_supported_smooth_approx_of_continuous g μ hμ hcF hFc hε₂
  refine ⟨k, hks, hkc, hksupp.trans hsF, ?_⟩
  have heq : f - k = (f - F) - (k - F) := by simp
  grw [heq, eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2), hfnorm,
    eLpNorm_sub_comm (f := k) (g := F) (p := 2) (μ := μ.restrict O),
    eLpNorm_restrict_le (F - k) 2 μ O, hknorm,
    ← ENNReal.ofReal_add hε₂.le hε₂.le, add_halves]

end Yau.Proofs.F03Aux
