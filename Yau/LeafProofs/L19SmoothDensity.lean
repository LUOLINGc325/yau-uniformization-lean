import Yau.LeafProofs.L19ScalarEnergyCompletion
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Density of the genuine smooth compact scalar domain in the given scalar L² space. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- A continuous compact scalar can be approximated in the actual measure by
smooth scalars supported in the same compact set. -/
theorem exists_smooth_compact_eLpNorm_sub_le_of_continuous
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {f : M.Carrier → ℝ}
    (hcf : HasCompactSupport f) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : M.Carrier → ℝ, SmoothFn k ∧ HasCompactSupport k ∧
      eLpNorm (f - k) 2 μ ≤ ENNReal.ofReal ε := by
  let := L12Aux.manifold_realSmooth M
  let : LocallyCompactSpace M.Carrier := L12Aux.manifold_locallyCompact M
  let : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  by_cases hfzero : f =ᵐ[μ] 0
  · refine ⟨0, smoothFn_const 0, HasCompactSupport.zero, ?_⟩
    rw [eLpNorm_congr_ae (by simpa using hfzero)]
    simp
  have hs₁ : μ (tsupport f) ≠ ⊤ := hcf.measure_lt_top.ne
  have hs₂ : 0 < (μ (tsupport f)).toReal := by
    rw [← Measure.measure_support_eq_zero_iff _] at hfzero
    exact ENNReal.toReal_pos (pos_mono (subset_tsupport f) (pos_of_ne_zero hfzero)).ne' hs₁
  let δ := ε * (μ (tsupport f)).toReal ^ (-(1 / (2 : ℝ)))
  have hδ : 0 < δ := by positivity
  have hδbound : ENNReal.ofReal δ * μ (tsupport f) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hs₁, ENNReal.ofReal_rpow_of_pos hs₂,
      ← ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_le_ofReal_iff hε.le]
    dsimp [δ]
    rw [mul_assoc, ← Real.rpow_add hs₂, neg_add_cancel, Real.rpow_zero, mul_one]
  obtain ⟨k, hkapprox, hksupp⟩ := hf.exists_contMDiff_approx
    𝓘(ℝ, ComplexVector n) ⊤ (ε := fun _ => δ) continuous_const (fun _ => hδ)
  refine ⟨k, smoothFn_of_contMDiff_real k.contMDiff, hcf.mono hksupp, ?_⟩
  apply (eLpNorm_sub_le_of_dist_bdd μ (by simp : (2 : ℝ≥0∞) ≠ ⊤)
    hcf.measurableSet.nullMeasurableSet hδ.le
    (hf.sub k.contMDiff.continuous).aestronglyMeasurable (fun x => ?_)
    (subset_tsupport f) (hksupp.trans (subset_tsupport f))).trans
  · simpa using hδbound
  · rw [dist_comm]
    exact (hkapprox x).le

/-- Actual L² functions admit genuine compactly supported smooth scalar
approximations, with no density premise. -/
theorem exists_smooth_compact_eLpNorm_sub_le
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {f : M.Carrier → ℝ} (hf : MemLp f 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : M.Carrier → ℝ, SmoothFn k ∧ HasCompactSupport k ∧
      eLpNorm (f - k) 2 μ ≤ ENNReal.ofReal ε := by
  let : LocallyCompactSpace M.Carrier := L12Aux.manifold_locallyCompact M
  let : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  have hε₂ : 0 < ε / 2 := by positivity
  have hε₂' : ENNReal.ofReal (ε / 2) ≠ 0 := by positivity
  obtain ⟨k, hkc, hknorm, hkcont, hkmem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hε₂'
  obtain ⟨v, hvs, hvc, hvnorm⟩ :=
    exists_smooth_compact_eLpNorm_sub_le_of_continuous g μ hμ hkc hkcont hε₂
  refine ⟨v, hvs, hvc, ?_⟩
  have heq : f - v = (f - k) - (v - k) := by simp
  grw [heq, eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2), hknorm,
    eLpNorm_sub_comm (f := v) (g := k) (p := 2) (μ := μ), hvnorm,
    ← ENNReal.ofReal_add hε₂.le hε₂.le, add_halves]

/-- The actual L² inclusion of the smooth compact energy domain has dense
range in the original measure. -/
theorem scalarEnergyDomainL2_denseRange (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : DenseRange (scalarEnergyDomainL2 g μ hμ) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  obtain ⟨k, hks, hkc, hknorm⟩ :=
    exists_smooth_compact_eLpNorm_sub_le g μ hμ (Lp.memLp f) hε
  let v : ScalarEnergyDomain g μ hμ := ⟨k, hks, hkc⟩
  refine ⟨scalarEnergyDomainL2 g μ hμ v, ⟨v, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
    ← ENNReal.le_ofReal_iff_toReal_le
      ((Lp.memLp f).sub (Lp.memLp (scalarEnergyDomainL2 g μ hμ v))).eLpNorm_ne_top hε.le]
  convert hknorm using 1
  apply eLpNorm_congr_ae
  filter_upwards [scalarEnergyDomainL2_coe g μ hμ v] with y hy
  simp only [Pi.sub_apply, hy]
  rfl

/-- The canonical inclusion of the actual energy completion also has dense
range in the scalar L² space. -/
theorem scalarEnergyL2_denseRange (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : DenseRange (scalarEnergyL2 g μ hμ) := by
  intro f
  apply closure_mono (s := Set.range (scalarEnergyDomainL2 g μ hμ)) ?_
    (scalarEnergyDomainL2_denseRange g μ hμ f)
  rintro z ⟨v, rfl⟩
  exact ⟨(v : ScalarEnergySpace g μ hμ), scalarEnergyL2_coe g μ hμ v⟩

end Yau.LeafProofs.L19Aux
