import Yau.LeafProofs.L05AutonomousSecondWeight

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

/-- The positive second FTC average converges to the genuine directional Hessian. -/
theorem auto_spatial_second_limit {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (x e : Space n) : Tendsto (fun h => autoSpatialSecond f e h x) (𝓝[>] 0)
      (𝓝 (fderiv ℝ (fderiv ℝ f) x e e)) := by
  let H : Space n → ℝ := fun z => fderiv ℝ (fderiv ℝ f) z e e
  have hH : Continuous H :=
    (((((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const).clm_apply contDiff_const).continuous)
  let : IsProbabilityMeasure autoTentMeasure := autoTentMeasure_isProbability
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  obtain ⟨delta,hdelta,hclose⟩ := Metric.continuousAt_iff.mp hH.continuousAt (eta/2) (half_pos heta)
  have hevent : Ioo (0 : ℝ) (delta/(‖e‖+1))∈𝓝[>] 0 :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨_,div_pos hdelta (by positivity),subset_rfl⟩
  filter_upwards [hevent] with h hh
  let path : ℝ → Space n := fun s => x+(s*h) • e
  have hc : Continuous (fun s => H (path s)) :=
    hH.comp (continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const))
  have hInt := autoTentMeasure_continuous_integrable hc
  have hDiff : autoSpatialSecond f e h x-H x=∫ s, (H (path s)-H x) ∂autoTentMeasure := by
    rw [auto_spatial_second_as_probability hf x e hh.1.ne',integral_sub hInt (integrable_const _),
      integral_const,probReal_univ,one_smul]
  have hBound := norm_integral_le_of_norm_le_const (μ := autoTentMeasure)
    (f := fun s => H (path s)-H x) (C := eta/2) (by
      filter_upwards [autoTentMeasure_interval_ae] with s hs
      have hsabs : |s| ≤ 1 := abs_le.mpr hs
      have hhdelta : h*(‖e‖+1) < delta := (lt_div_iff₀ (by positivity)).mp hh.2
      have hd : dist (path s) x < delta := by
        rw [dist_eq_norm,show path s-x=(s*h) • e by dsimp only [path];abel,
          norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos hh.1]
        have hb := mul_le_mul_of_nonneg_right hsabs (mul_nonneg hh.1.le (norm_nonneg e))
        nlinarith only [hb,hhdelta,hh.1]
      simpa only [dist_eq_norm] using (hclose hd).le)
  rw [dist_eq_norm,hDiff]
  exact (by simpa only [probReal_univ,mul_one] using hBound : ‖∫ s, (H (path s)-H x) ∂autoTentMeasure‖ ≤ eta/2).trans_lt
    (half_lt_self heta)

end Yau.LeafProofs.L05AutonomousAux
