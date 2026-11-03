import Yau.LeafProofs.L19HeatFamilyMultiplier
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! The genuine spectral heat family of the actual scalar energy resolvent. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Positive times use the bounded continuous functional calculus of the fixed
variational resolvent. At zero the operator is the identity. -/
def scalarComplexHeat (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  if 0 < t then cfc (scalarHeatMultiplier t) (scalarComplexResolvent g μ hμ) else 1

@[simp] theorem scalarComplexHeat_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : scalarComplexHeat g μ hμ 0 = 1 := by
  simp [scalarComplexHeat]

theorem scalarComplexHeat_of_pos (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 < t) :
    scalarComplexHeat g μ hμ t = cfc (scalarHeatMultiplier t) (scalarComplexResolvent g μ hμ) := by
  simp [scalarComplexHeat, ht]

theorem scalarComplexHeat_selfAdjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) : IsSelfAdjoint (scalarComplexHeat g μ hμ t) := by
  unfold scalarComplexHeat
  split_ifs
  · exact IsSelfAdjoint.cfc
  · exact IsSelfAdjoint.one _

theorem scalarComplexHeat_opNorm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) : ‖scalarComplexHeat g μ hμ t‖ ≤ 1 := by
  unfold scalarComplexHeat
  split_ifs with ht
  · apply norm_cfc_le zero_le_one
    intro s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (scalarHeatMultiplier_nonneg t s)]
    exact scalarHeatMultiplier_le_one ht.le (scalarComplexResolvent_spectrum g μ hμ hs).2
  · exact ContinuousLinearMap.norm_id_le

theorem scalarComplexHeat_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (f : Lp ℂ 2 μ) :
    ‖scalarComplexHeat g μ hμ t f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖scalarComplexHeat g μ hμ t‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right (scalarComplexHeat_opNorm_le g μ hμ t) (norm_nonneg f)
    _ = _ := one_mul _

theorem scalarComplexHeat_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    scalarComplexHeat g μ hμ (s + t) = scalarComplexHeat g μ hμ s * scalarComplexHeat g μ hμ t := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rw [scalarComplexHeat_of_pos g μ hμ (add_pos hs ht),
    scalarComplexHeat_of_pos g μ hμ hs, scalarComplexHeat_of_pos g μ hμ ht,
    ← cfc_mul _ _ _ (scalarHeatMultiplier_continuous hs).continuousOn
      (scalarHeatMultiplier_continuous ht).continuousOn]
  apply cfc_congr
  intro x _
  exact scalarHeatMultiplier_add s t x

/-- Uniform weighted initial estimate. It holds despite the multiplier's
failure to converge uniformly to one at spectral zero. -/
theorem scalarComplexHeat_initial_opNorm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 ≤ t) :
    ‖(scalarComplexHeat g μ hμ t - 1) * scalarComplexResolvent g μ hμ‖ ≤ t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rw [scalarComplexHeat_of_pos g μ hμ ht]
  have hc := scalarHeatMultiplier_continuous ht
  have hB := scalarComplexResolvent_selfAdjoint g μ hμ
  have heq : (cfc (scalarHeatMultiplier t) (scalarComplexResolvent g μ hμ) - 1) *
      scalarComplexResolvent g μ hμ =
      cfc (fun s => (scalarHeatMultiplier t s - 1) * s) (scalarComplexResolvent g μ hμ) := by
    rw [cfc_mul (fun s : ℝ => scalarHeatMultiplier t s - 1) (fun s : ℝ => s)
      (scalarComplexResolvent g μ hμ) (hc.sub continuous_const).continuousOn continuous_id.continuousOn,
      cfc_sub (f := scalarHeatMultiplier t) (g := fun _ : ℝ => 1) (a := scalarComplexResolvent g μ hμ)
        hc.continuousOn continuous_const.continuousOn,
      cfc_id' ℝ _ hB, cfc_const 1 _ hB, map_one]
  rw [heq]
  apply norm_cfc_le ht.le
  intro s hs
  exact scalarHeatMultiplier_initial_bound ht.le (scalarComplexResolvent_spectrum g μ hμ hs)

/-- Strong initial continuity on the dense resolvent range has an explicit
rate controlled by the preimage norm. -/
theorem scalarComplexHeat_initial_range_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {t : ℝ} (ht : 0 ≤ t) (f : Lp ℂ 2 μ) :
    ‖scalarComplexHeat g μ hμ t (scalarComplexResolvent g μ hμ f) -
      scalarComplexResolvent g μ hμ f‖ ≤ t * ‖f‖ := by
  have h := (ContinuousLinearMap.le_opNorm
    ((scalarComplexHeat g μ hμ t - 1) * scalarComplexResolvent g μ hμ) f).trans
    (mul_le_mul_of_nonneg_right (scalarComplexHeat_initial_opNorm g μ hμ ht) (norm_nonneg f))
  simpa only [mul_apply_eq_comp, sub_apply,
    one_apply_eq_self] using h

/-- The fixed CFC family tends strongly to the identity on the full original
complex L² space, by the proved dense range and its contraction bound. -/
theorem scalarComplexHeat_tendsto_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : Lp ℂ 2 μ) :
    Tendsto (fun t : ℝ => scalarComplexHeat g μ hμ t f) (𝓝[≥] (0 : ℝ)) (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨v, hv⟩ := (scalarComplexResolvent_denseRange g μ hμ).exists_dist_lt f
    (show 0 < ε / 4 by positivity)
  rw [dist_eq_norm] at hv
  let δ := ε / (2 * (‖v‖ + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hevent : ∀ᶠ t : ℝ in 𝓝[≥] (0 : ℝ), t < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hevent] with t ht htδ
  have ht₀ : 0 ≤ t := ht
  have hsmall : t * ‖v‖ < ε / 2 := by
    calc
      t * ‖v‖ ≤ t * (‖v‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) ht₀
      _ < δ * (‖v‖ + 1) := mul_lt_mul_of_pos_right htδ (by positivity)
      _ = ε / 2 := by dsimp [δ]; field_simp
  rw [dist_eq_norm]
  have heq : scalarComplexHeat g μ hμ t f - f =
      scalarComplexHeat g μ hμ t (f - scalarComplexResolvent g μ hμ v) +
        (scalarComplexHeat g μ hμ t (scalarComplexResolvent g μ hμ v) -
          scalarComplexResolvent g μ hμ v) + (scalarComplexResolvent g μ hμ v - f) := by
    simp only [map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖scalarComplexHeat g μ hμ t (f - scalarComplexResolvent g μ hμ v)‖ +
        ‖scalarComplexHeat g μ hμ t (scalarComplexResolvent g μ hμ v) -
          scalarComplexResolvent g μ hμ v‖ + ‖scalarComplexResolvent g μ hμ v - f‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ‖f - scalarComplexResolvent g μ hμ v‖ + t * ‖v‖ +
        ‖scalarComplexResolvent g μ hμ v - f‖ := by
      gcongr
      · exact scalarComplexHeat_norm_le g μ hμ t _
      · exact scalarComplexHeat_initial_range_bound g μ hμ ht₀ v
    _ < ε := by rw [norm_sub_rev (scalarComplexResolvent g μ hμ v) f]; linarith

end Yau.LeafProofs.L19Aux
