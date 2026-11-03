import Yau.Proofs.F03DirichletComplexResolvent
import Yau.LeafProofs.L19HeatFamilyMultiplier
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! The genuine spectral family of the constructed supported Dirichlet resolvent.
The scalar multiplier estimates are reused from native L19. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Positive times use the bounded continuous functional calculus of the fixed
variational resolvent. At zero the operator is the identity. -/
def dirichletComplexHeat (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) : Lp ℂ 2 (μ.restrict O) →L[ℂ] Lp ℂ 2 (μ.restrict O) :=
  if 0 < t then cfc (scalarHeatMultiplier t) (dirichletComplexResolvent g μ hμ O) else 1

@[simp] theorem dirichletComplexHeat_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) : dirichletComplexHeat g μ hμ O 0 = 1 := by
  simp [dirichletComplexHeat]

theorem dirichletComplexHeat_of_pos (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) :
    dirichletComplexHeat g μ hμ O t = cfc (scalarHeatMultiplier t) (dirichletComplexResolvent g μ hμ O) := by
  simp [dirichletComplexHeat, ht]

theorem dirichletComplexHeat_selfAdjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) : IsSelfAdjoint (dirichletComplexHeat g μ hμ O t) := by
  unfold dirichletComplexHeat
  split_ifs
  · exact IsSelfAdjoint.cfc
  · exact IsSelfAdjoint.one _

theorem dirichletComplexHeat_opNorm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) : ‖dirichletComplexHeat g μ hμ O t‖ ≤ 1 := by
  unfold dirichletComplexHeat
  split_ifs with ht
  · apply norm_cfc_le zero_le_one
    intro s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (scalarHeatMultiplier_nonneg t s)]
    exact scalarHeatMultiplier_le_one ht.le (dirichletComplexResolvent_spectrum g μ hμ O hs).2
  · exact ContinuousLinearMap.norm_id_le

theorem dirichletComplexHeat_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) (f : Lp ℂ 2 (μ.restrict O)) :
    ‖dirichletComplexHeat g μ hμ O t f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖dirichletComplexHeat g μ hμ O t‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right (dirichletComplexHeat_opNorm_le g μ hμ O t) (norm_nonneg f)
    _ = _ := one_mul _

theorem dirichletComplexHeat_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    dirichletComplexHeat g μ hμ O (s + t) = dirichletComplexHeat g μ hμ O s * dirichletComplexHeat g μ hμ O t := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rw [dirichletComplexHeat_of_pos g μ hμ O (add_pos hs ht),
    dirichletComplexHeat_of_pos g μ hμ O hs, dirichletComplexHeat_of_pos g μ hμ O ht,
    ← cfc_mul _ _ _ (scalarHeatMultiplier_continuous hs).continuousOn
      (scalarHeatMultiplier_continuous ht).continuousOn]
  apply cfc_congr
  intro x _
  exact scalarHeatMultiplier_add s t x

/-- Uniform weighted initial estimate. It holds despite the multiplier's
failure to converge uniformly to one at spectral zero. -/
theorem dirichletComplexHeat_initial_opNorm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 ≤ t) :
    ‖(dirichletComplexHeat g μ hμ O t - 1) * dirichletComplexResolvent g μ hμ O‖ ≤ t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rw [dirichletComplexHeat_of_pos g μ hμ O ht]
  have hc := scalarHeatMultiplier_continuous ht
  have hB := dirichletComplexResolvent_selfAdjoint g μ hμ O
  have heq : (cfc (scalarHeatMultiplier t) (dirichletComplexResolvent g μ hμ O) - 1) *
      dirichletComplexResolvent g μ hμ O =
      cfc (fun s => (scalarHeatMultiplier t s - 1) * s) (dirichletComplexResolvent g μ hμ O) := by
    rw [cfc_mul (fun s : ℝ => scalarHeatMultiplier t s - 1) (fun s : ℝ => s)
      (dirichletComplexResolvent g μ hμ O) (hc.sub continuous_const).continuousOn continuous_id.continuousOn,
      cfc_sub (f := scalarHeatMultiplier t) (g := fun _ : ℝ => 1) (a := dirichletComplexResolvent g μ hμ O)
        hc.continuousOn continuous_const.continuousOn,
      cfc_id' ℝ _ hB, cfc_const 1 _ hB, map_one]
  rw [heq]
  apply norm_cfc_le ht.le
  intro s hs
  exact scalarHeatMultiplier_initial_bound ht.le (dirichletComplexResolvent_spectrum g μ hμ O hs)

/-- Strong initial continuity on the dense resolvent range has an explicit
rate controlled by the preimage norm. -/
theorem dirichletComplexHeat_initial_range_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 ≤ t) (f : Lp ℂ 2 (μ.restrict O)) :
    ‖dirichletComplexHeat g μ hμ O t (dirichletComplexResolvent g μ hμ O f) -
      dirichletComplexResolvent g μ hμ O f‖ ≤ t * ‖f‖ := by
  have h := (ContinuousLinearMap.le_opNorm
    ((dirichletComplexHeat g μ hμ O t - 1) * dirichletComplexResolvent g μ hμ O) f).trans
    (mul_le_mul_of_nonneg_right (dirichletComplexHeat_initial_opNorm g μ hμ O ht) (norm_nonneg f))
  simpa only [mul_apply_eq_comp, sub_apply,
    one_apply_eq_self] using h

/-- The fixed CFC family tends strongly to the identity on the full original
complex L² space, by the proved dense range and its contraction bound. -/
theorem dirichletComplexHeat_tendsto_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O) (f : Lp ℂ 2 (μ.restrict O)) :
    Tendsto (fun t : ℝ => dirichletComplexHeat g μ hμ O t f) (𝓝[≥] (0 : ℝ)) (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨v, hv⟩ := (dirichletComplexResolvent_denseRange g μ hμ O hO).exists_dist_lt f
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
  have heq : dirichletComplexHeat g μ hμ O t f - f =
      dirichletComplexHeat g μ hμ O t (f - dirichletComplexResolvent g μ hμ O v) +
        (dirichletComplexHeat g μ hμ O t (dirichletComplexResolvent g μ hμ O v) -
          dirichletComplexResolvent g μ hμ O v) + (dirichletComplexResolvent g μ hμ O v - f) := by
    simp only [map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖dirichletComplexHeat g μ hμ O t (f - dirichletComplexResolvent g μ hμ O v)‖ +
        ‖dirichletComplexHeat g μ hμ O t (dirichletComplexResolvent g μ hμ O v) -
          dirichletComplexResolvent g μ hμ O v‖ + ‖dirichletComplexResolvent g μ hμ O v - f‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ‖f - dirichletComplexResolvent g μ hμ O v‖ + t * ‖v‖ +
        ‖dirichletComplexResolvent g μ hμ O v - f‖ := by
      gcongr
      · exact dirichletComplexHeat_norm_le g μ hμ O t _
      · exact dirichletComplexHeat_initial_range_bound g μ hμ O ht₀ v
    _ < ε := by rw [norm_sub_rev (dirichletComplexResolvent g μ hμ O v) f]; linarith

end Yau.Proofs.F03Aux
