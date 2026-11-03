import Yau.LeafProofs.L19HeatFamily

/-! The fixed spectral family preserves the actual real L² subspace. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every real continuous function of the constructed complex resolvent
preserves the actual real subspace. The proof uses the existing CFC's
continuous-function induction, including the closure step. -/
theorem scalarComplexResolvent_cfc_im_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (spectrum ℝ (scalarComplexResolvent g μ hμ)))
    (v : Lp ℂ 2 μ) (hv : heatLpIm μ v = 0) :
    heatLpIm μ (cfc φ (scalarComplexResolvent g μ hμ) v) = 0 := by
  let B := scalarComplexResolvent g μ hμ
  have hB : IsSelfAdjoint B := scalarComplexResolvent_selfAdjoint g μ hμ
  have hBim (v : Lp ℂ 2 μ) (hv : heatLpIm μ v = 0) : heatLpIm μ (B v) = 0 := by
    change heatLpIm μ (heatComplexify μ (scalarResolvent g μ hμ 1 zero_lt_one) v) = 0
    rw [heatComplexify_im, hv, map_zero]
  have hall (F : C(spectrum ℝ B, ℝ)) :
      ∀ v : Lp ℂ 2 μ, heatLpIm μ v = 0 → heatLpIm μ (cfcHom hB F v) = 0 := by
    induction F using ContinuousMap.induction_on_of_compact with
    | const r =>
        intro v hv
        have hc : cfcHom hB (ContinuousMap.const (spectrum ℝ B) r) =
            algebraMap ℝ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) r := (cfcHom hB).commutes r
        rw [hc, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self,
          map_smul, hv, smul_zero]
    | id =>
        intro v hv
        rw [cfcHom_id]
        exact hBim v hv
    | star_id =>
        intro v hv
        rw [map_star, cfcHom_id, hB.star_eq]
        exact hBim v hv
    | add F G hF hG =>
        intro v hv
        rw [map_add, add_apply, map_add, hF v hv, hG v hv, add_zero]
    | mul F G hF hG =>
        intro v hv
        rw [map_mul, mul_apply_eq_comp]
        exact hF _ (hG v hv)
    | frequently F hF =>
        intro v hv
        have hcont : Continuous (fun G : C(spectrum ℝ B, ℝ) => heatLpIm μ (cfcHom hB G v)) :=
          (heatLpIm μ).continuous.comp
            ((ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) v).continuous.comp (cfcHom_continuous hB))
        exact isClosed_singleton.mem_of_frequently_of_tendsto
          (hF.mono fun G hG => hG v hv) (hcont.tendsto F)
  rw [cfc_apply φ (scalarComplexResolvent g μ hμ) hB hφ]
  exact hall _ v hv

theorem scalarComplexHeat_im_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (v : Lp ℂ 2 μ)
    (hv : heatLpIm μ v = 0) : heatLpIm μ (scalarComplexHeat g μ hμ t v) = 0 := by
  unfold scalarComplexHeat
  split_ifs with ht
  · exact scalarComplexResolvent_cfc_im_zero g μ hμ _
      (scalarHeatMultiplier_continuous ht).continuousOn v hv
  · simpa only [one_apply_eq_self] using hv

/-- The actual scalar L² heat operator is the restriction of the fixed
complex CFC construction to the proved invariant real subspace. -/
def scalarHeatFamily (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (heatLpRe μ).comp (((scalarComplexHeat g μ hμ t).restrictScalars ℝ).comp (heatLpOfReal μ))

theorem scalarHeatFamily_apply (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (f : Lp ℝ 2 μ) :
    scalarHeatFamily g μ hμ t f = heatLpRe μ (scalarComplexHeat g μ hμ t (heatLpOfReal μ f)) := rfl

/-- The real family is exactly the original complex construction on real data. -/
theorem scalarHeatFamily_ofReal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (f : Lp ℝ 2 μ) :
    heatLpOfReal μ (scalarHeatFamily g μ hμ t f) =
      scalarComplexHeat g μ hμ t (heatLpOfReal μ f) := by
  have hdec := heatLp_decomposition μ (scalarComplexHeat g μ hμ t (heatLpOfReal μ f))
  rw [scalarComplexHeat_im_zero g μ hμ t _ (heatLpIm_ofReal μ f), map_zero,
    smul_zero, add_zero] at hdec
  exact hdec

@[simp] theorem scalarHeatFamily_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : scalarHeatFamily g μ hμ 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change heatLpRe μ (scalarComplexHeat g μ hμ 0 (heatLpOfReal μ f)) = f
  rw [scalarComplexHeat_zero, one_apply_eq_self, heatLpRe_ofReal]

theorem heatLpOfReal_norm {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : Lp ℝ 2 μ) :
    ‖heatLpOfReal μ f‖ = ‖f‖ := by
  have h := heatLp_norm_sq μ (heatLpOfReal μ f)
  simp only [heatLpRe_ofReal, heatLpIm_ofReal, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    add_zero] at h
  nlinarith [norm_nonneg (heatLpOfReal μ f), norm_nonneg f]

theorem scalarHeatFamily_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) (f : Lp ℝ 2 μ) :
    ‖scalarHeatFamily g μ hμ t f‖ ≤ ‖f‖ := by
  rw [← heatLpOfReal_norm μ (scalarHeatFamily g μ hμ t f), scalarHeatFamily_ofReal]
  exact (scalarComplexHeat_norm_le g μ hμ t _).trans_eq (heatLpOfReal_norm μ f)

theorem scalarHeatFamily_opNorm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) : ‖scalarHeatFamily g μ hμ t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using scalarHeatFamily_norm_le g μ hμ t f

theorem scalarHeatFamily_adjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (t : ℝ) :
    (scalarHeatFamily g μ hμ t).adjoint = scalarHeatFamily g μ hμ t := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro f k
  change ⟪scalarHeatFamily g μ hμ t f, k⟫_ℝ = ⟪f, scalarHeatFamily g μ hμ t k⟫_ℝ
  apply Complex.ofReal_injective
  rw [← heatLpOfReal_inner μ, ← heatLpOfReal_inner μ,
    scalarHeatFamily_ofReal, scalarHeatFamily_ofReal]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (scalarComplexHeat_selfAdjoint g μ hμ t)) (heatLpOfReal μ f) (heatLpOfReal μ k)

theorem scalarHeatFamily_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    scalarHeatFamily g μ hμ (s + t) = scalarHeatFamily g μ hμ s * scalarHeatFamily g μ hμ t := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Function.LeftInverse.injective (heatLpRe_ofReal μ))
  rw [mul_apply_eq_comp, scalarHeatFamily_ofReal, scalarHeatFamily_ofReal,
    scalarHeatFamily_ofReal, scalarComplexHeat_add g μ hμ hs ht, mul_apply_eq_comp]

theorem scalarHeatFamily_tendsto_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ) :
    Tendsto (fun t : ℝ => scalarHeatFamily g μ hμ t f) (𝓝[≥] (0 : ℝ)) (𝓝 f) := by
  have h := (heatLpRe μ).continuous.tendsto (heatLpOfReal μ f) |>.comp
    (scalarComplexHeat_tendsto_zero g μ hμ (heatLpOfReal μ f))
  simpa only [Function.comp_def, scalarHeatFamily_apply, heatLpRe_ofReal] using h

end Yau.LeafProofs.L19Aux
