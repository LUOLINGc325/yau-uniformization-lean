import Yau.Proofs.F03DirichletComplexHeat
import Yau.LeafProofs.L19HeatFamilyReal

/-! The supported spectral heat family preserves the actual restricted real L² subspace.
Generic scalar complexification maps are reused from native L19. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every real continuous function of the constructed complex resolvent
preserves the actual real subspace. The proof uses the existing CFC's
continuous-function induction, including the closure step. -/
theorem dirichletComplexResolvent_cfc_im_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (spectrum ℝ (dirichletComplexResolvent g μ hμ O)))
    (v : Lp ℂ 2 (μ.restrict O)) (hv : heatLpIm (μ.restrict O) v = 0) :
    heatLpIm (μ.restrict O) (cfc φ (dirichletComplexResolvent g μ hμ O) v) = 0 := by
  let B := dirichletComplexResolvent g μ hμ O
  have hB : IsSelfAdjoint B := dirichletComplexResolvent_selfAdjoint g μ hμ O
  have hBim (v : Lp ℂ 2 (μ.restrict O)) (hv : heatLpIm (μ.restrict O) v = 0) : heatLpIm (μ.restrict O) (B v) = 0 := by
    change heatLpIm (μ.restrict O) (heatComplexify (μ.restrict O) (dirichletResolvent g μ hμ O) v) = 0
    rw [heatComplexify_im, hv, map_zero]
  have hall (F : C(spectrum ℝ B, ℝ)) :
      ∀ v : Lp ℂ 2 (μ.restrict O), heatLpIm (μ.restrict O) v = 0 → heatLpIm (μ.restrict O) (cfcHom hB F v) = 0 := by
    induction F using ContinuousMap.induction_on_of_compact with
    | const r =>
        intro v hv
        have hc : cfcHom hB (ContinuousMap.const (spectrum ℝ B) r) =
            algebraMap ℝ (Lp ℂ 2 (μ.restrict O) →L[ℂ] Lp ℂ 2 (μ.restrict O)) r := (cfcHom hB).commutes r
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
        have hcont : Continuous (fun G : C(spectrum ℝ B, ℝ) => heatLpIm (μ.restrict O) (cfcHom hB G v)) :=
          (heatLpIm (μ.restrict O)).continuous.comp
            ((ContinuousLinearMap.apply ℂ (Lp ℂ 2 (μ.restrict O)) v).continuous.comp (cfcHom_continuous hB))
        exact isClosed_singleton.mem_of_frequently_of_tendsto
          (hF.mono fun G hG => hG v hv) (hcont.tendsto F)
  rw [cfc_apply φ (dirichletComplexResolvent g μ hμ O) hB hφ]
  exact hall _ v hv

theorem dirichletComplexHeat_im_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) (v : Lp ℂ 2 (μ.restrict O))
    (hv : heatLpIm (μ.restrict O) v = 0) : heatLpIm (μ.restrict O) (dirichletComplexHeat g μ hμ O t v) = 0 := by
  unfold dirichletComplexHeat
  split_ifs with ht
  · exact dirichletComplexResolvent_cfc_im_zero g μ hμ O _
      (scalarHeatMultiplier_continuous ht).continuousOn v hv
  · simpa only [one_apply_eq_self] using hv

/-- The actual scalar L² heat operator is the restriction of the fixed
complex CFC construction to the proved invariant real subspace. -/
def dirichletHeat (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) : Lp ℝ 2 (μ.restrict O) →L[ℝ] Lp ℝ 2 (μ.restrict O) :=
  (heatLpRe (μ.restrict O)).comp (((dirichletComplexHeat g μ hμ O t).restrictScalars ℝ).comp (heatLpOfReal (μ.restrict O)))

theorem dirichletHeat_apply (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) (f : Lp ℝ 2 (μ.restrict O)) :
    dirichletHeat g μ hμ O t f = heatLpRe (μ.restrict O) (dirichletComplexHeat g μ hμ O t (heatLpOfReal (μ.restrict O) f)) := rfl

/-- The real family is exactly the original complex construction on real data. -/
theorem dirichletHeat_ofReal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) (f : Lp ℝ 2 (μ.restrict O)) :
    heatLpOfReal (μ.restrict O) (dirichletHeat g μ hμ O t f) =
      dirichletComplexHeat g μ hμ O t (heatLpOfReal (μ.restrict O) f) := by
  have hdec := heatLp_decomposition (μ.restrict O) (dirichletComplexHeat g μ hμ O t (heatLpOfReal (μ.restrict O) f))
  rw [dirichletComplexHeat_im_zero g μ hμ O t _ (heatLpIm_ofReal (μ.restrict O) f), map_zero,
    smul_zero, add_zero] at hdec
  exact hdec

@[simp] theorem dirichletHeat_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) : dirichletHeat g μ hμ O 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change heatLpRe (μ.restrict O) (dirichletComplexHeat g μ hμ O 0 (heatLpOfReal (μ.restrict O) f)) = f
  rw [dirichletComplexHeat_zero, one_apply_eq_self, heatLpRe_ofReal]

theorem dirichletHeat_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) (f : Lp ℝ 2 (μ.restrict O)) :
    ‖dirichletHeat g μ hμ O t f‖ ≤ ‖f‖ := by
  rw [← heatLpOfReal_norm (μ.restrict O) (dirichletHeat g μ hμ O t f), dirichletHeat_ofReal]
  exact (dirichletComplexHeat_norm_le g μ hμ O t _).trans_eq (heatLpOfReal_norm (μ.restrict O) f)

theorem dirichletHeat_opNorm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) : ‖dirichletHeat g μ hμ O t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using dirichletHeat_norm_le g μ hμ O t f

theorem dirichletHeat_adjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) :
    (dirichletHeat g μ hμ O t).adjoint = dirichletHeat g μ hμ O t := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro f k
  change ⟪dirichletHeat g μ hμ O t f, k⟫_ℝ = ⟪f, dirichletHeat g μ hμ O t k⟫_ℝ
  apply Complex.ofReal_injective
  rw [← heatLpOfReal_inner (μ.restrict O), ← heatLpOfReal_inner (μ.restrict O),
    dirichletHeat_ofReal, dirichletHeat_ofReal]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (dirichletComplexHeat_selfAdjoint g μ hμ O t)) (heatLpOfReal (μ.restrict O) f) (heatLpOfReal (μ.restrict O) k)

theorem dirichletHeat_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    dirichletHeat g μ hμ O (s + t) = dirichletHeat g μ hμ O s * dirichletHeat g μ hμ O t := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Function.LeftInverse.injective (heatLpRe_ofReal (μ.restrict O)))
  rw [mul_apply_eq_comp, dirichletHeat_ofReal, dirichletHeat_ofReal,
    dirichletHeat_ofReal, dirichletComplexHeat_add g μ hμ O hs ht, mul_apply_eq_comp]

theorem dirichletHeat_tendsto_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O) (f : Lp ℝ 2 (μ.restrict O)) :
    Tendsto (fun t : ℝ => dirichletHeat g μ hμ O t f) (𝓝[≥] (0 : ℝ)) (𝓝 f) := by
  have h := (heatLpRe (μ.restrict O)).continuous.tendsto (heatLpOfReal (μ.restrict O) f) |>.comp
    (dirichletComplexHeat_tendsto_zero g μ hμ O hO (heatLpOfReal (μ.restrict O) f))
  simpa only [Function.comp_def, dirichletHeat_apply, heatLpRe_ofReal] using h

end Yau.Proofs.F03Aux
