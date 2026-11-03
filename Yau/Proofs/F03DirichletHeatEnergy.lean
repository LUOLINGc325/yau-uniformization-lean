import Yau.Proofs.F03DirichletHeat
import Yau.LeafProofs.L19HeatFamilyPositiveTime

/-! Actual positive-time supported energy representatives from the fixed supported resolvent. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

/-- This is an actual bounded operator defined by the fixed continuous
functional calculus, with no chosen heat-family premise. -/
def dirichletComplexHeatInverse (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) : Lp ℂ 2 (μ.restrict O) →L[ℂ] Lp ℂ 2 (μ.restrict O) :=
  cfc (scalarHeatInverseMultiplier t) (dirichletComplexResolvent g μ hμ O)

theorem dirichletComplexHeat_factor (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) :
    dirichletComplexHeat g μ hμ O t = dirichletComplexResolvent g μ hμ O * dirichletComplexHeatInverse g μ hμ O t := by
  rw [dirichletComplexHeat_of_pos g μ hμ O ht, dirichletComplexHeatInverse]
  calc
    _ = cfc (fun s => s * scalarHeatInverseMultiplier t s) (dirichletComplexResolvent g μ hμ O) := by
      apply cfc_congr
      intro s _
      exact (scalarHeatInverseMultiplier_mul t s).symm
    _ = cfc (fun s : ℝ => s) (dirichletComplexResolvent g μ hμ O) *
        cfc (scalarHeatInverseMultiplier t) (dirichletComplexResolvent g μ hμ O) :=
      cfc_mul _ _ _ continuous_id.continuousOn (scalarHeatInverseMultiplier_continuous ht).continuousOn
    _ = _ := by rw [cfc_id' ℝ _ (dirichletComplexResolvent_selfAdjoint g μ hμ O)]

theorem dirichletComplexHeatInverse_im_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) (v : Lp ℂ 2 (μ.restrict O))
    (hv : heatLpIm (μ.restrict O) v = 0) : heatLpIm (μ.restrict O) (dirichletComplexHeatInverse g μ hμ O t v) = 0 :=
  dirichletComplexResolvent_cfc_im_zero g μ hμ O _ (scalarHeatInverseMultiplier_continuous ht).continuousOn v hv

def dirichletHeatInverse (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) : Lp ℝ 2 (μ.restrict O) →L[ℝ] Lp ℝ 2 (μ.restrict O) :=
  (heatLpRe (μ.restrict O)).comp (((dirichletComplexHeatInverse g μ hμ O t).restrictScalars ℝ).comp (heatLpOfReal (μ.restrict O)))

theorem dirichletHeatInverse_apply (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) (f : Lp ℝ 2 (μ.restrict O)) :
    dirichletHeatInverse g μ hμ O t f = heatLpRe (μ.restrict O) (dirichletComplexHeatInverse g μ hμ O t (heatLpOfReal (μ.restrict O) f)) := rfl

theorem dirichletHeatInverse_ofReal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict O)) :
    heatLpOfReal (μ.restrict O) (dirichletHeatInverse g μ hμ O t f) =
      dirichletComplexHeatInverse g μ hμ O t (heatLpOfReal (μ.restrict O) f) := by
  have hd := heatLp_decomposition (μ.restrict O) (dirichletComplexHeatInverse g μ hμ O t (heatLpOfReal (μ.restrict O) f))
  rw [dirichletComplexHeatInverse_im_zero g μ hμ O ht _ (heatLpIm_ofReal (μ.restrict O) f), map_zero,
    smul_zero, add_zero] at hd
  exact hd

theorem dirichletHeat_factor (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) :
    dirichletHeat g μ hμ O t = dirichletResolvent g μ hμ O * dirichletHeatInverse g μ hμ O t := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Function.LeftInverse.injective (heatLpRe_ofReal (μ.restrict O)))
  rw [mul_apply_eq_comp, dirichletHeat_ofReal, ← dirichletComplexResolvent_ofReal,
    dirichletHeatInverse_ofReal g μ hμ O ht, dirichletComplexHeat_factor g μ hμ O ht, mul_apply_eq_comp]

/-- The actual energy representative of the positive-time heat flow. -/
def dirichletHeatEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) : Lp ℝ 2 (μ.restrict O) →L[ℝ] DirichletEnergy g μ hμ O :=
  (dirichletL2 g μ hμ O).adjoint.comp (dirichletHeatInverse g μ hμ O t)

theorem dirichletHeatEnergy_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict O)) :
    dirichletL2 g μ hμ O (dirichletHeatEnergy g μ hμ O t f) = dirichletHeat g μ hμ O t f := by
  rw [dirichletHeat_factor g μ hμ O ht, dirichletResolvent]
  rfl

theorem dirichletHeatEnergy_weak (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict O))
    (v : DirichletEnergy g μ hμ O) :
    dirichletClosedEnergy g μ hμ O (dirichletHeatEnergy g μ hμ O t f) v =
      ⟪dirichletHeatInverse g μ hμ O t f - dirichletHeat g μ hμ O t f,
        dirichletL2 g μ hμ O v⟫_ℝ := by
  rw [dirichletClosedEnergy, dirichletHeatEnergy_L2 g μ hμ O ht, inner_sub_left]
  change ⟪(dirichletL2 g μ hμ O).adjoint (dirichletHeatInverse g μ hμ O t f), v⟫_ℝ - _ = _
  rw [ContinuousLinearMap.adjoint_inner_left]

end Yau.Proofs.F03Aux
