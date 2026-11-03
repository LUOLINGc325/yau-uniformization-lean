import Yau.Proofs.F03DirichletComplexHeat
import Yau.Proofs.F03GeneratorMultiplier

/-! Actual bounded initial-generator difference operators for the supported heat family. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus

namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ} {M : ComplexManifold n}

def dirichletComplexDifference (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) :
    Lp ℂ 2 (μ.restrict O) →L[ℂ] Lp ℂ 2 (μ.restrict O) :=
  cfc (heatDifferenceMultiplier t) (dirichletComplexResolvent g μ hμ O)

theorem dirichletComplexDifference_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) :
    dirichletComplexDifference g μ hμ O t =
      t⁻¹ • ((dirichletComplexHeat g μ hμ O t - 1) * dirichletComplexResolvent g μ hμ O) := by
  let B := dirichletComplexResolvent g μ hμ O
  have hB : IsSelfAdjoint B := dirichletComplexResolvent_selfAdjoint g μ hμ O
  have hc := scalarHeatMultiplier_continuous ht
  calc
    _ = cfc (fun r => t⁻¹ * ((scalarHeatMultiplier t r - 1) * r)) B := by
      apply cfc_congr
      intro r _
      dsimp [heatDifferenceMultiplier]
      ring
    _ = t⁻¹ • cfc (fun r => (scalarHeatMultiplier t r - 1) * r) B :=
      cfc_const_mul _ _ B ((hc.sub continuous_const).mul continuous_id).continuousOn
    _ = t⁻¹ • ((cfc (scalarHeatMultiplier t) B - 1) * B) := by
      rw [cfc_mul (fun r : ℝ => scalarHeatMultiplier t r - 1) (fun r : ℝ => r) B
        (hc.sub continuous_const).continuousOn continuous_id.continuousOn,
        cfc_sub (f := scalarHeatMultiplier t) (g := fun _ : ℝ => 1) (a := B)
          hc.continuousOn continuous_const.continuousOn,
        cfc_id' ℝ B hB, cfc_const 1 B hB, map_one]
    _ = _ := by rw [dirichletComplexHeat_of_pos g μ hμ O ht]

theorem dirichletComplexDifference_opNorm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) :
    ‖dirichletComplexDifference g μ hμ O t‖ ≤ 1 := by
  unfold dirichletComplexDifference
  apply norm_cfc_le zero_le_one
  intro r hr
  exact heatDifferenceMultiplier_bound ht (dirichletComplexResolvent_spectrum g μ hμ O hr)

theorem dirichletComplexDifference_weighted_error (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    {t : ℝ} (ht : 0 < t) :
    ‖(dirichletComplexDifference g μ hμ O t - (dirichletComplexResolvent g μ hμ O - 1)) *
      dirichletComplexResolvent g μ hμ O‖ ≤ t := by
  let B := dirichletComplexResolvent g μ hμ O
  have hB : IsSelfAdjoint B := dirichletComplexResolvent_selfAdjoint g μ hμ O
  have hc := heatDifferenceMultiplier_continuous ht
  have heq : (dirichletComplexDifference g μ hμ O t - (B - 1)) * B =
      cfc (fun r => (heatDifferenceMultiplier t r - (r - 1)) * r) B := by
    rw [cfc_mul (fun r : ℝ => heatDifferenceMultiplier t r - (r - 1)) (fun r : ℝ => r) B
      (hc.sub (continuous_id.sub continuous_const)).continuousOn continuous_id.continuousOn,
      cfc_sub (f := heatDifferenceMultiplier t) (g := fun r : ℝ => r - 1) (a := B)
        hc.continuousOn (continuous_id.sub continuous_const).continuousOn,
      cfc_sub (f := fun r : ℝ => r) (g := fun _ : ℝ => 1) (a := B)
        continuous_id.continuousOn continuous_const.continuousOn,
      cfc_id' ℝ B hB, cfc_const 1 B hB, map_one]
    rfl
  change ‖(dirichletComplexDifference g μ hμ O t - (B - 1)) * B‖ ≤ t
  rw [heq]
  apply norm_cfc_le ht.le
  intro r hr
  exact heatDifferenceMultiplier_weighted_error ht (dirichletComplexResolvent_spectrum g μ hμ O hr)

end Yau.Proofs.F03Aux
