import Yau.Proofs.F03DirichletHeat
import Yau.Proofs.F03DirichletStepRelations
import Yau.LeafProofs.L19HeatMarkovResolvent

/-! The actual supported Euler resolvents have the forced bounded rational CFC formula. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual Euler operator relation, complexified by the explicit L² maps. -/
theorem dirichletComplexEuler_relation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h) :
    heatComplexify (μ.restrict O) (dirichletStepResolvent g μ hμ O h hh) *
      (h • (1 : Lp ℂ 2 (μ.restrict O) →L[ℂ] Lp ℂ 2 (μ.restrict O)) + (1 - h) • dirichletComplexResolvent g μ hμ O) =
        dirichletComplexResolvent g μ hμ O := by
  have heq := congrArg (heatComplexify (μ.restrict O))
    (dirichletStepResolvent_euler_operator_relation g μ hμ O h hh)
  rw [dirichletStepResolvent_one_ident g μ hμ O] at heq
  change heatComplexify (μ.restrict O) (dirichletStepResolvent g μ hμ O h hh *
    (h • 1 + (1 - h) • dirichletResolvent g μ hμ O)) =
      dirichletComplexResolvent g μ hμ O at heq
  simpa only [heatComplexify_mul, heatComplexify_add, heatComplexify_smul,
    heatComplexify_one, dirichletComplexResolvent] using heq

/-- The rational CFC formula is forced by the genuine variational relation. -/
theorem dirichletStepResolvent_complexify_eq_cfc (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h) :
    heatComplexify (μ.restrict O) (dirichletStepResolvent g μ hμ O h hh) =
      cfc (scalarEulerMultiplier h) (dirichletComplexResolvent g μ hμ O) := by
  let B := dirichletComplexResolvent g μ hμ O
  have hB : IsSelfAdjoint B := dirichletComplexResolvent_selfAdjoint g μ hμ O
  let d : ℝ → ℝ := fun s => h + (1 - h) * s
  have hd : ContinuousOn d (spectrum ℝ B) := by fun_prop
  have hdn : ∀ s ∈ spectrum ℝ B, d s ≠ 0 := fun s hs =>
    (scalarEuler_denominator_pos hh (dirichletComplexResolvent_spectrum g μ hμ O hs)).ne'
  have hdi := hd.inv₀ hdn
  have hT : cfc d B = h • (1 : Lp ℂ 2 (μ.restrict O) →L[ℂ] Lp ℂ 2 (μ.restrict O)) + (1 - h) • B := by
    change cfc (fun s => h + (1 - h) * s) B = _
    rw [cfc_add (a := B) (fun _ => h) (fun s => (1 - h) * s) continuous_const.continuousOn (by fun_prop), cfc_const h B hB,
      Algebra.algebraMap_eq_smul_one, cfc_const_mul_id (1 - h) B hB]
  have hTD : cfc d B * cfc (fun s => (d s)⁻¹) B = 1 := by
    rw [← cfc_mul d (fun s => (d s)⁻¹) B hd hdi, ← cfc_const_one ℝ B hB]
    exact cfc_congr fun s hs => mul_inv_cancel₀ (hdn s hs)
  have hR := dirichletComplexEuler_relation g μ hμ O h hh
  change heatComplexify (μ.restrict O) (dirichletStepResolvent g μ hμ O h hh) *
    (h • 1 + (1 - h) • B) = B at hR
  rw [← hT] at hR
  calc
    heatComplexify (μ.restrict O) (dirichletStepResolvent g μ hμ O h hh) =
        heatComplexify (μ.restrict O) (dirichletStepResolvent g μ hμ O h hh) *
          (cfc d B * cfc (fun s => (d s)⁻¹) B) := by rw [hTD, mul_one]
    _ = B * cfc (fun s => (d s)⁻¹) B := by rw [← mul_assoc, hR]
    _ = cfc (scalarEulerMultiplier h) B := by
      calc
        _ = cfc (fun s : ℝ => s) B * cfc (fun s => (d s)⁻¹) B := by rw [cfc_id' ℝ B hB]
        _ = cfc (fun s => s * (d s)⁻¹) B := (cfc_mul _ _ B continuous_id.continuousOn hdi).symm
        _ = _ := rfl

end Yau.Proofs.F03Aux
