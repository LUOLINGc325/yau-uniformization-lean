import Yau.LeafProofs.L17LocalizedSchauderGlobalJetContinuity

open Set Metric
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem unscale_globalUnitValue (P : UniformChartPartition g) (T : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ) (q : M.Carrier) (t : Time T) :
    unitValue P.radius⁻¹ (globalUnitValue P T v q t) =
      (fun z => globalSum P T v (P.charts.chart q z,t)) := by
  funext z
  change ((P.radius⁻¹)^2)⁻¹ • ((P.radius^2)⁻¹ •
    globalSum P T v (P.charts.chart q (P.radius • (P.radius⁻¹ • z)),t)) = _
  have hScalar : ((P.radius⁻¹)^2)⁻¹*(P.radius^2)⁻¹ = 1 := by field_simp [P.radius_pos.ne']
  simp only [smul_smul,mul_inv_cancel₀ P.radius_pos.ne',one_smul,hScalar]

variable (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ)
    (hTrue : LocalTrueJets P T hT v D H b)

include hTrue

theorem globalSum_chart_hasFDerivAt (q : M.Carrier) (t : Time T)
    {z : ComplexVector n} (hz : z ∈ ball 0 P.radius) :
    HasFDerivAt (fun w => globalSum P T v (P.charts.chart q w,t))
      (P.radius • globalUnitGradient P T v q t (P.radius⁻¹ • z)) z := by
  have hUnit := globalUnitValue_hasFDerivAt P T hT v D H b hTrue q t (inv_radius_smul_mem_unit_ball P hz)
  have h := unitValue_hasFDerivAt (inv_pos.mpr P.radius_pos)
    (globalUnitValue P T v q t) (globalUnitGradient P T v q t) z hUnit
  rw [unscale_globalUnitValue] at h
  simpa only [unitFirstJet,inv_inv] using h

theorem globalSum_chart_gradient_hasFDerivAt (q : M.Carrier) (t : Time T)
    {z : ComplexVector n} (hz : z ∈ ball 0 P.radius) :
    HasFDerivAt (fun w => P.radius • globalUnitGradient P T v q t (P.radius⁻¹ • w))
      (globalUnitHessian P T v q t (P.radius⁻¹ • z)) z := by
  have hUnit := globalUnitGradient_hasFDerivAt P T hT v D H b hTrue q t (inv_radius_smul_mem_unit_ball P hz)
  have h := unitFirstJet_hasFDerivAt (inv_pos.mpr P.radius_pos)
    (globalUnitGradient P T v q t) (globalUnitHessian P T v q t) z hUnit
  have hEq : unitFirstJet P.radius⁻¹ (globalUnitGradient P T v q t) =
      (fun w => P.radius • globalUnitGradient P T v q t (P.radius⁻¹ • w)) := by
    funext w
    simp only [unitFirstJet,inv_inv]
  rw [hEq] at h
  exact h

end Yau.LeafProofs.L17LocalizedSchauderAux
