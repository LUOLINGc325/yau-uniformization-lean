import Yau.Proofs.C04BoundedGeometryChartsCurvatureRaising
import Yau.Proofs.C04BoundedGeometryChartsVectorForms

/-! The genuine radial curvature as a smooth operator-valued trilinear map. -/

noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

def radialCurvatureOperator (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ComplexVector n) (ComplexVector n) :=
  (curvatureRaisingMap n (radialCurvatureForm g p U 0 v)).compContinuousLinearMap
    ![radialCoframe g p U v, radialCoframe g p U v, ContinuousLinearMap.id ℝ (ComplexVector n)]

theorem radialCurvatureOperator_apply (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v u w z : ComplexVector n) :
    radialCurvatureOperator g p U v ![u, w, z] =
      connectionCurvature (radialConnection g p U) v u w z := by
  rw [radialConnection_curvature_eq_raising g p U hU]
  unfold radialCurvatureOperator
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem connectionCurvature_smooth
    (conn : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (hc : ContDiff ℝ ∞ conn) (u w z : ComplexVector n) :
    ContDiff ℝ ∞ (fun v => connectionCurvature conn v u w z) := by
  have hD := hc.fderiv_right (m := ∞) (by simp)
  have h₁ := ((hD.clm_apply (contDiff_const (c := u))).clm_apply
    (contDiff_const (c := w))).clm_apply (contDiff_const (c := z))
  have h₂ := ((hD.clm_apply (contDiff_const (c := w))).clm_apply
    (contDiff_const (c := u))).clm_apply (contDiff_const (c := z))
  have h₃ := (hc.clm_apply (contDiff_const (c := u))).clm_apply
    ((hc.clm_apply (contDiff_const (c := w))).clm_apply (contDiff_const (c := z)))
  have h₄ := (hc.clm_apply (contDiff_const (c := w))).clm_apply
    ((hc.clm_apply (contDiff_const (c := u))).clm_apply (contDiff_const (c := z)))
  exact ((h₁.sub h₂).add h₃).sub h₄

theorem radialCurvatureOperator_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) : ContDiff ℝ ∞ (radialCurvatureOperator g p U) := by
  apply vectorForm_smooth_of_basis
  intro idx
  have H := connectionCurvature_smooth (radialConnection g p U) (radialConnection_smooth g p U)
    (realVec (idx 0)) (realVec (idx 1)) (realVec (idx 2))
  convert H using 1
  funext v
  have hvec : (fun j : Fin 3 => realVec (idx j)) =
      ![realVec (idx 0), realVec (idx 1), realVec (idx 2)] := by
    funext j
    fin_cases j <;> rfl
  rw [hvec, radialCurvatureOperator_apply g p U hU]

theorem radialCurvatureOperator_norm_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    ‖radialCurvatureOperator g p U v‖ ≤
      ‖curvatureRaisingMap n‖ * ‖radialCurvatureForm g p U 0 v‖ * ‖radialCoframe g p U v‖ ^ 2 := by
  have hprod : (∏ i : Fin 3,
      ‖(![radialCoframe g p U v, radialCoframe g p U v,
        ContinuousLinearMap.id ℝ (ComplexVector n)] : Fin 3 → _) i‖) ≤ ‖radialCoframe g p U v‖ ^ 2 := by
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one]
    have H := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ComplexVector n)
    nlinarith [mul_nonneg (sq_nonneg ‖radialCoframe g p U v‖)
      (sub_nonneg.mpr H)]
  exact ((curvatureRaisingMap n (radialCurvatureForm g p U 0 v)).norm_compContinuousLinearMap_le _).trans
    (mul_le_mul ((curvatureRaisingMap n).le_opNorm _) hprod
      (Finset.prod_nonneg fun i _ => norm_nonneg _)
      (mul_nonneg (norm_nonneg (curvatureRaisingMap n)) (norm_nonneg (radialCurvatureForm g p U 0 v))))

end Yau.Proofs.C04ChartsAux
