import Yau.Proofs.C04BoundedGeometryChartsRadialCurvature

/-! Raising the last curvature slot is one fixed bounded linear map, independent of derivative order. -/

noncomputable section
open scoped Topology ContDiff InnerProductSpace
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

def curvatureRaisingMap (n : ℕ) : RealTensorForm n 4 →L[ℝ]
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ComplexVector n) (ComplexVector n) :=
  let R : (ComplexVector n →L[ℝ] ℝ) →L[ℝ] ComplexVector n :=
    (InnerProductSpace.toDual ℝ (ComplexVector n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  (1 / 2 : ℝ) •
    (((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin 3 => ComplexVector n)
      (ComplexVector n →L[ℝ] ℝ) (ComplexVector n)) R).comp
      (continuousMultilinearCurryRightEquiv' ℝ 3 (ComplexVector n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap)

theorem curvatureRaisingMap_apply (T : RealTensorForm n 4) (V : Fin 3 → ComplexVector n) :
    curvatureRaisingMap n T V = (1 / 2 : ℝ) •
      (InnerProductSpace.toDual ℝ (ComplexVector n)).symm (T.curryRight V) := rfl

theorem curvatureRaisingMap_pairing (T : RealTensorForm n 4) (u w z a : ComplexVector n) :
    2 * ⟪a, curvatureRaisingMap n T ![u, w, z]⟫_ℝ = T ![u, w, z, a] := by
  rw [curvatureRaisingMap_apply, real_inner_smul_right, real_inner_comm,
    InnerProductSpace.toDual_symm_apply, ContinuousMultilinearMap.curryRight_apply]
  have hvec : Fin.snoc (![u, w, z] : Fin 3 → ComplexVector n) a =
      (![u, w, z, a] : Fin 4 → ComplexVector n) := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]
  ring

theorem radialConnection_curvature_eq_raising {M : ComplexManifold n}
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v u w z : ComplexVector n) :
    connectionCurvature (radialConnection g p U) v u w z =
      curvatureRaisingMap n (radialCurvatureForm g p U 0 v)
        ![radialCoframe g p U v u, radialCoframe g p U v w, z] := by
  apply ext_inner_left ℝ
  intro a
  have H := radialConnection_curvature_pairing g p U hU v u w z a
  have Hr : ⟪a, connectionCurvature (radialConnection g p U) v u w z⟫_ℝ =
      (⟪a, connectionCurvature (radialConnection g p U) v u w z⟫_ℂ).re := by
    simp only [PiLp.inner_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact real_inner_eq_re_inner ℂ (a i) _
  rw [← Hr] at H
  have HR := curvatureRaisingMap_pairing (radialCurvatureForm g p U 0 v)
    (radialCoframe g p U v u) (radialCoframe g p U v w) z a
  linarith

end Yau.Proofs.C04ChartsAux
