import Yau.Proofs.G04SignedFormAlgebra
import Yau.Proofs.G01KahlerClosure

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem chartVec_std_expansion (x y : M.Carrier) (u : ComplexVector n) :
    (∑ a, u a • chartVec x y (stdVec a)) = chartVec x y u := by
  have hu : (∑ a, u a • stdVec a) = u := by
    ext a
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  calc
    (∑ a, u a • chartVec x y (stdVec a)) = chartVec x y (∑ a, u a • stdVec a) := by
      rw [L12Aux.chartVec_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact (L12Aux.chartVec_complex_smul x y _ _).symm
    _ = chartVec x y u := congrArg (chartVec x y) hu

theorem hMat_matrixPairing (h : HermitianField M) (x : M.Carrier) (z u v : ComplexVector n) :
    matrixPairing (hMat h x z) u v =
      (h (chartInv x z)).toFun (chartVec x (chartInv x z) u) (chartVec x (chartInv x z) v) := by
  rw [← chartVec_std_expansion x (chartInv x z) u,
    ← chartVec_std_expansion x (chartInv x z) v, L12Aux.hermitian_sum_left]
  simp only [L12Aux.hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right, matrixPairing, hMat]

def omegaForm (h : HermitianField M) : RealForm M 2 :=
  iotaRealForm (gMat h) (fun x => L12Aux.hMat_isHermitian h x (chartPt x x))

theorem omegaForm_apply (h : HermitianField M) (x : M.Carrier) (u v : TangentVector M x) :
    omegaForm h x ![u, v] = 2 * ((h x).toFun u v).im := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have he := hMat_matrixPairing h x (chartPt x x) (tangentCoords x x u) (tangentCoords x x v)
  rw [hx, L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x),
    L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x)] at he
  change matrixPairing (gMat h x) (tangentCoords x x u) (tangentCoords x x v) = (h x).toFun u v at he
  change 2 * (matrixPairing (gMat h x) (tangentCoords x x u) (tangentCoords x x v)).im = _
  rw [he]

theorem omegaForm_components (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (I : Fin 2 → RIdx n) :
    formComponents (omegaForm h) x z I = kahlerFormFn h x z (I 0) (I 1) := by
  have he : (fun r => chartVec x (chartInv x z) (realVec (I r))) =
      ![chartVec x (chartInv x z) (realVec (I 0)), chartVec x (chartInv x z) (realVec (I 1))] := by
    ext r
    fin_cases r <;> rfl
  unfold formComponents
  rw [he, omegaForm_apply]
  rfl

theorem omegaForm_smooth (h : HermitianField M) (hs : MetricSmooth h) :
    SmoothRealForm (omegaForm h) := by
  intro x I
  have he : (fun z => formComponents (omegaForm h) x z I) =
      (fun z => L12Aux.jSign (I 0) * realMetricFn h x z (L12Aux.jIndex n (I 0)) (I 1)) := by
    funext z
    rw [omegaForm_components, L12Aux.kahlerFormFn_eq_jIndex_metric]
  rw [he]
  exact contDiffOn_const.mul (hs x _ _)

theorem omegaForm_oneOne (h : HermitianField M) : RealOneOne (omegaForm h) :=
  iotaRealForm_oneOne (gMat h) (fun x => L12Aux.hMat_isHermitian h x (chartPt x x))

theorem omegaForm_represents (h : HermitianField M) : RepresentsIota (gMat h) (omegaForm h) :=
  iotaRealForm_represents (gMat h) (fun x => L12Aux.hMat_isHermitian h x (chartPt x x))

theorem omegaForm_closed (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) :
    ClosedRealForm (omegaForm h) := by
  intro x z hz I
  have hc := G01Aux.kahlerClosed_in_chart h hs hk x hz (I 0) (I 1) (I 2)
  have hskew : (fun w => kahlerFormFn h x w (I 2) (I 0)) =
      (fun w => -kahlerFormFn h x w (I 0) (I 2)) := by
    funext w
    unfold kahlerFormFn
    rw [(h (chartInv x w)).conjugate_symmetric]
    simp
  rw [hskew] at hc
  simp only [rDeriv, fderiv_fun_neg, ContinuousLinearMap.neg_apply] at hc
  unfold exteriorComponents
  simp only [omegaForm_components]
  simp [Fin.sum_univ_succ, Fin.succAbove, rDeriv] at ⊢
  linarith

end Yau.NodeProofs.G04Aux
