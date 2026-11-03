import Yau.Proofs.P03TensorFibres

open scoped Manifold Topology TensorProduct

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n : ℕ} {M : ComplexManifold n}

theorem determinantFrameBasis_repr (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (v : TangentVector M x) (i : Fin n) :
    (determinantFrameBasis a x hx).repr v i = tangentCoords a x v i := by
  change (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.repr
    ((chartFrameEquiv a x hx).symm v) i = _
  rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rfl

def determinantTransition (a b x : M.Carrier) : ComplexVector n →L[ℂ] ComplexVector n :=
  (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) b) x).comp
    (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) a).symm
      (chartPt a x))

@[simp] theorem determinantTransition_apply (a b x : M.Carrier) (v : ComplexVector n) :
    determinantTransition a b x v = tangentCoords b x (chartVec a x v) := rfl

def determinantTransitionMatrix (a b x : M.Carrier) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => determinantTransition a b x (stdVec j) i

theorem determinantTransitionMatrix_eq_basisMatrix (a b x : M.Carrier)
    (ha : x ∈ (extChartAt (ComplexModel n) a).source)
    (hb : x ∈ (extChartAt (ComplexModel n) b).source) :
    determinantTransitionMatrix a b x =
      (determinantFrameBasis b x hb).toMatrix (determinantFrameBasis a x ha) := by
  ext i j
  simp only [Module.Basis.toMatrix_apply, determinantFrameBasis_repr,
    determinantFrameBasis_apply, determinantTransitionMatrix, determinantTransition_apply]

theorem determinantTransitionMatrix_det_ne_zero (a b x : M.Carrier)
    (ha : x ∈ (extChartAt (ComplexModel n) a).source)
    (hb : x ∈ (extChartAt (ComplexModel n) b).source) :
    (determinantTransitionMatrix a b x).det ≠ 0 := by
  rw [determinantTransitionMatrix_eq_basisMatrix a b x ha hb]
  exact ((determinantFrameBasis b x hb).isUnit_det
    (determinantFrameBasis a x ha)).ne_zero

theorem chartTopForm_other_frame (a b x : M.Carrier)
    (ha : x ∈ (extChartAt (ComplexModel n) a).source)
    (hb : x ∈ (extChartAt (ComplexModel n) b).source) :
    chartTopForm b x hb (determinantFrameBasis a x ha) =
      (determinantTransitionMatrix a b x).det := by
  change (determinantFrameBasis b x hb).det (determinantFrameBasis a x ha) = _
  rw [Module.Basis.det_apply, determinantTransitionMatrix_eq_basisMatrix a b x ha hb]

theorem chartTopForm_change (a b x : M.Carrier)
    (ha : x ∈ (extChartAt (ComplexModel n) a).source)
    (hb : x ∈ (extChartAt (ComplexModel n) b).source) :
    chartTopForm b x hb = (determinantTransitionMatrix a b x).det • chartTopForm a x ha := by
  simpa only [chartTopForm_other_frame a b x ha hb] using
    canonical_eq_smul_chartTopForm a x ha (chartTopForm b x hb)

theorem antiCanonicalScalar_change (a b x : M.Carrier)
    (ha : x ∈ (extChartAt (ComplexModel n) a).source)
    (hb : x ∈ (extChartAt (ComplexModel n) b).source) (ℓ : AntiCanonicalFiber M x) :
    ℓ (chartTopForm b x hb) =
      (determinantTransitionMatrix a b x).det * ℓ (chartTopForm a x ha) := by
  rw [chartTopForm_change a b x ha hb, map_smul, smul_eq_mul]

theorem tangentAntiCanonicalCoordinate_change (a b x : M.Carrier)
    (ha : x ∈ (extChartAt (ComplexModel n) a).source)
    (hb : x ∈ (extChartAt (ComplexModel n) b).source)
    (u : TangentAntiCanonicalFiber M x) :
    tangentAntiCanonicalCoordinateLinearEquiv b x hb u =
      (determinantTransitionMatrix a b x).det •
        determinantTransition a b x (tangentAntiCanonicalCoordinateLinearEquiv a x ha u) := by
  induction u using TensorProduct.inductionOn with
  | tmul v ℓ =>
    simp only [tangentAntiCanonicalCoordinateLinearEquiv_tmul,
      antiCanonicalScalar_change a b x ha hb, map_smul, determinantTransition_apply,
      chartVec_tangentCoords a x ha, mul_smul]
  | add u v hu hv => simp only [map_add, smul_add, hu, hv]

end Yau.NodeProofs.P03Aux
