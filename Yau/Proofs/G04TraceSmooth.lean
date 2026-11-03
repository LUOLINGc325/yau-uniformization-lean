import Yau.Proofs.G04FormInnerMatrix
import Yau.Proofs.G04KahlerForm

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ} {M : ComplexManifold n}

theorem formInner_smooth (h : HermitianField M) (hs : MetricSmooth h)
    (A B : RealForm M k) (hA : SmoothRealForm A) (hB : SmoothRealForm B) :
    SmoothFn (formInner h A B) := by
  intro x
  apply (contDiffOn_const.mul (L03.tensorCoefficientPairing_contDiffOn
    (fun z => (realMetricFn h x z)⁻¹) (formComponents A x) (formComponents B x)
    (chartTarget x) (L23Aux.realMetricFn_inverse_contDiffOn h hs x) (hA x) (hB x))).congr
  intro z hz
  exact L03.formInner_chartInv_eq_tensorPairing h A B x hz

theorem formTrace_eq_inner_omega (h : HermitianField M) (A : RealForm M 2)
    (hA : RealOneOne A) (x : M.Carrier) :
    formTrace h A x = formInner h A (omegaForm h) x := by
  rw [formInner_oneOne h A (omegaForm h) hA (omegaForm_oneOne h) x,
    formHermitianMatrix_of_representsIota (gMat h) (omegaForm h) (omegaForm_represents h)]
  unfold formTrace traceWith
  have hunit : IsUnit (gMat h x).det :=
    (L12Aux.hMat_posDef h x (chartPt x x) (mem_extChartAt_target x)).isUnit.map Matrix.detMonoidHom
  rw [Matrix.mul_assoc ((gMat h x)⁻¹ * formHermitianMatrix A x),
    Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]

theorem trace_smooth (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A) :
    SmoothFn (formTrace h A) := by
  have he : formTrace h A = formInner h A (omegaForm h) :=
    funext (formTrace_eq_inner_omega h A h11)
  rw [he]
  exact formInner_smooth h hs A (omegaForm h) hA (omegaForm_smooth h hs)

end Yau.NodeProofs.G04Aux
