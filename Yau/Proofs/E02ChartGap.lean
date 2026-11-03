import Yau.Proofs.E02Optimizer
import Yau.LeafProofs.L18

open Matrix
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The actual fixed-chart cotangent metric, with the original transpose. -/
def chartCometric {n : ℕ} (X : KahlerManifold n) (h : Flow X) (x : Pt X)
    (z : ComplexVector n) (t : ℝ) : Herm n := ((hMat (h t) x z)⁻¹)ᵀ

theorem chartCometric_posDef {n : ℕ} (X : KahlerManifold n) (h : Flow X) (x : Pt X)
    (z : ComplexVector n) (t : ℝ) (hz : z ∈ chartTarget x) :
    (chartCometric X h x z t).PosDef :=
  (Yau.LeafProofs.L18Aux.hMat_posDef (h t) x z hz).inv.transpose

theorem volumeGap_exp_eq_metric_det_mul {n : ℕ} (X : KahlerManifold n) (h : Flow X)
    (T : ℝ) (x : Pt X) (z : ComplexVector n) (t : ℝ) (B : Herm n)
    (hz : z ∈ chartTarget x) (hB : FeasibleEllipsoid X h T x z t B)
    (hMax : ∀ D, FeasibleEllipsoid X h T x z t D → D.det.re ≤ B.det.re) :
    Real.exp (-volumeGap X h T x z t) = (hMat (h t) x z).det.re*B.det.re := by
  have hH := Yau.LeafProofs.L18Aux.hMat_posDef (h t) x z hz
  have hHr : 0 < (hMat (h t) x z).det.re := (RCLike.pos_iff.mp hH.det_pos).1
  have hBr : 0 < B.det.re := (RCLike.pos_iff.mp hB.1.det_pos).1
  have hLog : -volumeGap X h T x z t =
      Real.log (hMat (h t) x z).det.re+Real.log B.det.re := by
    rw [volumeGap_eq_of_max X h T x z t B hB hMax]
    unfold logDet
    ring
  rw [hLog,Real.exp_add,Real.exp_log hHr,Real.exp_log hBr]

/-- This is the exact determinant ratio multiplying the original heat
operator; neither the chart nor its maximizing matrix is changed. -/
theorem volumeGap_exp_eq_cometric_ratio {n : ℕ} (X : KahlerManifold n) (h : Flow X)
    (T : ℝ) (x : Pt X) (z : ComplexVector n) (t : ℝ) (B : Herm n)
    (hz : z ∈ chartTarget x) (hB : FeasibleEllipsoid X h T x z t B)
    (hMax : ∀ D, FeasibleEllipsoid X h T x z t D → D.det.re ≤ B.det.re) :
    Real.exp (-volumeGap X h T x z t) = B.det.re/(chartCometric X h x z t).det.re := by
  have hH := Yau.LeafProofs.L18Aux.hMat_posDef (h t) x z hz
  have hHi : (hMat (h t) x z).det.im = 0 := (RCLike.pos_iff.mp hH.det_pos).2
  have hbPos := chartCometric_posDef X h x z t hz
  have hb : 0 < (chartCometric X h x z t).det.re := (RCLike.pos_iff.mp hbPos.det_pos).1
  have hInv : (chartCometric X h x z t).det.re*(hMat (h t) x z).det.re = 1 := by
    have hh := congrArg Complex.re
      (Matrix.det_nonsing_inv_mul_det (A := hMat (h t) x z) (hH.isUnit.map Matrix.detMonoidHom))
    simpa only [chartCometric,Matrix.det_transpose,Complex.mul_re,hHi,mul_zero,sub_zero,Complex.one_re] using hh
  rw [volumeGap_exp_eq_metric_det_mul X h T x z t B hz hB hMax]
  apply (eq_div_iff hb.ne').mpr
  calc
    _ = B.det.re*((chartCometric X h x z t).det.re*(hMat (h t) x z).det.re) := by ring
    _ = B.det.re := by rw [hInv,mul_one]

end Yau.NodeProofs.E02Aux
