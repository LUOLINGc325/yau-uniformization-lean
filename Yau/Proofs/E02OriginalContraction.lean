import Yau.Proofs.E02FeasibleCometric
import Yau.Proofs.E02RelativeTrace

open Matrix Set
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The PSD majorant contracts to the EXACT original coefficient and
trace operator. The relative order is never applied to indefinite L. -/
theorem optimizer_majorant_original_contraction {n : ℕ}
    (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (z : ComplexVector n) (t : ℝ) (hz : z ∈ chartTarget x) (ht : t ∈ Ioo 0 T)
    (B : Herm n) (hB : FeasibleEllipsoid X h T x z t B)
    (hMax : ∀ D, FeasibleEllipsoid X h T x z t D → D.det.re ≤ B.det.re)
    (K L : Herm n) (a : ℝ) (hK : K.PosSemidef) (hDom : (K-L).PosSemidef)
    (hTrace : tracePair B K ≤ a) :
    Real.exp (-volumeGap X h T x z t)*traceWith (hMat (h t) x z) L ≤ a := by
  have hb := chartCometric_posDef X h x z t hz
  have hOrder := feasibleEllipsoid_le_chartCometric X h T x z t hz ht B hB
  have hRelative := relative_det_trace_majorant B (chartCometric X h x z t)
    K L hB.1 hb hOrder hK hDom
  have hPair : tracePair (chartCometric X h x z t) L = traceWith (hMat (h t) x z) L := by
    simp only [tracePair,chartCometric,Matrix.transpose_transpose,traceWith]
  rw [hPair] at hRelative
  rw [volumeGap_exp_eq_cometric_ratio X h T x z t B hz hB hMax]
  exact hRelative.trans hTrace

end Yau.NodeProofs.E02Aux
