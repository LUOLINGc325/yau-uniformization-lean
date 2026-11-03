import Yau.Proofs.V04WallErrorPhysicalTime
import Yau.Proofs.V04WallErrorRelativeTrace
import Yau.Proofs.F02Elementary

/-! The trace bound uses the determinant ratio of the actual localized
flow, hence exactly the original `rho` appearing in the base wall error. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem initialMetric_traceWith_le_exp_rho
    {d : VariationData X q} (hd : VariationSetup d) (x : Pt X) {t : ℝ} (ht : 0 ≤ t) :
    traceWith (gMat (d.h t) x) (gMat X.metric.form x) ≤ n * Real.exp (d.rho x t) := by
  have hl : LocalizedFlow X d.o d.h d.U d.P d.rho := hd.2.2.1.1
  rcases hl with ⟨hkrf, hU, hP, hrho, hle, hpot, hzero, hUP, hdet, hrhoeq, hrest⟩
  have hH := gMat_posDef (d.h t) x
  have hG := gMat_posDef X.metric.form x
  have hp := relative_inverse_trace_le_det_ratio hH hG (hle t ht x)
  have hHdet : 0 < (gMat (d.h t) x).det.re := (Complex.pos_iff.mp hH.det_pos).1
  have hGdet : 0 < (gMat X.metric.form x).det.re := (Complex.pos_iff.mp hG.det_pos).1
  have hexp : Real.exp (d.rho x t) =
      (gMat X.metric.form x).det.re / (gMat (d.h t) x).det.re := by
    rw [(hrhoeq x t ht).1, hdet x t ht, Real.exp_neg,
      Real.exp_log (div_pos hHdet hGdet), inv_div]
  simpa only [traceWith, Fintype.card_fin, hexp] using hp

end Yau.Blueprint.V04Proof.WallErrorAux
