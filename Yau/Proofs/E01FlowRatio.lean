import Yau.Proofs.V03DualTransport
import Yau.Proofs.V03DualNorm
import Yau.LeafProofs.L17ChartNaturality

/-! The original rho is the fixed-chart difference of the two actual metric log determinants. -/

noncomputable section
open scoped Manifold Topology Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint
open Yau.Blueprint.V03Proof

variable {n : ℕ} {X : KahlerManifold n}

theorem localized_rho_fixed_chart_ratio {o : Pt X} {h : Flow X} {U P ρ : STF X}
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (t : ℝ) (ht : 0 ≤ t) :
    ρ (chartInv x z) t = Real.log (hMat X.metric.form x z).det.re -
      Real.log (hMat (h t) x z).det.re := by
  let y : Pt X := chartInv x z
  have hy : y ∈ (extChartAt (ComplexModel n) x).source :=
    (extChartAt (ComplexModel n) x).map_target hz
  have hround : chartPt x y = z := (extChartAt (ComplexModel n) x).right_inv hz
  have hratio : (hMat (h t) x z).det.re / (hMat X.metric.form x z).det.re =
      (gMat (h t) y).det.re / (gMat X.metric.form y).det.re := by
    rw [← hround, hMat_eq_centered_congruence (h t) x y hy,
      hMat_eq_centered_congruence X.metric.form x y hy]
    exact Yau.LeafProofs.L17Aux.determinant_ratio_congruence _ _ _
      ((tangentFrameMatrix_isUnit x y hy).map Matrix.detMonoidHom).ne_zero
  rcases hloc with ⟨_, _, _, _, _, _, _, _, hP, hρ, _⟩
  rw [(hρ y t ht).1, hP y t ht, ← hratio]
  have hh : 0 < (hMat (h t) x z).det.re := (Complex.pos_iff.mp (hMat_posDef (h t) x z hz).det_pos).1
  have hg : 0 < (hMat X.metric.form x z).det.re := (Complex.pos_iff.mp (hMat_posDef X.metric.form x z hz).det_pos).1
  rw [Real.log_div hh.ne' hg.ne']
  ring

end Yau.NodeProofs.E01Aux
