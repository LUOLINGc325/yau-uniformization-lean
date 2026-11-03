import Yau.LeafProofs.L14

/-! The actual original smooth Kähler metric has symmetric holomorphic
first jets. Reuse the proved native barred identity and conjugation. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothMetric_hMat_wirt_symm (g : SmoothMetric M) (a : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget a) (i j k : Fin n) :
    wirt (fun y => hMat g.form a y k j) z (stdVec i) =
      wirt (fun y => hMat g.form a y k i) z (stdVec j) := by
  have he := congrArg star (L14Aux.kahler_hMat_wirtBar_symm g a z hz i j k)
  have hc (p q : Fin n) : (fun y => hMat g.form a y q p) =
      (fun y => star (hMat g.form a y p q)) := by
    funext y
    exact (L12Aux.hMat_isHermitian g.form a y).apply q p |>.symm
  rw [hc j k, hc i k, L14Aux.wirt_star, L14Aux.wirt_star]
  exact he

end Yau.NodeProofs.F01Aux
