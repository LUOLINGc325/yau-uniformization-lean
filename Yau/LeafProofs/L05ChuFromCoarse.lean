import Yau.LeafProofs.L05ChuSharpUpgrade
import Yau.LeafProofs.L05PerturbationStatement
import Yau.LeafProofs.L05Assembly

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

variable (hCoarse : VariableConcaveCoarseSchauderGap)

include hCoarse

set_option maxHeartbeats 1800000 in
theorem chuTransformedHessian_of_coarse : ChuTransformedHessian := by
  intro n hn alpha beta ell L K fB uB ha ha1 hb hb1 hell hL hK hfB huB omega hm
  obtain ⟨eta,M,he,hEta,hM,hProvider⟩ := hCoarse n hn alpha beta (chuCoarseLower ell K)
    (chuCoarseUpper n ell L K) (chuCoarseBudget n L K fB uB) fB uB
    ha ha1 hb hb1 (chuCoarseLower_pos hell hK) (chuCoarseLower_le_upper n ell L K)
    (chuCoarseBudget_pos n (hell.le.trans hL) hK.le hfB huB).le hfB huB
  have he1 : eta < 1 := hEta.trans ((min_le_left alpha beta).trans_lt ha1)
  obtain ⟨C,hC,hSharp⟩ := chu_sharp_upgrade_of_coarse n hn ell L K alpha beta eta (min alpha beta) fB M
    hell hL hK hM.le he he1 hb (lt_min ha hb) ((min_le_left _ _).trans_lt ha1)
    (min_le_left _ _) (min_le_right _ _) hfB omega hm
  refine ⟨C,hC,?_⟩
  intro E U F S T f u hEc hEv hne hF hT hS hDF hf hu hub hRange hPDE
  have hData := chu_global_reduction_data hEc hEv hne hell.le hL hK.le hb hfB huB hF hT hS hu hub
    (fun p hp => by simpa only [Real.norm_eq_abs] using hf.2.1 p hp) hRange hPDE
  have hCrude := hProvider (chuGlobalOperator E F S T ell L) f u hData.1 hData.2.1 hData.2.2.1
    hData.2.2.2.1 hData.2.2.2.2.1 hf hu hub hData.2.2.2.2.2
  exact hSharp E U F T S f u hEc hEv hne hF hT hS hDF hf hu hCrude hRange hPDE

theorem leaf_L05_of_coarse : LeafObligations.L05 :=
  leaf_of_chu (chuTransformedHessian_of_coarse hCoarse)

end Yau.LeafProofs.L05Aux
