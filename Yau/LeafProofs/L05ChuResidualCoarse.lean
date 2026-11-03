import Yau.LeafProofs.L05ChuRestriction

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem chuFrozenLinear_bound {n : ℕ} {E U : Set (Sym n)}
    {F : Sym n → Point n → ℝ} {T : Sym n → Point n → Sym n} {ell L K beta : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K)
    (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta)
    {A0 : Sym n} (hA0 : A0 ∈ E) {p0 : Point n} (hp0 : p0 ∈ backward 1) (V : Sym n) :
    |chuFrozenLinear hT F A0 p0 hp0 V| ≤
      (bellmanMatrixConstant n L*chuTransformNormConstant n K)*‖V‖ := by
  have hn := chuTransform_norm_le hK hT hp0 V
  have hd := chuDerivative_bound hell hF hA0 hp0 (T V p0)
  have hc := mul_le_mul_of_nonneg_left hn (bellmanMatrixConstant_nonneg n (hell.trans hL))
  rw [chuFrozenLinear_apply]
  change |fderiv ℝ (fun N => F N p0) A0 (T V p0)| ≤ bellmanMatrixConstant n L*‖T V p0‖ at hd
  exact hd.trans (hc.trans_eq (by ring))

def chuFrozenResidualBudget (n : ℕ) (L K M : ℝ) : ℝ :=
  M+(bellmanMatrixConstant n L*chuTransformNormConstant n K)*chuHessianTransportConstant n*M

set_option maxHeartbeats 1600000 in
theorem chuFrozenResidual_holderBound {n : ℕ} {E U : Set (Sym n)}
    {F : Sym n → Point n → ℝ} {T : Sym n → Point n → Sym n}
    {ell L K beta eta r M : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K)
    (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta)
    {A0 : Sym n} (hA0 : A0 ∈ E) {p0 : Point n} (hp0 : p0 ∈ backward 1)
    {u : Point n → ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (hu : SchauderBound eta (backward r) u M) :
    HolderBound eta (backward r) (chuFrozenResidual hT F A0 p0 hp0 u) (chuFrozenResidualBudget n L K M) := by
  have hC : 0 ≤ bellmanMatrixConstant n L*chuTransformNormConstant n K :=
    mul_nonneg (bellmanMatrixConstant_nonneg n (hell.trans hL)) (chuTransformNormConstant_nonneg n hK)
  have hDim := (chuHessianTransportConstant_pos n).le
  have hM := hu.2.1
  have hH := hessian_holderBound_of_spatialDD hu.2.2.2.1
  have hTime : HolderBound eta (backward r) (timeD (backward 1) u) M := by
    refine ⟨hu.2.2.2.2.1,?_,?_⟩
    · intro p hp
      rw [← chu_timeD_backward_restrict hr hr1 u hp]
      exact hu.2.2.2.2.2.1 p hp
    · intro p hp q hq
      rw [← chu_timeD_backward_restrict hr hr1 u hp,← chu_timeD_backward_restrict hr hr1 u hq]
      exact hu.2.2.2.2.2.2 p hp q hq
  refine ⟨by unfold chuFrozenResidualBudget; positivity,?_,?_⟩
  · intro p hp
    have hl := chuFrozenLinear_bound hell hL hK hF hT hA0 hp0 (hessian u p)
    have hs := mul_le_mul_of_nonneg_left (hH.2.1 p hp) hC
    have ht := hTime.2.1 p hp
    have hh : ‖chuFrozenResidual hT F A0 p0 hp0 u p‖ ≤
        ‖timeD (backward 1) u p‖+|chuFrozenLinear hT F A0 p0 hp0 (hessian u p)| :=
      norm_sub_le _ _
    unfold chuFrozenResidualBudget
    nlinarith only [hh,hl,hs,ht]
  · intro p hp q hq
    let l := chuFrozenLinear hT F A0 p0 hp0
    have he : chuFrozenResidual hT F A0 p0 hp0 u p-chuFrozenResidual hT F A0 p0 hp0 u q=
        (timeD (backward 1) u p-timeD (backward 1) u q)-l (hessian u p-hessian u q) := by
      have hl := l.map_sub (hessian u p) (hessian u q)
      dsimp only [chuFrozenResidual]
      linarith only [hl]
    rw [he]
    have hn := norm_sub_le (timeD (backward 1) u p-timeD (backward 1) u q) (l (hessian u p-hessian u q))
    have hl := chuFrozenLinear_bound hell hL hK hF hT hA0 hp0 (hessian u p-hessian u q)
    have hs := mul_le_mul_of_nonneg_left (hH.2.2 p hp q hq) hC
    have ht := hTime.2.2 p hp q hq
    rw [Real.norm_eq_abs (l _)] at hn
    unfold chuFrozenResidualBudget
    nlinarith only [hn,hl,hs,ht]

end Yau.LeafProofs.L05Aux
