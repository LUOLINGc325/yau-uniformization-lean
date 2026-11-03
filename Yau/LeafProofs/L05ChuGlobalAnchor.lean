import Yau.LeafProofs.L05ChuOriginAnchor

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem chuGlobalOperator_origin_bound {n : ℕ} {E U : Set (Sym n)}
    (hEc : IsCompact E) (hEv : Convex ℝ E) (hne : E.Nonempty)
    {F : Sym n → Point n → ℝ} {S : Point n → Sym n} {T : Sym n → Point n → Sym n}
    {ell L K beta fB uB : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K)
    (hb : 0 ≤ beta) (huB : 0 ≤ uB) (hF : ChuH1 E U F ell L K beta)
    (hT : ChuH2 T K beta) (hS : ChuH3 S K beta)
    {u f : Point n → ℝ} (hu : C2 (backward 1) u)
    (hub : ∀ p ∈ backward 1, |u p| ≤ uB) (hfb : ∀ p ∈ backward 1, |f p| ≤ fB)
    (hRange : ∀ p ∈ backward 1, S p+T (hessian u p) p ∈ E)
    (hPDE : ∀ p ∈ backward 1,
      timeD (backward 1) u p-F (S p+T (hessian u p) p) p=f p) :
    |chuGlobalOperator E F S T ell L 0 (0,0)| ≤
      chuOriginAnchorBound n (Real.sqrt (Fintype.card (RIdx n))*K*L)
        (chuGlobalTimeConstant n L K) fB uB := by
  have hM : 0 ≤ chuGlobalTimeConstant n L K := by
    unfold chuGlobalTimeConstant
    exact mul_nonneg hK (add_nonneg (mul_nonneg (by norm_num) (bellmanMatrixConstant_nonneg n (hell.trans hL))) zero_le_one)
  have hVarPhi : ∀ p ∈ backward 1,
      |chuGlobalOperator E F S T ell L 0 p-chuGlobalOperator E F S T ell L 0 (0,0)| ≤
        chuGlobalTimeConstant n L K*holderWeight beta p (0,0) := by
    intro p hp
    have hh := chuGlobalOperator_time_holder hEc hne hell hL hK hF hT hS (0 : Sym n) hp (backward_one_origin_mem n)
    simpa only [norm_zero,add_zero,mul_one] using hh
  have hPDEPhi : ∀ p ∈ backward 1,
      timeD (backward 1) u p-chuGlobalOperator E F S T ell L (hessian u p) p=f p := by
    intro p hp
    rw [chuGlobalOperator_eq_on hEc hEv hne hell hL hF hp (hRange p hp)]
    exact hPDE p hp
  exact chu_operator_origin_bound (ell := ell*K⁻¹) (mul_nonneg hell (inv_nonneg.mpr hK)) hM hb huB
    (fun p hp => chuGlobalOperator_globalElliptic hEc hne hell hL hF hT hp) hVarPhi hu hub hfb hPDEPhi

end Yau.LeafProofs.L05Aux
