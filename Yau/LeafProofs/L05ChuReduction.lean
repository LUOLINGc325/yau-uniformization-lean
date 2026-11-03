import Yau.LeafProofs.L05ChuGlobalAnchor

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

def chuCoarseLower (ell K : ℝ) : ℝ := ell*K⁻¹

def chuCoarseUpper (n : ℕ) (ell L K : ℝ) : ℝ :=
  max (chuCoarseLower ell K) (Real.sqrt (Fintype.card (RIdx n))*K*L)

def chuCoarseBudget (n : ℕ) (L K fB uB : ℝ) : ℝ :=
  1+chuGlobalTimeConstant n L K+
    chuOriginAnchorBound n (Real.sqrt (Fintype.card (RIdx n))*K*L) (chuGlobalTimeConstant n L K) fB uB

theorem chuCoarseLower_pos {ell K : ℝ} (hell : 0 < ell) (hK : 0 < K) :
    0 < chuCoarseLower ell K := mul_pos hell (inv_pos.mpr hK)

theorem chuCoarseLower_le_upper (n : ℕ) (ell L K : ℝ) :
    chuCoarseLower ell K ≤ chuCoarseUpper n ell L K := le_max_left _ _

theorem chuCoarseBudget_pos (n : ℕ) {L K fB uB : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hfB : 0 ≤ fB) (huB : 0 ≤ uB) :
    0 < chuCoarseBudget n L K fB uB := by
  have hM : 0 ≤ chuGlobalTimeConstant n L K := by
    unfold chuGlobalTimeConstant
    exact mul_nonneg hK (by linarith only [bellmanMatrixConstant_nonneg n hL])
  have hLp : 0 ≤ Real.sqrt (Fintype.card (RIdx n))*K*L :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK) hL
  have hh := chuOriginAnchorBound_pos n hLp hM hfB huB
  unfold chuCoarseBudget
  linarith only [hM,hh]

set_option maxHeartbeats 1400000 in
theorem chu_global_reduction_data {n : ℕ} {E U : Set (Sym n)}
    (hEc : IsCompact E) (hEv : Convex ℝ E) (hne : E.Nonempty)
    {F : Sym n → Point n → ℝ} {S : Point n → Sym n} {T : Sym n → Point n → Sym n}
    {ell L K beta fB uB : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K)
    (hb : 0 < beta) (hfB : 0 ≤ fB) (huB : 0 ≤ uB) (hF : ChuH1 E U F ell L K beta)
    (hT : ChuH2 T K beta) (hS : ChuH3 S K beta)
    {u f : Point n → ℝ} (hu : C2 (backward 1) u)
    (hub : ∀ p ∈ backward 1, |u p| ≤ uB) (hfb : ∀ p ∈ backward 1, |f p| ≤ fB)
    (hRange : ∀ p ∈ backward 1, S p+T (hessian u p) p ∈ E)
    (hPDE : ∀ p ∈ backward 1,
      timeD (backward 1) u p-F (S p+T (hessian u p) p) p=f p) :
    ContinuousOn (fun z : Sym n × Point n => chuGlobalOperator E F S T ell L z.1 z.2)
      (Set.univ ×ˢ backward 1) ∧
    (∀ p ∈ backward 1, globalElliptic (fun H => chuGlobalOperator E F S T ell L H p)
      (chuCoarseLower ell K) (chuCoarseUpper n ell L K)) ∧
    (∀ p ∈ backward 1, ConcaveOn ℝ Set.univ (fun H => chuGlobalOperator E F S T ell L H p)) ∧
    (∀ H : Sym n, ∀ p ∈ backward 1, ∀ q ∈ backward 1,
      |chuGlobalOperator E F S T ell L H p-chuGlobalOperator E F S T ell L H q| ≤
        chuCoarseBudget n L K fB uB*(1+‖H‖)*holderWeight beta p q) ∧
    |chuGlobalOperator E F S T ell L 0 (0,0)| ≤ chuCoarseBudget n L K fB uB ∧
    (∀ p ∈ backward 1,
      timeD (backward 1) u p-chuGlobalOperator E F S T ell L (hessian u p) p=f p) := by
  have hM : 0 ≤ chuGlobalTimeConstant n L K := by
    unfold chuGlobalTimeConstant
    exact mul_nonneg hK (by linarith only [bellmanMatrixConstant_nonneg n (hell.trans hL)])
  have hLp : 0 ≤ Real.sqrt (Fintype.card (RIdx n))*K*L :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK) (hell.trans hL)
  have hApos := chuOriginAnchorBound_pos n hLp hM hfB huB
  have hMbudget : chuGlobalTimeConstant n L K ≤ chuCoarseBudget n L K fB uB := by
    unfold chuCoarseBudget
    linarith only [hApos]
  have hAbudget : chuOriginAnchorBound n (Real.sqrt (Fintype.card (RIdx n))*K*L)
      (chuGlobalTimeConstant n L K) fB uB ≤ chuCoarseBudget n L K fB uB := by
    unfold chuCoarseBudget
    linarith only [hM]
  refine ⟨chuGlobalOperator_continuousOn hEc hne hell hL hK hb hF hT hS,?_,?_,?_,?_,?_⟩
  · intro p hp N P hP
    have hh := chuGlobalOperator_globalElliptic (S := S) hEc hne hell hL hF hT hp N P hP
    exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hP.trace_nonneg)⟩
  · exact fun p hp => chuGlobalOperator_concave hEc hne hell hL hF hT hp
  · intro H p hp q hq
    have hh := chuGlobalOperator_time_holder hEc hne hell hL hK hF hT hS H hp hq
    have hW : 0 ≤ holderWeight beta p q :=
      add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMbudget (by positivity)) hW)
  · exact (chuGlobalOperator_origin_bound hEc hEv hne hell hL hK hb.le huB hF hT hS hu hub hfb hRange hPDE).trans hAbudget
  · intro p hp
    rw [chuGlobalOperator_eq_on hEc hEv hne hell hL hF hp (hRange p hp)]
    exact hPDE p hp

end Yau.LeafProofs.L05Aux
