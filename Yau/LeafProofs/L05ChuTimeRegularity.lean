import Yau.LeafProofs.L05ChuParabolicGeometry
import Yau.LeafProofs.L05ChuRestriction

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

local instance l05ChuTimeRegularityDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuTimeRegularityDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuTimeRegularityHessianGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuTimeRegularityHessianSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

def chuTimeSharpBudget (n : ℕ) (L K fB MH : ℝ) : ℝ :=
  (bellmanMatrixConstant n L*chuTransformNormConstant n K)*(chuHessianTransportConstant n*MH)+
    chuGlobalTimeConstant n L K*(1+chuHessianTransportConstant n*MH)+fB

set_option maxHeartbeats 1600000 in
theorem chu_timeD_holder_of_spatial_hessian {n : ℕ} {E U : Set (Sym n)}
    (hEc : IsCompact E) (hEv : Convex ℝ E) (hne : E.Nonempty)
    {F : Sym n → Point n → ℝ} {T : Sym n → Point n → Sym n} {S : Point n → Sym n}
    {ell L K alpha beta gamma fB MH Mtime : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K)
    (hg : 0 < gamma) (hg1 : gamma < 1) (hga : gamma ≤ alpha) (hgb : gamma ≤ beta)
    (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta) (hS : ChuH3 S K beta)
    {u f : Point n → ℝ} (_hu : C2 (backward 1) u) (hf : HolderBound alpha (backward 1) f fB)
    (hRange : ∀ p ∈ backward 1, S p+T (hessian u p) p ∈ E)
    (hPDE : ∀ p ∈ backward 1, timeD (backward 1) u p-F (S p+T (hessian u p) p) p=f p)
    (hH : HolderBound gamma (backward (1/2)) (spatialDD u) MH) (hM : 0 ≤ Mtime)
    (hTime : ∀ p ∈ backward (1/2), |timeD (backward 1) u p| ≤ Mtime) :
    HolderBound gamma (backward (1/2)) (timeD (backward (1/2)) u)
      (3*Mtime+2*chuTimeSharpBudget n L K fB MH) := by
  have hCL := bellmanMatrixConstant_nonneg n (hell.trans hL)
  have hCT := chuTransformNormConstant_nonneg n hK
  have hCLT : 0 ≤ chuGlobalTimeConstant n L K := by
    unfold chuGlobalTimeConstant
    positivity
  have hCH := (chuHessianTransportConstant_pos n).le
  have hHs := hessian_holderBound_of_spatialDD hH
  have hCoeff : 0 ≤ chuTimeSharpBudget n L K fB MH := by
    unfold chuTimeSharpBudget
    exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hCL hCT) hHs.1)
      (mul_nonneg hCLT (by linarith only [hHs.1]))) hf.1
  have hSub : backward (n := n) (1/2) ⊆ backward 1 := chu_backward_subset (by norm_num) (by norm_num)
  have hTimeEq (p : Point n) (hp : p ∈ backward (1/2)) :
      timeD (backward (1/2)) u p=timeD (backward 1) u p :=
    chu_timeD_backward_restrict (by norm_num) (by norm_num) u hp
  have hEq (p : Point n) (hp : p ∈ backward (1/2)) :
      timeD (backward (1/2)) u p=chuGlobalOperator E F S T ell L (hessian u p) p+f p := by
    rw [hTimeEq p hp,chuGlobalOperator_eq_on hEc hEv hne hell hL hF (hSub hp) (hRange p (hSub hp))]
    linarith only [hPDE p (hSub hp)]
  have hNear (p : Point n) (hp : p ∈ backward (1/2)) (q : Point n) (hq : q ∈ backward (1/2))
      (hpq : parabolicDistance p q ≤ 1) :
      ‖timeD (backward (1/2)) u p-timeD (backward (1/2)) u q‖ ≤
        (2*chuTimeSharpBudget n L K fB MH)*(parabolicDistance p q)^gamma := by
    have hLip := chuGlobalOperator_matrix_sub_le (S := S) hEc hne hell hL hK hF hT (hSub hp) (hessian u p) (hessian u q)
    have hVar := chuGlobalOperator_time_holder hEc hne hell hL hK hF hT hS (hessian u q) (hSub hp) (hSub hq)
    have hHpair := mul_le_mul_of_nonneg_left (hHs.2.2 p hp q hq) (mul_nonneg hCL hCT)
    have hGrowth := mul_le_mul_of_nonneg_left (show 1+‖hessian u q‖ ≤ 1+chuHessianTransportConstant n*MH by linarith only [hHs.2.1 q hq]) hCLT
    have hVarGamma := mul_le_mul hGrowth (holderWeight_lower_exponent_near hg.le hgb hpq)
      (show 0 ≤ holderWeight beta p q from by unfold holderWeight; positivity)
      (mul_nonneg hCLT (by linarith only [hHs.1]))
    have hfGamma := mul_le_mul_of_nonneg_left (holderWeight_lower_exponent_near hg.le hga hpq) hf.1
    have hfpair := hf.2.2 p (hSub hp) q (hSub hq)
    have hTriangle := abs_sub_le
      (chuGlobalOperator E F S T ell L (hessian u p) p)
      (chuGlobalOperator E F S T ell L (hessian u q) p)
      (chuGlobalOperator E F S T ell L (hessian u q) q)
    have hSum := abs_add_le
      (chuGlobalOperator E F S T ell L (hessian u p) p-chuGlobalOperator E F S T ell L (hessian u q) q)
      (f p-f q)
    have hPair : ‖timeD (backward (1/2)) u p-timeD (backward (1/2)) u q‖ ≤
        chuTimeSharpBudget n L K fB MH*holderWeight gamma p q := by
      rw [hEq p hp,hEq q hq,Real.norm_eq_abs]
      have harg : (chuGlobalOperator E F S T ell L (hessian u p) p+f p)-
          (chuGlobalOperator E F S T ell L (hessian u q) q+f q)=
          (chuGlobalOperator E F S T ell L (hessian u p) p-chuGlobalOperator E F S T ell L (hessian u q) q)+(f p-f q) := by ring
      rw [harg]
      rw [Real.norm_eq_abs] at hfpair
      unfold chuTimeSharpBudget
      nlinarith only [hLip,hVar,hHpair,hVarGamma,hfGamma,hfpair,hTriangle,hSum]
    have hw := mul_le_mul_of_nonneg_left
      (holderWeight_le_twice_radius_power hg.le (le_refl (parabolicDistance p q))) hCoeff
    exact hPair.trans (hw.trans_eq (by ring))
  have hh := chu_holderBound_of_near_power hg.le hg1.le zero_lt_one hM (by positivity : 0 ≤ 2*chuTimeSharpBudget n L K fB MH)
    (fun p hp => by rw [hTimeEq p hp,Real.norm_eq_abs]; exact hTime p hp) hNear
  convert! hh using 1 <;> simp only [Real.one_rpow] <;> ring

end Yau.LeafProofs.L05Aux
