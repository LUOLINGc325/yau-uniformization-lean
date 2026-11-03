import Yau.LeafProofs.L05ChuSharpHessian
import Yau.LeafProofs.L05ChuTimeRegularity

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

local instance l05ChuSharpUpgradeDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuSharpUpgradeDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuSharpUpgradeHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05ChuSharpUpgradeHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

set_option maxHeartbeats 2500000 in
theorem chu_sharp_upgrade_of_coarse (n : ℕ) (hn : 0 < n) (ell L K alpha beta eta gamma fB M : ℝ)
    (hell : 0 < ell) (hL : ell ≤ L) (hK : 0 < K) (hM : 0 ≤ M)
    (he : 0 < eta) (he1 : eta < 1) (hb : 0 < beta) (hg : 0 < gamma) (hg1 : gamma < 1)
    (hga : gamma ≤ alpha) (hgb : gamma ≤ beta) (hfB : 0 ≤ fB) (omega : ℝ → ℝ) (hm : Modulus omega) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E U : Set (Sym n)) (F : Sym n → Point n → ℝ) (T : Sym n → Point n → Sym n)
        (S : Point n → Sym n) (f u : Point n → ℝ),
      IsCompact E → Convex ℝ E → E.Nonempty →
      ChuH1 E U F ell L K beta → ChuH2 T K beta → ChuH3 S K beta →
      ChuDerivativeModulus E F omega → HolderBound alpha (backward 1) f fB → C2 (backward 1) u →
      SchauderBound eta (backward (3/4)) u M →
      (∀ p ∈ backward 1, S p+T (hessian u p) p ∈ E) →
      (∀ p ∈ backward 1, timeD (backward 1) u p-F (S p+T (hessian u p) p) p=f p) →
      SchauderBound gamma (backward (1/2)) u C := by
  obtain ⟨CH,hCH,hHessian⟩ := chu_sharp_hessian_of_coarse n hn ell L K alpha beta eta gamma fB M
    hell hL hK hM he he1 hb hg hg1 hga hgb hfB omega hm
  let CT : ℝ := 3*M+2*chuTimeSharpBudget n L K fB CH
  have hCL := bellmanMatrixConstant_nonneg n (hell.le.trans hL)
  have hTNorm := chuTransformNormConstant_nonneg n hK.le
  have hDim := (chuHessianTransportConstant_pos n).le
  have hTimeCoef : 0 ≤ chuGlobalTimeConstant n L K := by unfold chuGlobalTimeConstant; positivity
  have hCT : 0 ≤ CT := by dsimp only [CT,chuTimeSharpBudget]; positivity
  let C : ℝ := 1+M+CH+CT
  have hC : 0 < C := by dsimp only [C]; positivity
  have hMC : M ≤ C := by dsimp only [C]; linarith only [hCH,hCT]
  have hHC : CH ≤ C := by dsimp only [C]; linarith only [hM,hCT]
  have hTC : CT ≤ C := by dsimp only [C]; linarith only [hM,hCH]
  refine ⟨C,hC,?_⟩
  intro E U F T S f u hEc hEv hne hF hT hS hDF hf hu hCoarse hRange hPDE
  have hHalf : backward (n := n) (1/2) ⊆ backward (3/4) := chu_backward_subset (by norm_num) (by norm_num)
  have hHs := hHessian E U F T S f u hEv hF hT hS hDF hf hu hCoarse hRange hPDE
  have hTimeBound (p : Point n) (hp : p ∈ backward (1/2)) : |timeD (backward 1) u p| ≤ M := by
    rw [← chu_timeD_backward_restrict (r := (3/4:ℝ)) (by norm_num) (by norm_num) u (hHalf hp)]
    simpa only [Real.norm_eq_abs] using hCoarse.2.2.2.2.2.1 p (hHalf hp)
  have hTs := chu_timeD_holder_of_spatial_hessian hEc hEv hne hell.le hL hK.le hg hg1 hga hgb
    hF hT hS hu hf hRange hPDE hHs hM hTimeBound
  refine ⟨chu_c2_backward_restrict (by norm_num) (by norm_num) hu,hC.le,?_,
    L16Aux.holderBound_mono_const hHs hHC,L16Aux.holderBound_mono_const hTs hTC⟩
  intro p hp
  exact ⟨(hCoarse.2.2.1 p (hHalf hp)).1.trans hMC,(hCoarse.2.2.1 p (hHalf hp)).2.trans hMC⟩

end Yau.LeafProofs.L05Aux
