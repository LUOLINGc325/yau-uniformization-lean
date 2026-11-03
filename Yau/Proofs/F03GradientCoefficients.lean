import Yau.Proofs.F03GradientAlgebra

/-! Actual real scalar coefficients in the physical gradient norm. -/
noncomputable section
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem sqrt_gradNormSq_const_mul (g : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (c : ℝ) (x : M.Carrier) :
    Real.sqrt (gradNormSq g (fun y => c*f y) x)=|c| * Real.sqrt (gradNormSq g f x) := by
  have hMul : SmoothFn (fun y => c*f y) := fun a => contDiffOn_const.mul (hf a)
  rw [sqrt_gradNormSq_eq_physicalCovector g hMul,sqrt_gradNormSq_eq_physicalCovector g hf]
  unfold physicalCovector
  change ‖dualNormFactor (gMat g x) (realWirtingerMap n
    (fderiv ℝ (fun z => c*inChart x f z) (chartPt x x)))‖=_
  rw [fderiv_const_mul (smoothFn_center_differentiableAt hf x) c,map_smul,map_smul,norm_smul,Real.norm_eq_abs]

theorem sqrt_gradNormSq_sub_le (g : HermitianField M)
    {f q : M.Carrier → ℝ} (hf : SmoothFn f) (hq : SmoothFn q) (x : M.Carrier) :
    Real.sqrt (gradNormSq g (fun y => f y-q y) x) ≤
      Real.sqrt (gradNormSq g f x)+Real.sqrt (gradNormSq g q x) := by
  have hNeg : SmoothFn (fun y => (-1:ℝ)*q y) := fun a => contDiffOn_const.mul (hq a)
  have hh := sqrt_gradNormSq_add_le g hf hNeg x
  rw [sqrt_gradNormSq_const_mul g hq (-1) x] at hh
  simpa only [neg_one_mul,abs_neg,abs_one,one_mul,sub_eq_add_neg] using hh

end Yau.Proofs.F03Aux
