import Yau.Proofs.E02BaseTimePacking
import Yau.Proofs.E02RealTensorLevi

open scoped Topology ContDiff
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau

theorem baseTimeStrictify_fderiv {n : ℕ} {f : ComplexVector n × ℝ → ℝ}
    {a : ComplexVector n × ℝ} (hf : ContDiffAt ℝ ∞ f a) :
    fderiv ℝ (baseTimeStrictify f a) a = fderiv ℝ f a :=
  (realSecondJet_hasFDerivAt (baseTimeStrictify_realSecondJet (hf.of_le (by simp)))).fderiv

theorem baseTimeStrictify_second_fderiv {n : ℕ} {f : ComplexVector n × ℝ → ℝ}
    {a : ComplexVector n × ℝ} (hf : ContDiffAt ℝ ∞ f a) :
    fderiv ℝ (fderiv ℝ (baseTimeStrictify f a)) a = fderiv ℝ (fderiv ℝ f) a :=
  realSecondJet_second_fderiv_eq (baseTimeStrictify_realSecondJet (hf.of_le (by simp)))
    ((baseTimeStrictify_contDiffAt hf).of_le (by simp))

theorem baseTimeStrictify_time_deriv {n : ℕ} {f : ComplexVector n × ℝ → ℝ}
    {z : ComplexVector n} {t : ℝ} (hf : ContDiffAt ℝ ∞ f (z,t)) :
    deriv (fun s => baseTimeStrictify f (z,t) (z,s)) t = deriv (fun s => f (z,s)) t := by
  have hTime : HasDerivAt (fun s : ℝ => (z,s)) (0,1) t := by
    simpa using (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  have hSharp := (realSecondJet_hasFDerivAt
    (baseTimeStrictify_realSecondJet (hf.of_le (by simp)))).comp_hasDerivAt t hTime
  have hOrig := (hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hTime
  exact hSharp.deriv.trans hOrig.deriv.symm

/-- The actual spatial Levi at the original base-time is preserved;
the physical time is held fixed in the original computed operator. -/
theorem baseTimeStrictify_leviC {n : ℕ} {f : ComplexVector n × ℝ → ℝ}
    {z : ComplexVector n} {t : ℝ} (hf : ContDiffAt ℝ ∞ f (z,t)) :
    leviC (fun w => baseTimeStrictify f (z,t) (w,t)) z = leviC (fun w => f (w,t)) z := by
  let L : ComplexVector n →L[ℝ] (ComplexVector n × ℝ) :=
    (ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0
  let a : ComplexVector n × ℝ := (0,t)
  have hArg (w : ComplexVector n) : a+L w = (w,t) := by simp [a,L]
  have hSharp : ContDiffAt ℝ 2 (baseTimeStrictify f (z,t)) (a+L z) := by
    rw [hArg]
    exact (baseTimeStrictify_contDiffAt hf).of_le (by simp)
  have hOrig : ContDiffAt ℝ 2 f (a+L z) := by rw [hArg]; exact hf.of_le (by simp)
  have hSharpLevi := leviMatrix_real_affine a L hSharp (stdVec (n := n))
  have hOrigLevi := leviMatrix_real_affine a L hOrig (stdVec (n := n))
  have hSharpFun : (fun w => baseTimeStrictify f (z,t) (w,t)) =
      (fun w => baseTimeStrictify f (z,t) (a+L w)) := by funext w; rw [hArg]
  have hOrigFun : (fun w => f (w,t)) = (fun w => f (a+L w)) := by funext w; rw [hArg]
  unfold leviC
  rw [hSharpFun,hOrigFun,hSharpLevi,hOrigLevi,hArg,baseTimeStrictify_second_fderiv hf]

end Yau.NodeProofs.E02Aux
