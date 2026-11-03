import Yau.Proofs.E02RealTensorLevi

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau

theorem stdVec_combination {n : ℕ} (X : ComplexVector n) :
    complexDirectionCombination stdVec (WithLp.ofLp X) = X := by
  ext i
  simp [complexDirectionCombination,stdVec,Pi.single_apply,mul_ite]

/-- The physical time is fixed in the original Levi operator; its
quadratic form agrees with the two real base-time Hessian directions. -/
theorem baseTime_leviC_quadratic {n : ℕ} {f : ComplexVector n × ℝ → ℝ}
    {z : ComplexVector n} {t : ℝ} (hf : ContDiffAt ℝ 2 f (z,t)) (X : ComplexVector n) :
    (star (WithLp.ofLp X) ⬝ᵥ (leviC (fun w => f (w,t)) z*ᵥWithLp.ofLp X)).re =
      (fderiv ℝ (fderiv ℝ f) (z,t) (X,0) (X,0)+
        fderiv ℝ (fderiv ℝ f) (z,t) (Complex.I • X,0) (Complex.I • X,0))/4 := by
  let L : ComplexVector n →L[ℝ] (ComplexVector n × ℝ) :=
    (ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0
  have hArg (w : ComplexVector n) : (0,t)+L w = (w,t) := by simp [L]
  have hAt : ContDiffAt ℝ 2 f ((0,t)+L z) := by rw [hArg]; exact hf
  have hComp : ContDiffAt ℝ 2 (fun w => f ((0,t)+L w)) z :=
    hAt.comp z (contDiff_const.add L.contDiff).contDiffAt
  have hPull := affinePullback_second_fderiv (0,t) L hAt
  have hQuad := leviMatrix_quadratic_re hComp stdVec (WithLp.ofLp X)
  rw [stdVec_combination X,hPull] at hQuad
  have hFun : (fun w => f ((0,t)+L w)) = (fun w => f (w,t)) := by
    funext w
    rw [hArg]
  rw [hFun] at hQuad
  simpa [leviC,ContinuousLinearMap.bilinearComp_apply,L] using hQuad

end Yau.NodeProofs.E02Aux
