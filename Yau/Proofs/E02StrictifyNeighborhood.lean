import Yau.Proofs.E02BaseTimePacking

open Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau

/-- One finite C² neighborhood of the original test is all that the
strictified comparison needs, including away from its center. -/
theorem baseTimeStrictify_contDiffOn_two {n : ℕ}
    (f : ComplexVector n × ℝ → ℝ) (a : ComplexVector n × ℝ)
    (V : Set (ComplexVector n × ℝ)) (hf : ContDiffOn ℝ 2 f V) :
    ContDiffOn ℝ 2 (baseTimeStrictify f a) V := by
  let e := baseTimeRealCoordinates n
  have hSq : ContDiff ℝ ∞ (fun p : ComplexVector n × ℝ => ‖e p-e a‖^2) :=
    (e.contDiff.sub contDiff_const).norm_sq ℝ
  have hFourth : ContDiff ℝ 2 (fun p : ComplexVector n × ℝ => ‖e p-e a‖^4) := by
    simpa only [←pow_mul] using (hSq.pow 2).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hEq : baseTimeStrictify f a = (fun p => f p-‖e p-e a‖^4) := by
    funext p
    simp only [baseTimeStrictify,strictifyTest,ContinuousLinearEquiv.symm_apply_apply,e]
  rw [hEq]
  exact hf.sub hFourth.contDiffOn

end Yau.NodeProofs.E02Aux
