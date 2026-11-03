import Yau.Proofs.F01BoundaryRatio
import Yau.Proofs.F01ParametricSmooth

/-! The explicit boundary ratio is jointly smooth, including at zero scale,
from the actual smoothness of u on an ordinary coordinate buffer. -/
open Set
open scoped ContDiff Interval
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

abbrev BoundaryParameters (E : Type*) := E × ℝ × E

def segmentEvaluation (c : ℝ) (w : BoundaryParameters E × ℝ) : E :=
  w.1.1 + (w.2 * (c * w.1.2.1)) • w.1.2.2

theorem segmentEvaluation_contDiff (c : ℝ) : ContDiff ℝ ∞ (segmentEvaluation (E := E) c) := by
  unfold segmentEvaluation
  fun_prop

theorem boundaryRatio_contDiffOn {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) {V : Set (BoundaryParameters E)}
    (hV : IsOpen V) (L c : ℝ)
    (hseg : ∀ θ ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, segmentEvaluation c (θ, t) ∈ U) :
    ContDiffOn ℝ ∞ (fun θ : BoundaryParameters E => boundaryRatio u L c θ.1 θ.2.1 θ.2.2) V := by
  let W := segmentEvaluation (E := E) c ⁻¹' U
  have hW : IsOpen W := hU.preimage (segmentEvaluation_contDiff c).continuous
  have hinc : V ×ˢ Icc (0 : ℝ) 1 ⊆ W := fun _ hw => hseg _ hw.1 _ hw.2
  have hgrad : ContDiffOn ℝ ∞ (fun w : BoundaryParameters E × ℝ =>
      fderiv ℝ u (segmentEvaluation c w)) W :=
    (hu.fderiv_of_isOpen hU (m := ∞) (by simp)).comp
      (segmentEvaluation_contDiff c).contDiffOn (fun _ hw => hw)
  have heval : ContDiffOn ℝ ∞ (fun w : BoundaryParameters E × ℝ => w.1.2.2) W := by
    fun_prop
  have hjoint := hgrad.clm_apply heval
  have hI := contDiffOn_fixed_intervalIntegral_of_joint hV hW hjoint hinc
  simpa only [boundaryRatio, segmentEvaluation] using
    (contDiffOn_const.sub (contDiffOn_const.mul hI))

end Yau.NodeProofs.F01Aux
