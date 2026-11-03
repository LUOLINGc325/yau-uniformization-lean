import Yau.Proofs.V01QuadraticTimeJet
import Yau.Proofs.E02LocalPeano

/-! V01 scratch source: use the canonical published finite-C² Peano bridge.
Pointwise C∞ never supplies a common C∞ neighborhood. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Blueprint.V01Proof

variable {n : ℕ}

def canonicalQuadraticSupport
    (f : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ) (α : ℝ) :
    ComplexVector n × ComplexVector n × ℝ → ℝ :=
  quadraticSupport f a (fderiv ℝ f a) (fderiv ℝ (fderiv ℝ f) a) α

theorem canonicalQuadraticSupport_contDiff
    (f : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ) (α : ℝ) :
    ContDiff ℝ ∞ (canonicalQuadraticSupport f a α) :=
  quadraticSupport_contDiff f a _ _ α

@[simp] theorem canonicalQuadraticSupport_self
    (f : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ) (α : ℝ) :
    canonicalQuadraticSupport f a α a = f a :=
  quadraticSupport_self f a _ _ α

theorem canonicalQuadraticSupport_strict_margin
    {f : ComplexVector n × ComplexVector n × ℝ → ℝ}
    {a : ComplexVector n × ComplexVector n × ℝ}
    (hf : ContDiffAt ℝ 2 f a) {α : ℝ} (hα : 0 < α) :
    ∀ᶠ y in 𝓝 a, canonicalQuadraticSupport f a α y +
      (α / 2) * coordinateSquare a y ≤ f y :=
  quadraticSupport_strict_margin
    (Yau.NodeProofs.E02Aux.realSecondJet_of_contDiffAt_two hf) hα

theorem canonicalQuadraticSupport_time_deriv
    {f : ComplexVector n × ComplexVector n × ℝ → ℝ}
    {a : ComplexVector n × ComplexVector n × ℝ}
    (hf : ContDiffAt ℝ 2 f a) (α : ℝ) :
    deriv (fun t => canonicalQuadraticSupport f a α (a.1, a.2.1, t)) a.2.2 =
      deriv (fun t => f (a.1, a.2.1, t)) a.2.2 :=
  quadraticSupport_time_deriv_eq (hf.differentiableAt (by norm_num)) _
    (Yau.NodeProofs.E02Aux.realSecondJet_of_contDiffAt_two hf).1 α

end Yau.Blueprint.V01Proof
