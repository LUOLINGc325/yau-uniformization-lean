import Yau.Proofs.E02PeanoUnique
import Yau.Proofs.E02StrictTest

open scoped Topology ContDiff
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The strictifying Euclidean quartic preserves the genuine derivative
of the original C² test, not just its formal coefficient. -/
theorem strictifyTest_fderiv {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (strictifyTest f x) x = fderiv ℝ f x :=
  (realSecondJet_hasFDerivAt (realSecondJet_strictify (realSecondJet_of_contDiffAt_two hf))).fderiv

/-- Actual second Frechet derivatives agree, using the true C² germs of
both tests and the proved uniqueness of their symmetric Peano tensors. -/
theorem strictifyTest_second_fderiv {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (fderiv ℝ (strictifyTest f x)) x = fderiv ℝ (fderiv ℝ f) x :=
  realSecondJet_second_fderiv_eq
    (realSecondJet_strictify (realSecondJet_of_contDiffAt_two hf)) (strictifyTest_contDiffAt_two hf)

end Yau.NodeProofs.E02Aux
