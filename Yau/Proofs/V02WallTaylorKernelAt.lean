import Yau.Proofs.V02WallTaylorClearedKernels

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem clearedInverseIncrement_contDiffAt (a : ℕ) {u v R : E → ℝ} {p : E}
    (hu : ContDiffAt ℝ ∞ u p) (hv : ContDiffAt ℝ ∞ v p) (hR : ContDiffAt ℝ ∞ R p)
    (hden : 1 + wallRatioMultiplier a (u p) (v p) * R p ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => clearedInverseIncrement a (u q) (v q) (R q)) p :=
  (((hu.pow _).mul (hv.pow _)).mul hR).neg.div
    (contDiffAt_const.add (((hu.pow _).mul (hv.pow _)).mul hR)) hden

theorem clearedLogIncrement_contDiffAt (a : ℕ) {u v R : E → ℝ} {p : E}
    (hu : ContDiffAt ℝ ∞ u p) (hv : ContDiffAt ℝ ∞ v p) (hR : ContDiffAt ℝ ∞ R p)
    (hden : 1 + wallRatioMultiplier a (u p) (v p) * R p ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => clearedLogIncrement a (u q) (v q) (R q)) p :=
  (contDiffAt_const.add (((hu.pow _).mul (hv.pow _)).mul hR)).log hden

end Yau.Blueprint.V02WallTaylorProof
