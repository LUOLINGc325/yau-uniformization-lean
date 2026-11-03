import Yau.Proofs.V02WallTaylorFactors
import Yau.Proofs.V02WallTaylorParameterJets

/-! Smooth reciprocal differences and log increments. Their definitions
extend to zero cutoff values and contain no reciprocal of a cutoff. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof

def clearedInverseIncrement (a : ℕ) (u v R : ℝ) : ℝ :=
  -(wallInverseMultiplier a u v * R) / (1 + wallRatioMultiplier a u v * R)

def clearedLogIncrement (a : ℕ) (u v R : ℝ) : ℝ :=
  Real.log (1 + wallRatioMultiplier a u v * R)

theorem clearedInverseIncrement_zero (a : ℕ) (u v : ℝ) :
    clearedInverseIncrement a u v 0 = 0 := by simp [clearedInverseIncrement]

theorem clearedLogIncrement_zero (a : ℕ) (u v : ℝ) :
    clearedLogIncrement a u v 0 = 0 := by simp [clearedLogIncrement]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem clearedInverseIncrement_contDiffOn (a : ℕ) {U : Set E}
    {u v R : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hR : ContDiffOn ℝ ∞ R U)
    (hden : ∀ p ∈ U, 1 + wallRatioMultiplier a (u p) (v p) * R p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => clearedInverseIncrement a (u p) (v p) (R p)) U := by
  exact (((hu.pow _).mul (hv.pow _)).mul hR).neg.div
    (contDiffOn_const.add (((hu.pow _).mul (hv.pow _)).mul hR)) hden

theorem clearedLogIncrement_contDiffOn (a : ℕ) {U : Set E}
    {u v R : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hR : ContDiffOn ℝ ∞ R U)
    (hden : ∀ p ∈ U, 1 + wallRatioMultiplier a (u p) (v p) * R p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => clearedLogIncrement a (u p) (v p) (R p)) U := by
  exact (contDiffOn_const.add (((hu.pow _).mul (hv.pow _)).mul hR)).log hden

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem clearedInverseIncrement_parameterJet_contDiffOn (a m : ℕ)
    {U : Set (E × P)} (hU : IsOpen U) {u v R : E × P → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) (hR : ContDiffOn ℝ ∞ R U)
    (hden : ∀ p ∈ U, 1 + wallRatioMultiplier a (u p) (v p) * R p ≠ 0) :
    ContDiffOn ℝ ∞ (parameterJet (fun p => clearedInverseIncrement a (u p) (v p) (R p)) m) U :=
  parameterJet_contDiffOn hU (clearedInverseIncrement_contDiffOn a hu hv hR hden) m

theorem clearedLogIncrement_parameterJet_contDiffOn (a m : ℕ)
    {U : Set (E × P)} (hU : IsOpen U) {u v R : E × P → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) (hR : ContDiffOn ℝ ∞ R U)
    (hden : ∀ p ∈ U, 1 + wallRatioMultiplier a (u p) (v p) * R p ≠ 0) :
    ContDiffOn ℝ ∞ (parameterJet (fun p => clearedLogIncrement a (u p) (v p) (R p)) m) U :=
  parameterJet_contDiffOn hU (clearedLogIncrement_contDiffOn a hu hv hR hden) m

end Yau.Blueprint.V02WallTaylorProof
