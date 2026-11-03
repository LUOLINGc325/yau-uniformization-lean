import Yau.Proofs.V01QuadraticTimeJet
import Yau.Proofs.V01TestClock

/-! The actual polynomial support retains the original physical derivative,
including after the localization data have been enlarged. -/

noncomputable section
open scoped Topology ContDiff
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem canonicalQuadraticSupport_timeSlope
    {φ : ComplexVector n × ComplexVector n × ℝ → ℝ}
    {p : ComplexVector n × ComplexVector n × ℝ}
    (hφ : ContDiffAt ℝ 2 φ p) (α : ℝ) :
    coordinateTimeSlope (canonicalQuadraticSupport φ p α) p =
      coordinateTimeSlope φ p := by
  exact quadraticSupport_time_deriv_eq (hφ.differentiableAt (by norm_num))
    (fderiv ℝ (fderiv ℝ φ) p)
    (Yau.NodeProofs.E02Aux.realSecondJet_of_contDiffAt_two hφ).1 α

theorem localized_support_time_slope
    (d : VariationData X q)
    {φ : ComplexVector n × ComplexVector n × ℝ → ℝ}
    {p : ComplexVector n × ComplexVector n × ℝ}
    (hφ : ContDiffAt ℝ 2 φ p) (α : ℝ)
    (hTest : d.test = chartTest d.chart (canonicalQuadraticSupport φ p α))
    (hContact : contactAssoc d.contact = p)
    (F : ℕ → ℝ → ℕ → VariationDisc X)
    (hF : LocalizedMinimizers d F) (hLoc : LocalizationEstimates d) :
    LocalizedZero (fun j ε ν =>
      deriv (d.test ((F j ε ν).f 0)) (F j ε ν).s - coordinateTimeSlope φ p) := by
  have hSmooth : ContDiff ℝ 1 (canonicalQuadraticSupport φ p α) :=
    (canonicalQuadraticSupport_contDiff φ p α).of_le (by norm_num)
  have h := localized_test_time_slope d _ hSmooth hTest F hF hLoc
  rwa [hContact, canonicalQuadraticSupport_timeSlope hφ α] at h

end Yau.Blueprint.V01Proof
