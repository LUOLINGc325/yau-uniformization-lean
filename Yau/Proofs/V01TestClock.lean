import Yau.Proofs.V01TimeField
import Yau.Proofs.V01ChartTest

/-! The clock inequality contains the ordinary derivative of the actual
geometric test. Its ordered limit follows from the original center limit. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem localized_test_time_slope
    (d : VariationData X q)
    (ψ : ComplexVector n × ComplexVector n × ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hTest : d.test = chartTest d.chart ψ)
    (F : ℕ → ℝ → ℕ → VariationDisc X)
    (hF : LocalizedMinimizers d F) (hLoc : LocalizationEstimates d) :
    LocalizedZero (fun j ε ν =>
      deriv (d.test ((F j ε ν).f 0)) (F j ε ν).s -
        coordinateTimeSlope ψ (contactAssoc d.contact)) := by
  have hCenter := (hLoc.2.2 F hF).2.2.1
  have hSlope := localized_time_slope (n := n) hψ hCenter
  rw [hTest]
  change LocalizedZero (fun j ε ν =>
    coordinateTimeSlope ψ (contactAssoc
      (cotangentChart d.chart ((F j ε ν).f 0), (F j ε ν).s)) -
        coordinateTimeSlope ψ (contactAssoc d.contact))
  exact hSlope

end Yau.Blueprint.V01Proof
