import Yau.LeafProofs.L18Poincare

/-! The original Li--Schoen leaf, proved through actual minimizing
segments, scalar Poincaré and Sobolev estimates, and Moser iteration. -/

namespace Yau.LeafProofs

theorem L18 : Yau.LeafObligations.L18 := by
  apply L18Aux.liSchoenMeanValue_of_ballScalarSobolev
  intro n hn
  exact L18Aux.exists_ballScalarSobolevEstimate_of_poincare n hn
    ⟨(2 : ℝ) ^ (2 * n + 1), by positivity, L18Aux.ballScalarPoincareEstimate n⟩

end Yau.LeafProofs
