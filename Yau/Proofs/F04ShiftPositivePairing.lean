import Yau.Proofs.F04ShiftPositiveDifferential
import Yau.Proofs.F04PositiveProjection
import Yau.Proofs.F04PositiveScalarPairing

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

/-- Both exact projection pairings for the actual supported shifted test.
These are the fixed-metric coercive Green-test identities. -/
theorem dirichletShiftPosPart_pairings
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (u : DirichletEnergy g μ hμ O) :
    let w := dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u
    inner ℝ (dirichletL2 g μ hμ O u - scalarToLp hr2) (dirichletL2 g μ hμ O w) =
        ‖dirichletL2 g μ hμ O w‖ ^ 2 ∧
      inner ℝ (dirichletD g μ hμ O u -
        realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2))
        (dirichletD g μ hμ O w) = ‖dirichletD g μ hμ O w‖ ^ 2 := by
  dsimp only
  have hs := dirichletShiftPosPart_spec g μ hμ O hO r hr hr0 hr2 hdr2 u
  constructor
  · simpa only [hs.1] using l2_posPart_pairing (μ.restrict O) (dirichletL2 g μ hμ O u - scalarToLp hr2)
  · simpa only [hs.2] using positiveFormMultiplier_pairing g (μ.restrict O)
      (dirichletL2 g μ hμ O u - scalarToLp hr2)
      (dirichletD g μ hμ O u -
        realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2))

end Yau.F04Proof
