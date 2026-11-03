import Yau.Proofs.F04ShiftInclusion
import Yau.Proofs.F04CompletedCoreTest
import Yau.Proofs.F04InclusionPairing

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

/-- The actual smooth shifted test has the exact larger-domain form energy.
 The Laplacian term uses the actual compact profile's completed L2 class. -/
theorem localCoreForm_shift_identity
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {O W : Set M.Carrier}
    (hO : IsOpen O) (hW : IsOpen W) (hOW : O ⊆ W)
    (H : HermitianField M) (hH : MetricSmooth H)
    (B : DirichletEnergy g μ hμ O →L[ℝ] DirichletEnergy g μ hμ O →L[ℝ] ℝ)
    (A : DirichletEnergy g μ hμ W →L[ℝ] DirichletEnergy g μ hμ W →L[ℝ] ℝ)
    (hB : ∀ f v : dirichletCore g μ hμ O,
      B (dirichletCoreToEnergy g μ hμ O f) (dirichletCoreToEnergy g μ hμ O v) =
        -(∫ x in O, v.val x * laplacian H f.val x ∂μ))
    (hA : ∀ f v : dirichletCore g μ hμ W,
      A (dirichletCoreToEnergy g μ hμ W f) (dirichletCoreToEnergy g μ hμ W v) =
        -(∫ x in W, v.val x * laplacian H f.val x ∂μ))
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (f : dirichletCore g μ hμ W) (hf0 : ∀ x ∈ W, 0 ≤ f.val x)
    (hfr : ∀ x ∈ O, f.val x = r x) (u : DirichletEnergy g μ hμ O) :
    let w := dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u
    B u w + inner ℝ (scalarToLp (dirichletCore_laplacian_scalarL2 g μ hμ W H hH f))
      (dirichletL2 g μ hμ W (dirichletInclusion g μ hμ hOW w)) =
        A (dirichletInclusion g μ hμ hOW w) (dirichletInclusion g μ hμ hOW w) := by
  let I := dirichletInclusion g μ hμ hOW
  let w := dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u
  let q := dirichletCoreToEnergy g μ hμ W f
  have hw := dirichletInclusion_shiftPosPart g hK μ hμ hO hW hOW r hr hr0 hr2 hdr2 f hf0 hfr u
  change I w = dirichletPosPart g μ hμ W hW.measurableSet (I u - q) at hw
  have hm := localCoreForm_posPart_test g hK μ hμ W hW.measurableSet H A hA (I u - q)
  rw [← hw] at hm
  have he : A (I u - q) (I w) = A (I u) (I w) - A q (I w) :=
    congrArg (fun L : DirichletEnergy g μ hμ W →L[ℝ] ℝ => L (I w)) (A.map_sub (I u) q)
  rw [he] at hm
  have ht := localCoreForm_completed_test g μ hμ W H hH A hA f (I w)
  change A q (I w) = _ at ht
  rw [ht, sub_neg_eq_add] at hm
  have hIncl := localCoreForm_inclusion_eq g μ hμ hOW H B A hB hA u w
  rw [← hIncl] at hm
  exact hm

end Yau.F04Proof
