import Yau.Proofs.P04DbarSlice

noncomputable section
open Set MeasureTheory Bundle
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

/-- Subtraction in the actual Hilbert graph preserves the homogeneous
distributional equation for actual tensor representatives. -/
theorem canonicalDbar_difference (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ)
    (u v : L14Aux.WeightedTopSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ)
    (f : L14Aux.WeightedOneSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ)
    (hu : WeakDbar (r := 1) (CanonicalCoefficients M) u.1 f.1)
    (hv : WeakDbar (r := 1) (CanonicalCoefficients M) v.1 f.1) :
    WeakDbar (r := 1) (CanonicalCoefficients M) (u-v).1
      (0 : NQForm (CanonicalCoefficients M) 1) := by
  let G := L14Aux.weightedMaximalDbarHilbertGraph (CanonicalCoefficients M) g μ hμ
    flatMetric flatMetric_smooth Φ hΦ
  have huG := (L14Aux.weightedMaximalDbarHilbertGraph_realize_iff (CanonicalCoefficients M)
    g μ hμ flatMetric flatMetric_smooth Φ hΦ u f).mpr hu
  have hvG := (L14Aux.weightedMaximalDbarHilbertGraph_realize_iff (CanonicalCoefficients M)
    g μ hμ flatMetric flatMetric_smooth Φ hΦ v f).mpr hv
  have hsub := G.sub_mem huG hvG
  apply (L14Aux.weightedMaximalDbarHilbertGraph_realize_iff (CanonicalCoefficients M)
    g μ hμ flatMetric flatMetric_smooth Φ hΦ (u-v) 0).mp
  change ((↑(u-v) : UniformSpace.Completion _),(↑(0 : L14Aux.WeightedOneSection
    (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ) : UniformSpace.Completion _)) ∈ G
  simpa only [Prod.mk_sub_mk,sub_self,L14Aux.realizeWeightedTopSection,
    L14Aux.realizeWeightedOneSection,UniformSpace.Completion.coe_sub,
    UniformSpace.Completion.coe_zero] using hsub

end Yau.Proofs.P04Aux
