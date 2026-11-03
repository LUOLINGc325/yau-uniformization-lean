import Yau.Proofs.P04CanonicalRegularity
import Yau.Proofs.P04NestedConvex

noncomputable section
open Set MeasureTheory Bundle
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}
variable (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ)

/-- The solution set is the slice of the actual distributional Dolbeault
Hilbert graph at the actual finite weighted source. -/
def canonicalDbarSlice
    (f : L14Aux.WeightedOneSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ) :
    Set (L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ) :=
  {v | (v,L14Aux.realizeWeightedOneSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ f) ∈
    L14Aux.weightedMaximalDbarHilbertGraph (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ}

theorem canonicalDbarSlice_isClosed
    (f : L14Aux.WeightedOneSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ) :
    IsClosed (canonicalDbarSlice g μ hμ Φ hΦ f) :=
  (L14Aux.weightedMaximalDbarHilbertGraph_isClosed (CanonicalCoefficients M) g μ hμ
    flatMetric flatMetric_smooth Φ hΦ).preimage (continuous_id.prodMk continuous_const)

theorem canonicalDbarSlice_convex
    (f : L14Aux.WeightedOneSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ) :
    Convex ℝ (canonicalDbarSlice g μ hμ Φ hΦ f) := by
  let G := (L14Aux.weightedMaximalDbarHilbertGraph (CanonicalCoefficients M) g μ hμ
    flatMetric flatMetric_smooth Φ hΦ).restrictScalars ℝ
  intro u hu v hv a b ha hb hab
  have H := G.convex hu hv ha hb hab
  change (a • u+b • v,_) ∈ G
  have heq : a • (u,L14Aux.realizeWeightedOneSection (CanonicalCoefficients M) g μ hμ
        flatMetric flatMetric_smooth Φ hΦ f) +
      b • (v,L14Aux.realizeWeightedOneSection (CanonicalCoefficients M) g μ hμ
        flatMetric flatMetric_smooth Φ hΦ f) =
      (a • u+b • v,L14Aux.realizeWeightedOneSection (CanonicalCoefficients M) g μ hμ
        flatMetric flatMetric_smooth Φ hΦ f) := by
    apply Prod.ext
    · rfl
    · dsimp
      rw [← add_smul,hab,one_smul]
  rw [heq] at H
  exact H

theorem canonicalDbarSlice_mem_iff
    (f : L14Aux.WeightedOneSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ)
    (v : L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ) :
    v ∈ canonicalDbarSlice g μ hμ Φ hΦ f ↔
      WeakDbar (r := 1) (CanonicalCoefficients M)
        (L14Aux.weightedTopHilbertRepresentative (CanonicalCoefficients M) g μ hμ
          flatMetric flatMetric_smooth Φ hΦ v).1 f.1 := by
  have H := L14Aux.weightedMaximalDbarHilbertGraph_realize_iff (CanonicalCoefficients M) g μ hμ
    flatMetric flatMetric_smooth Φ hΦ
    (L14Aux.weightedTopHilbertRepresentative (CanonicalCoefficients M) g μ hμ
      flatMetric flatMetric_smooth Φ hΦ v) f
  simpa only [L14Aux.weightedTopHilbertRepresentative_realize,canonicalDbarSlice,mem_setOf_eq] using H

end Yau.Proofs.P04Aux
