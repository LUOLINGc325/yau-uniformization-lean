import Yau.Proofs.C03SourceEnergy
import Yau.Proofs.P04FlatNakano

/-! Genuine smooth scalar weights on the complete source background give
the actual nonnegative weighted curvature of the trivial coefficient line. -/

noncomputable section
open Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
open Yau.Proofs.P04Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem inChart_euclidean (hn : 1 ≤ n) (f : ComplexVector n → ℝ)
    (a : (ComplexEuclideanManifold n hn).Carrier) :
    inChart (M := ComplexEuclideanManifold n hn) a f = f := by
  funext z
  change f ((extChartAt (ComplexModel n) (a : ComplexVector n)).symm z) = f z
  rw [extChartAt_model_space_eq_id]
  rfl

theorem smoothFn_euclidean_of_contDiff (hn : 1 ≤ n) (f : ComplexVector n → ℝ)
    (hf : ContDiff ℝ ∞ f) : SmoothFn (M := ComplexEuclideanManifold n hn) f := by
  intro a
  change ContDiffOn ℝ ∞ (inChart (M := ComplexEuclideanManifold n hn) a f) (chartTarget a)
  rw [inChart_euclidean hn f a]
  exact hf.contDiffOn

theorem flat_weightedNakano_of_source_levi (hn : 1 ≤ n) (f : ComplexVector n → ℝ)
    (hpsh : ∀ z, (leviC f z).PosSemidef) :
    BundleDbar.WeightedNakanoNonnegative (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn)) flatMetric f := by
  apply flat_weightedNakano_of_chartLevi
  intro a z _
  rw [inChart_euclidean hn f a]
  exact hpsh z

end Yau.Proofs.C03Aux
