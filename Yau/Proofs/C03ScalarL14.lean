import Yau.Proofs.C03ScalarL2
import Yau.Proofs.P03OneRegularizedSolution

/-! Smooth L14 on the genuine complete Euclidean background gives one
actual representative for the compact scalar seed and every pole weight. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L14Aux Yau.Proofs.P04Aux BundleDbar
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem exists_scalar_seed_common_solution (hn : 1 ≤ n)
    (f : ComplexVector n → ℂ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (p : ℕ → ComplexVector n → ℝ) (hp : ∀ j, ContDiff ℝ ∞ (p j))
    (hpc : ∀ j, HasCompactSupport (p j)) (hp0 : ∀ j z, p j z ≤ 0)
    (hpm : ∀ z, Antitone (fun j => p j z))
    (hcurv : ∀ j z, (leviC (fun w => φ w + p j w) z).PosSemidef)
    (B : ℝ) (hB : 0 ≤ B)
    (hsource : ∀ j, inverseCurvatureIntegral (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric
      (FlatComplete.euclideanVolume n hn) (fun z => φ z + p j z)
      (scalarSeedDbar hn f) ≤ ENNReal.ofReal B) :
    ∃ u : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 0,
      WeakDbar (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
        u (scalarSeedDbar hn f) ∧
      WeightedL2 (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
        (FlatComplete.euclideanCompleteMetric n hn).form flatMetric
        (FlatComplete.euclideanVolume n hn) φ u ∧
      ∀ j, weightedNormSq (r := 1)
        (CanonicalCoefficients (ComplexEuclideanManifold n hn))
        (FlatComplete.euclideanCompleteMetric n hn).form flatMetric
        (FlatComplete.euclideanVolume n hn) (fun z => φ z + p j z) u ≤ ENNReal.ofReal B := by
  exact Yau.NodeProofs.P03Aux.one_solution_all_regularized_bounds
    (CanonicalCoefficients (ComplexEuclideanManifold n hn))
    (FlatComplete.euclideanCompleteMetric n hn) (FlatComplete.euclideanVolume n hn)
    (FlatComplete.euclideanCompleteMetric_volume n hn) flatMetric flatMetric_smooth
    coefficient_holomorphic φ (smoothFn_euclidean_of_contDiff hn φ hφ)
    p (fun j => smoothFn_euclidean_of_contDiff hn (p j) (hp j)) hpc hp0 hpm
    (scalarSeedDbar hn f) (scalarSeed_weaklyClosed hn f hf hfc)
    (scalarSeedDbar_weightedL2 hn f hf hfc φ hφ)
    (fun j => flat_weightedNakano_of_source_levi hn (fun z => φ z + p j z) (hcurv j))
    B hB hsource

end Yau.Proofs.C03Aux
