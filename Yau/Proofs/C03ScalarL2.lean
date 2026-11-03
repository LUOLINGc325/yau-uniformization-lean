import Yau.Proofs.C03ScalarForms
import Yau.Proofs.C03FlatComplete

/-! The actual compact scalar seed and its actual Dolbeault source satisfy
the fixed-background weighted L² requirements of the smooth L14 theorem. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L14Aux Yau.Proofs.P04Aux BundleDbar
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem scalarModelDbar_compact (f : ComplexVector n → ℂ) (hfc : HasCompactSupport f) :
    HasCompactSupport (modelTopDbar (scalarSeedCoefficient f)) :=
  (scalarSeedCoefficient_compact f hfc).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_modelTopDbar_subset _)

theorem scalarSeedTop_weightedL2 (hn : 1 ≤ n) (f : ComplexVector n → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    WeightedL2 (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric
      (FlatComplete.euclideanVolume n hn) φ (scalarSeedTop hn f) := by
  apply topFormPushforward_weightedL2 _ (FlatComplete.euclideanCompleteMetric n hn)
    (FlatComplete.euclideanVolume n hn) (FlatComplete.euclideanCompleteMetric_volume n hn)
    flatMetric flatMetric_smooth φ (smoothFn_euclidean_of_contDiff hn φ hφ)
    coefficient_holomorphic (0 : ComplexVector n) (scalarSeedCoefficient f)
    (scalarSeedCoefficient_contDiff f hf) (scalarSeedCoefficient_compact f hfc)
  rw [coefficient_source_localDomain hn]
  exact subset_univ _

theorem scalarSeedDbar_weightedL2 (hn : 1 ≤ n) (f : ComplexVector n → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    WeightedL2 (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric
      (FlatComplete.euclideanVolume n hn) φ (scalarSeedDbar hn f) := by
  apply oneFormPushforward_weightedL2 _ (FlatComplete.euclideanCompleteMetric n hn)
    (FlatComplete.euclideanVolume n hn) (FlatComplete.euclideanCompleteMetric_volume n hn)
    flatMetric flatMetric_smooth φ (smoothFn_euclidean_of_contDiff hn φ hφ)
    coefficient_holomorphic (0 : ComplexVector n) (modelTopDbar (scalarSeedCoefficient f))
    (modelTopDbar_smooth _ (scalarSeedCoefficient_contDiff f hf)) (scalarModelDbar_compact f hfc)
  rw [coefficient_source_localDomain hn]
  exact subset_univ _

end Yau.Proofs.C03Aux
