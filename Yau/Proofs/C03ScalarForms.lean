import Yau.Proofs.C03FlatWeights
import Yau.Proofs.P04CanonicalTensors
import Yau.LeafProofs.L14Exact

/-! A genuine smooth compact scalar seed gives the actual flat-line top
form and its genuine closed Dolbeault source, in the source's global chart. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L14Aux
open Yau.Proofs.P04Aux BundleDbar
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def scalarSeedCoefficient (f : ComplexVector n → ℂ) (z : ComplexVector n) : ComplexVector 1 :=
  scalarToCoefficient (f z)

def scalarSeedTop (hn : 1 ≤ n) (f : ComplexVector n → ℂ) :
    NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 0 :=
  topFormPushforward (CanonicalCoefficients (ComplexEuclideanManifold n hn))
    (0 : ComplexVector n) (scalarSeedCoefficient f)

def scalarSeedDbar (hn : 1 ≤ n) (f : ComplexVector n → ℂ) :
    NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 1 :=
  oneFormPushforward (CanonicalCoefficients (ComplexEuclideanManifold n hn))
    (0 : ComplexVector n) (modelTopDbar (scalarSeedCoefficient f))

theorem scalarSeedCoefficient_contDiff (f : ComplexVector n → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scalarSeedCoefficient f) :=
  (scalarToCoefficient.restrictScalars ℝ).contDiff.comp hf

theorem scalarSeedCoefficient_tsupport (f : ComplexVector n → ℂ) :
    tsupport (scalarSeedCoefficient f) ⊆ tsupport f := by
  apply closure_mono
  intro z hz hzero
  exact hz (by simp only [scalarSeedCoefficient, hzero, map_zero])

theorem scalarSeedCoefficient_compact (f : ComplexVector n → ℂ) (hf : HasCompactSupport f) :
    HasCompactSupport (scalarSeedCoefficient f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (scalarSeedCoefficient_tsupport f)

theorem coefficient_source_localDomain (hn : 1 ≤ n) (a : ComplexVector n) :
    localDomain (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn)) a = univ := by
  rw [coefficient_localDomain, euclidean_chartTarget hn]

theorem scalarSeedTop_smooth (hn : 1 ≤ n) (f : ComplexVector n → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    SmoothForm (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (scalarSeedTop hn f) := by
  apply topFormPushforward_smooth _ coefficient_holomorphic (0 : ComplexVector n)
    (scalarSeedCoefficient f) (scalarSeedCoefficient_contDiff f hf) (scalarSeedCoefficient_compact f hfc)
  rw [coefficient_source_localDomain hn]
  exact subset_univ _

theorem scalarSeed_isDbarOf (hn : 1 ≤ n) (f : ComplexVector n → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    IsDbarOf (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (scalarSeedTop hn f) (scalarSeedDbar hn f) := by
  apply topFormPushforward_isDbarOf _ coefficient_holomorphic (0 : ComplexVector n)
    (scalarSeedCoefficient f) (scalarSeedCoefficient_contDiff f hf) (scalarSeedCoefficient_compact f hfc)
  rw [coefficient_source_localDomain hn]
  exact subset_univ _

theorem scalarSeedDbar_smooth (hn : 1 ≤ n) (f : ComplexVector n → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    SmoothForm (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (scalarSeedDbar hn f) :=
  smoothForm_of_isDbarOf _ _ _ (scalarSeedTop_smooth hn f hf hfc) (scalarSeed_isDbarOf hn f hf hfc)

theorem scalarSeed_weakDbar (hn : 1 ≤ n) (f : ComplexVector n → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    WeakDbar (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (scalarSeedTop hn f) (scalarSeedDbar hn f) :=
  weakDbar_of_smooth_isDbarOf _ _ _ (scalarSeedTop_smooth hn f hf hfc)
    (scalarSeedDbar_smooth hn f hf hfc) (scalarSeed_isDbarOf hn f hf hfc)

theorem scalarSeed_weaklyClosed (hn : 1 ≤ n) (f : ComplexVector n → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    WeaklyClosed (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (scalarSeedDbar hn f) :=
  weakDbar_weaklyClosed_top _ _ _ (scalarSeed_weakDbar hn f hf hfc)

end Yau.Proofs.C03Aux
