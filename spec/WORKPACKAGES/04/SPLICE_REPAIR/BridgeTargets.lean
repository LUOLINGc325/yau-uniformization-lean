import Yau.Blueprint.ConcreteExtensions

/-! Closed proposition definitions for exactly the three registered internal
outputs. These are statements; no analytic producer is asserted or proved. -/
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle
noncomputable section
namespace Yau.Blueprint.SpliceRepair
open Yau

def SameMetricSmoothness : Prop :=
  ∀ (n : ℕ) (M : ComplexManifold n) (g : SmoothMetric M),
    IsSmooth g → MetricSmooth g.form

def CotangentBoxCompact : Prop :=
  ∀ (n : ℕ) (M : ComplexManifold n) (g : HermitianField M),
    MetricSmooth g → ∀ (K : Set M.Carrier) (R : ℝ), IsCompact K →
      CotangentCompact {y : CotangentPoint M | InCotangentCompact g K R y.1 y.2}

def CotangentCompactEnclosure : Prop :=
  ∀ (n : ℕ) (M : ComplexManifold n) (g : HermitianField M),
    MetricSmooth g → ∀ L : Set (CotangentPoint M), CotangentCompact L →
      ∃ (K : Set M.Carrier) (R : ℝ), IsCompact K ∧
        ∀ y ∈ L, InCotangentCompact g K R y.1 y.2

end Yau.Blueprint.SpliceRepair
