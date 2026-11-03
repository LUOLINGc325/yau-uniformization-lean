import Yau.Proofs.V04CutoffProfiles
import Yau.Proofs.V04Enlargement
import Yau.Proofs.V03DualTransport
import Yau.Proofs.V03MetricSmooth

/-! The explicit cutoff profiles give the original clock-cutoff predicate
on the same enlarged localization, using valid induced cotangent charts. -/

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem clockCutoffs_of_log_radius {d : VariationData X q} (hd : VariationSetup d)
    (C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j)
    (hlog : Tendsto (fun j => Real.log (C j) / d.B j ^ 2) atTop (𝓝 0)) :
    ClockCutoffs d (chosenClockData X C) := by
  rcases hd with ⟨_, _, hflow, hu, _, _, hp, _, _, _, _, _, _, hindex⟩
  have hzero : d.h 0 = X.metric.form := hflow.1.1.1
  refine ⟨by norm_num [chosenClockData], baseClockProfile_contDiff,
    fiberClockProfile_contDiff, fun j => ?_, hlog⟩
  have hA : 0 < d.A j := (hindex j).1
  have hB : 0 < d.B j := lt_of_lt_of_le (by positivity : (0 : ℝ) < j + 1) (hindex j).2.1
  refine ⟨hC j, ?_, ?_, clockBaseCutoff_support d C j hA,
    ?_, clockFiberCutoff_support d C j hB, ?_⟩
  · intro x
    exact baseClockProfile_contDiff.comp_contDiffOn ((hu.1 x).div_const (d.A j))
  · intro x
    refine ⟨(baseClockProfile_bounds _).1, (baseClockProfile_bounds _).2, ?_⟩
    intro hnot
    apply baseClockProfile_one
    by_contra h
    apply hnot
    apply (hp.2.2.1 (d.u x / d.A j)).2.2.2
    have := lt_of_not_ge h
    linarith
  · intro y
    refine ⟨(fiberClockProfile_bounds _).1, (fiberClockProfile_bounds _).2, ?_⟩
    intro hnot
    apply fiberClockProfile_one
    by_contra h
    apply hnot
    apply (hp.2.2.2 (dualNorm (d.h 0) y.1 y.2 / d.B j ^ 2)).2.2.2
    have := lt_of_not_ge h
    linarith
  · intro x
    have hnorm : ContDiffOn ℝ ∞ (fun z =>
        dualNorm (d.h 0) (cotangentChartInv x z).1 (cotangentChartInv x z).2)
        (cotangentTarget x) := by
      rw [hzero]
      exact (dualNormChart_contDiffOn X.metric x).congr
        (fun z hz => dualNorm_cotangentChartInv X.metric.form x hz)
    exact fiberClockProfile_contDiff.comp_contDiffOn (hnorm.div_const (d.B j ^ 2))

/-- The coefficient is held fixed while both the setup and every cutoff
condition are transported to the explicitly enlarged radii. -/
theorem exists_clock_cutoff_enlargement {d : VariationData X q} (hd : VariationSetup d)
    (C : ℕ → ℝ) (hC : ∀ j, 1 ≤ C j) :
    ∃ B : ℕ → ℝ, (∀ j, d.B j ≤ B j) ∧
      VariationSetup {d with B := B} ∧ ClockCutoffs {d with B := B} (chosenClockData X C) := by
  obtain ⟨B, hB, hdb, _, hlog⟩ := exists_localization_enlargement hd C hC
  exact ⟨B, hB, hdb, clockCutoffs_of_log_radius hdb C hC hlog⟩

end Yau.Blueprint.V04Proof
