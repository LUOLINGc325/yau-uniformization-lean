import Yau.Blueprint.VariationContracts
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Explicit cutoffs leave a neighborhood of every point with cutoff less
than one inside the constant part of the original wall profile. -/

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

def baseClockProfile (r : ℝ) : ℝ := Real.smoothTransition (6 * r - 2)
def fiberClockProfile (r : ℝ) : ℝ := Real.smoothTransition (8 * r - 2)

def chosenClockData {n : ℕ} (X : KahlerManifold n) (C : ℕ → ℝ) : ClockData X where
  cutoffBaseProfile := baseClockProfile
  cutoffFiberProfile := fiberClockProfile
  fiberCoefficient := C
  fiberPower := 6
  dampingPower := 10
  fiberSupportScale := 1 / 4

theorem baseClockProfile_contDiff : ContDiff ℝ ∞ baseClockProfile :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem fiberClockProfile_contDiff : ContDiff ℝ ∞ fiberClockProfile :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem baseClockProfile_bounds (r : ℝ) :
    0 ≤ baseClockProfile r ∧ baseClockProfile r ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem fiberClockProfile_bounds (r : ℝ) :
    0 ≤ fiberClockProfile r ∧ fiberClockProfile r ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem baseClockProfile_zero {r : ℝ} (hr : r ≤ 1 / 3) : baseClockProfile r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem baseClockProfile_one {r : ℝ} (hr : 1 / 2 ≤ r) : baseClockProfile r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem fiberClockProfile_zero {r : ℝ} (hr : r ≤ 1 / 4) : fiberClockProfile r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem fiberClockProfile_one {r : ℝ} (hr : 3 / 8 ≤ r) : fiberClockProfile r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem baseClockProfile_lt_one {r : ℝ} (hr : baseClockProfile r < 1) : r < 1 / 2 := by
  by_contra h
  rw [baseClockProfile_one (le_of_not_gt h)] at hr
  exact (lt_irrefl 1) hr

theorem fiberClockProfile_lt_one {r : ℝ} (hr : fiberClockProfile r < 1) : r < 3 / 8 := by
  by_contra h
  rw [fiberClockProfile_one (le_of_not_gt h)] at hr
  exact (lt_irrefl 1) hr

theorem chosenClockData_powers {n : ℕ} (X : KahlerManifold n) (C : ℕ → ℝ)
    {a : ℕ} (ha : 4 ≤ a) :
    (chosenClockData X C).fiberPower + 3 ≤ 4 * a ∧
      (chosenClockData X C).fiberPower + 3 < (chosenClockData X C).dampingPower := by
  dsimp [chosenClockData]
  omega

variable {n q : ℕ} {X : KahlerManifold n}

theorem base_wall_profile_constant_near {d : VariationData X q} (hp : WallProfiles d)
    {r : ℝ} (hr : baseClockProfile r < 1) :
    ∃ V : Set ℝ, IsOpen V ∧ r ∈ V ∧ ∀ r' ∈ V, d.profileBase r' = 1 := by
  refine ⟨Set.Iio (2 / 3), isOpen_Iio, ?_, fun r' hr' => (hp.2.2.1 r').2.2.2 hr'.le⟩
  change r < (2 / 3 : ℝ)
  have := baseClockProfile_lt_one hr
  linarith

theorem fiber_wall_profile_constant_near {d : VariationData X q} (hp : WallProfiles d)
    {r : ℝ} (hr : fiberClockProfile r < 1) :
    ∃ V : Set ℝ, IsOpen V ∧ r ∈ V ∧ ∀ r' ∈ V, d.profileFiber r' = 1 := by
  refine ⟨Set.Iio (1 / 2), isOpen_Iio, ?_, fun r' hr' => (hp.2.2.2 r').2.2.2 hr'.le⟩
  change r < (1 / 2 : ℝ)
  have := fiberClockProfile_lt_one hr
  linarith

theorem clockBaseCutoff_support (d : VariationData X q) (C : ℕ → ℝ) (j : ℕ)
    (hA : 0 < d.A j) :
    Function.support (clockBaseCutoff d (chosenClockData X C) j) ⊆
      {x | d.A j / 3 < d.u x} := by
  intro x hx
  change clockBaseCutoff d (chosenClockData X C) j x ≠ 0 at hx
  by_contra h
  apply hx
  apply baseClockProfile_zero
  apply (div_le_iff₀ hA).2
  have hux : d.u x ≤ d.A j / 3 := le_of_not_gt h
  linarith

theorem clockFiberCutoff_support (d : VariationData X q) (C : ℕ → ℝ) (j : ℕ)
    (hB : 0 < d.B j) :
    Function.support (clockFiberCutoff d (chosenClockData X C) j) ⊆
      {y | (1 / 4 : ℝ) * d.B j ^ 2 < dualNorm (d.h 0) y.1 y.2} := by
  intro y hy
  change clockFiberCutoff d (chosenClockData X C) j y ≠ 0 at hy
  by_contra h
  apply hy
  apply fiberClockProfile_zero
  apply (div_le_iff₀ (sq_pos_of_pos hB)).2
  exact le_of_not_gt h

end Yau.Blueprint.V04Proof
