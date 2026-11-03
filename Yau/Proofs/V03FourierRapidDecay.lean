import Yau.Proofs.V03FourierDecay
import Yau.Proofs.V03PeriodicCircle
import Yau.Proofs.V03FourierTranslation

/-! Smooth periodic traces have arbitrarily high Fourier decay. The
finite bound is derived from their actual derivative trace on the compact circle. -/

open scoped Topology ContDiff
open MeasureTheory Filter AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem fourierCoeff_norm_le_bound {T : ℝ} [Fact (0 < T)] {u : AddCircle T → ℂ}
    {C : ℝ} (hC : ∀ x, ‖u x‖ ≤ C) (k : ℤ) : ‖fourierCoeff u k‖ ≤ C := by
  unfold fourierCoeff
  have hb : ∀ᵐ x : AddCircle T ∂haarAddCircle, ‖fourier (-k) x • u x‖ ≤ C := by
    apply Eventually.of_forall
    intro x
    rw [norm_smul, fourier_point_norm, one_mul]
    exact hC x
  simpa using norm_integral_le_of_norm_le_const hb

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem circleFourier_rapid_decay {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u (2 * Real.pi)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℤ, k ≠ 0 →
      ‖circleFourier u k‖ ≤ |(k : ℝ)|⁻¹ ^ m * C := by
  have hper := periodic_iteratedDeriv hp m
  have hcont := hu.continuous_iteratedDeriv m (by simp)
  let v : C(AddCircle (2 * Real.pi), ℂ) := ⟨hper.lift, periodic_lift_continuous hper hcont⟩
  refine ⟨‖v‖, norm_nonneg _, ?_⟩
  intro k hk
  have hb : ‖circleFourier (iteratedDeriv m u) k‖ ≤ ‖v‖ := by
    rw [circleFourier_eq_periodic_lift hper]
    apply fourierCoeff_norm_le_bound
    intro x
    change ‖v x‖ ≤ ‖v‖
    exact v.norm_coe_le_norm x
  rw [circleFourier_norm_iteratedDeriv hu hp hk m]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end Yau.Blueprint.V03Proof
