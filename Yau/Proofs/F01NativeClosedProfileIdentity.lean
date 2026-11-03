import Yau.Proofs.F01NativeClosedTerminalSlices

/-! Exact old-profile and terminal-profile identities for the explicitly
closed native potential. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem native_closed_profile_eq_on_negative_clock
    (A : BoundedChartFamily g) (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ)
    (a : M.Carrier) {σ : ℝ} (hσ : 0 < σ) (T : ℝ) {p : Point n} (ht : p.2 < 0) :
    shiftedNativePotential A (nativeClosedTerminalPotential U u T) a σ T p =
      shiftedNativePotential A U a σ T p := by
  have he : T + σ ^ 2 * p.2 ≠ T := by
    have hh := mul_neg_of_pos_of_neg (sq_pos_of_pos hσ) ht
    linarith
  change (σ ^ 2)⁻¹ * (if T + σ ^ 2 * p.2 = T then u (A.chart a (σ • p.1 + 0))
    else U (A.chart a (σ • p.1 + 0)) (T + σ ^ 2 * p.2)) =
    (σ ^ 2)⁻¹ * U (A.chart a (σ • p.1 + 0)) (T + σ ^ 2 * p.2)
  rw [if_neg he]

theorem native_closed_profile_at_zero
    (A : BoundedChartFamily g) (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ)
    (a : M.Carrier) (σ T : ℝ) (z : Space n) :
    shiftedNativePotential A (nativeClosedTerminalPotential U u T) a σ T (z, 0) =
      (σ ^ 2)⁻¹ * u (A.chart a (σ • z)) := by
  simp only [shiftedNativePotential, affineParabolicPotential, affineParabolicPullback,
    affineParabolicPoint, nativeClosedTerminalPotential, mul_zero, add_zero, ite_true]

end Yau.NodeProofs.F01Aux
