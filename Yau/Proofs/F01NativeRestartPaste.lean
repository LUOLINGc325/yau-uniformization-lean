import Yau.Proofs.F01NormalizedRestartProfile
import Yau.Proofs.F01TimeFacePaste

/-! One explicit native pasted potential uses the original partial
potential, its constructed terminal value, and the actual restart. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def nativePastedRestartPotential (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ)
    (W : M.Carrier → ℝ → ℝ) (T : ℝ) : M.Carrier → ℝ → ℝ :=
  fun x t => if t ≤ T then nativeClosedTerminalPotential U u T x t else W x (t - T)

theorem normalized_native_restart_paste
    (A : BoundedChartFamily g) (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ)
    (W : M.Carrier → ℝ → ℝ) (a : M.Carrier) {σ : ℝ} (hσ : 0 < σ)
    (T : ℝ) (p : Point n) :
    shiftedNativePotential A (nativePastedRestartPotential U u W T) a σ T p =
      timeFacePaste
        (shiftedNativePotential A (nativeClosedTerminalPotential U u T) a σ T)
        (shiftedNativePotential A (absoluteRestartPotential W T) a σ T) 0 p := by
  have he : T + σ ^ 2 * p.2 ≤ T ↔ p.2 ≤ 0 := by
    constructor
    · intro hh
      have hs : σ ^ 2 * p.2 ≤ 0 := by linarith
      by_contra hn
      have hh := mul_pos (sq_pos_of_pos hσ) (lt_of_not_ge hn)
      linarith
    · intro hh
      have hs := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg σ) hh
      linarith
  by_cases ht : p.2 ≤ 0
  · change (σ ^ 2)⁻¹ *
      (if T + σ ^ 2 * p.2 ≤ T then
        nativeClosedTerminalPotential U u T (A.chart a (σ • p.1 + 0)) (T + σ ^ 2 * p.2)
       else W (A.chart a (σ • p.1 + 0)) (T + σ ^ 2 * p.2 - T)) = _
    rw [if_pos (he.mpr ht)]
    simp only [timeFacePaste, if_pos ht, shiftedNativePotential, affineParabolicPotential,
      affineParabolicPullback, affineParabolicPoint]
  · change (σ ^ 2)⁻¹ *
      (if T + σ ^ 2 * p.2 ≤ T then
        nativeClosedTerminalPotential U u T (A.chart a (σ • p.1 + 0)) (T + σ ^ 2 * p.2)
       else W (A.chart a (σ • p.1 + 0)) (T + σ ^ 2 * p.2 - T)) = _
    rw [if_neg (fun hh => ht (he.mp hh))]
    simp only [timeFacePaste, if_neg ht, shiftedNativePotential, affineParabolicPotential,
      affineParabolicPullback, affineParabolicPoint, absoluteRestartPotential]

end Yau.NodeProofs.F01Aux
