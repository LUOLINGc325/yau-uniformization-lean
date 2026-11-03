import Yau.Proofs.F01ShiftedNativePotential
import Yau.Proofs.F01NormalizedBackgroundRegularity

/-! Fixed secondary parabolic normalization acts on the same native
potential and background. The endpoint clock remains unchanged and the
inverse-square amplitude is retained exactly. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem affinePotential_shifted_scale (A : BoundedChartFamily g)
    (U : M.Carrier → ℝ → ℝ) (a : M.Carrier) (ρ τ κ : ℝ) :
    affineParabolicPotential κ 0 0 (shiftedNativePotential A U a ρ τ) =
      shiftedNativePotential A U a (ρ * κ) τ := by
  funext p
  simp only [shiftedNativePotential, affineParabolicPotential, affineParabolicPullback,
    affineParabolicPoint, add_zero, zero_add, smul_smul, mul_pow, mul_inv_rev, mul_assoc]

theorem shifted_background_scale (A : BoundedChartFamily g) (a : M.Carrier) (ρ τ κ : ℝ) :
    (fun p => shiftedComplexBackground A a ρ τ (affineParabolicPoint κ 0 0 p)) =
      shiftedComplexBackground A a (ρ * κ) τ := by
  funext p
  simp only [shiftedComplexBackground, affineParabolicPoint, add_zero, zero_add,
    smul_smul, mul_pow, mul_assoc]

theorem shifted_source_scale (A : BoundedChartFamily g) (a : M.Carrier) (ρ κ : ℝ) :
    (fun z => normalizedPotentialLogSource A a ρ (κ • z)) = normalizedPotentialLogSource A a (ρ * κ) := by
  funext z
  simp only [normalizedPotentialLogSource, smul_smul]

theorem shifted_native_quarter_schauder
    (A : BoundedChartFamily g) (U : M.Carrier → ℝ → ℝ) (a : M.Carrier) (ρ τ : ℝ)
    {β C : ℝ} (hβ : 0 ≤ β)
    (hu : SchauderBound β (cylinder (ball 0 (1 / 2)) (-(1 / 8)) 0)
      (shiftedNativePotential A U a ρ τ) C) :
    SchauderBound β (cylinder (ball 0 1) (-1) 0)
      (shiftedNativePotential A U a (ρ * (1 / 4)) τ) (16 * C) := by
  have hSpace : MapsTo (fun z : Space n => (1 / 4 : ℝ) • z + 0) (ball 0 1) (ball 0 (1 / 2)) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
    simpa only [mem_ball, dist_zero_right, add_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)] using
      (show (1 / 4 : ℝ) * ‖z‖ < 1 / 2 by linarith)
  have hClock : MapsTo (fun t : ℝ => 0 + (1 / 4 : ℝ) ^ 2 * t) (Icc (-1) 0) (Icc (-(1 / 8)) 0) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hh := schauderBound_affineParabolicPotential (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : |(1 / 4 : ℝ)| ≤ 1) hβ hSpace hClock hu
  rw [affinePotential_shifted_scale] at hh
  simpa only [show |(((1 / 4 : ℝ) ^ 2)⁻¹)| = 16 by norm_num] using hh

end Yau.NodeProofs.F01Aux
