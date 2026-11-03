import Yau.Proofs.F01SchauderScalarMultiplication
import Yau.Proofs.F01ClosedBackwardRestriction
import Yau.Proofs.F01ParabolicDilation

/-! Exact half-cylinder rescaling for the literal original initial
Schauder conclusion. The normalized potential has amplitude four,
which is retained in the resulting numerical budget. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem half_initial_cylinder_schauder {β C : ℝ} {u : Point n → ℝ}
    (hβ : 0 ≤ β)
    (hu : SchauderBound β (cylinder (ball 0 (1/2)) (-(1/4)) (1/4)) u C) :
    SchauderBound β (cylinder (ball 0 1) (-1) 1)
      (fun p => 4 * u (parabolicDilation (1/2) p)) (4 * C) := by
  have hSpace : MapsTo (fun x : Space n => (1/2 : ℝ) • x + 0) (ball 0 1) (ball 0 (1/2)) := by
    intro x hx
    simpa only [add_zero] using spatialDilation_mem_ball
      (by norm_num : (0 : ℝ) < 1/2) (le_refl (1/2 : ℝ)) hx
  have hClock : MapsTo (fun t : ℝ => 0 + (1/2 : ℝ) ^ 2 * t)
      (Icc (-1) 1) (Icc (-(1/4)) (1/4)) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hpull := schauderBound_affineParabolicPullback (by norm_num : (-1 : ℝ) < 1)
    (by norm_num : |(1/2 : ℝ)| ≤ 1) hβ hSpace hClock hu
  have hscale := schauderBound_real_mul hpull 4
  simpa only [affineParabolicPullback, affineParabolicPoint, parabolicDilation,
    add_zero, zero_add, abs_of_pos (by norm_num : (0 : ℝ) < 4)] using hscale

theorem parabolicRescalePotential_half_scale {ρ : ℝ} (hρ : ρ ≠ 0)
    (F : Point n → ℝ) (p : Point n) :
    parabolicRescalePotential ρ F p =
      4 * parabolicRescalePotential (2 * ρ) F (parabolicDilation (1/2) p) := by
  have hPoint : parabolicDilation (2 * ρ) (parabolicDilation (1/2) p) =
      parabolicDilation ρ p := by
    apply Prod.ext
    · simp only [parabolicDilation, smul_smul]
      congr 1
      ring
    · simp only [parabolicDilation]
      ring
  have hScalar : (ρ ^ 2)⁻¹ = 4 * ((2 * ρ) ^ 2)⁻¹ := by field_simp; ring
  change (ρ ^ 2)⁻¹ * F (parabolicDilation ρ p) =
    4 * (((2 * ρ) ^ 2)⁻¹ * F (parabolicDilation (2 * ρ) (parabolicDilation (1/2) p)))
  rw [hPoint, hScalar]
  ring

theorem forwardZero_normalized_half_scale {ρ : ℝ} (hρ : ρ ≠ 0)
    (F : Point n → ℝ) (p : Point n) :
    forwardZeroSpaceTime (parabolicRescalePotential ρ F) p =
      4 * forwardZeroSpaceTime (parabolicRescalePotential (2 * ρ) F)
        (parabolicDilation (1/2) p) := by
  by_cases ht : p.2 ≤ 0
  · have hsmall : (parabolicDilation (1/2) p).2 ≤ 0 := by
      change (1/2 : ℝ) ^ 2 * p.2 ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) ht
    simp only [forwardZeroSpaceTime, forwardZeroExtension, if_pos ht, if_pos hsmall, mul_zero]
  · have hsmall : ¬(parabolicDilation (1/2) p).2 ≤ 0 := by
      change ¬(1/2 : ℝ) ^ 2 * p.2 ≤ 0
      nlinarith
    simp only [forwardZeroSpaceTime, forwardZeroExtension, if_neg ht, if_neg hsmall]
    exact parabolicRescalePotential_half_scale hρ F p

theorem normalized_initial_half_scale_schauder {ρ β C : ℝ} (hρ : ρ ≠ 0)
    (F : Point n → ℝ) (hβ : 0 ≤ β)
    (hu : SchauderBound β (cylinder (ball 0 (1/2)) (-(1/4)) (1/4))
      (forwardZeroSpaceTime (parabolicRescalePotential (2 * ρ) F)) C) :
    SchauderBound β (cylinder (ball 0 1) (-1) 1)
      (forwardZeroSpaceTime (parabolicRescalePotential ρ F)) (4 * C) := by
  have hb := half_initial_cylinder_schauder hβ hu
  have he : (fun p => 4 * forwardZeroSpaceTime (parabolicRescalePotential (2 * ρ) F)
      (parabolicDilation (1/2) p)) = forwardZeroSpaceTime (parabolicRescalePotential ρ F) :=
    funext (fun p => (forwardZero_normalized_half_scale hρ F p).symm)
  rw [he] at hb
  exact hb

end Yau.NodeProofs.F01Aux
