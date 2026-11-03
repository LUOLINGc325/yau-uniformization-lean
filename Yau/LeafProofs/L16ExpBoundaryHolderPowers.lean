import Yau.LeafProofs.L16DeGiorgiOscillationIteration
import Mathlib.Analysis.MeanInequalitiesPow

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryHolderAux

open Yau.Parabolic

theorem parabolicDistance_nonneg {n : ℕ} (p q : Point n) : 0 ≤ parabolicDistance p q :=
  add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem parabolicDistance_symm {n : ℕ} (p q : Point n) : parabolicDistance p q = parabolicDistance q p := by
  simp only [parabolicDistance,norm_sub_rev,abs_sub_comm]

theorem parabolicDistance_spatial_le {n : ℕ} (p q : Point n) : ‖p.1-q.1‖ ≤ parabolicDistance p q :=
  le_add_of_nonneg_right (Real.sqrt_nonneg _)

theorem parabolicDistance_sqrt_le {n : ℕ} (p q : Point n) :
    Real.sqrt |p.2-q.2| ≤ parabolicDistance p q := le_add_of_nonneg_left (norm_nonneg _)

theorem parabolicDistance_eq_zero {n : ℕ} {p q : Point n} (h : parabolicDistance p q = 0) : p = q := by
  have hx : ‖p.1-q.1‖ = 0 := by
    have hle := parabolicDistance_spatial_le p q
    rw [h] at hle
    exact le_antisymm hle (norm_nonneg _)
  have hs : Real.sqrt |p.2-q.2| = 0 := by
    have hle := parabolicDistance_sqrt_le p q
    rw [h] at hle
    exact le_antisymm hle (Real.sqrt_nonneg _)
  have ht : |p.2-q.2| = 0 := by nlinarith [Real.sq_sqrt (abs_nonneg (p.2-q.2))]
  exact Prod.ext (sub_eq_zero.mp (norm_eq_zero.mp hx)) (sub_eq_zero.mp (abs_eq_zero.mp ht))

theorem parabolicDistance_time_gap_le_sq {n : ℕ} (p q : Point n) :
    |p.2-q.2| ≤ (parabolicDistance p q)^2 := by
  have hs := parabolicDistance_sqrt_le p q
  have hn := parabolicDistance_nonneg p q
  nlinarith [Real.sq_sqrt (abs_nonneg (p.2-q.2)),Real.sqrt_nonneg |p.2-q.2|]

theorem parabolicDistance_rpow_le_holderWeight {n : ℕ} {γ : ℝ}
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (p q : Point n) :
    (parabolicDistance p q)^γ ≤ holderWeight γ p q := by
  dsimp only [parabolicDistance,holderWeight]
  calc
    _ ≤ ‖p.1-q.1‖^γ+(Real.sqrt |p.2-q.2|)^γ :=
      Real.rpow_add_le_add_rpow (norm_nonneg _) (Real.sqrt_nonneg _) hγ hγ1
    _ = _ := by rw [← Real.rpow_div_two_eq_sqrt γ (abs_nonneg _)]

theorem small_linear_le_rpow {δ γ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) : δ ≤ δ^γ := by
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' hδ hδ1 hγ hγ1

/-- The O(R) outer amplitude cancels the denominator in the interior
oscillation estimate, retaining the original exponent. -/
theorem scaled_power_times_radius_le {δ R γ : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R)
    (hR1 : R ≤ 1) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (2*δ/R)^γ*R ≤ (2 : ℝ)^γ*δ^γ := by
  have hp : 0 < R^γ := Real.rpow_pos_of_pos hR γ
  have hpow : R^(1-γ) ≤ 1 := Real.rpow_le_one hR.le hR1 (sub_nonneg.mpr hγ1)
  have hEq : (2*δ/R)^γ*R = ((2 : ℝ)^γ*δ^γ)*R^(1-γ) := by
    rw [Real.div_rpow (by positivity) hR.le,Real.mul_rpow (by norm_num) hδ,
      Real.rpow_sub hR,Real.rpow_one]
    ring
  rw [hEq]
  exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans_eq (mul_one _)

theorem interior_amplitude_power_bound {δ R γ C H F : ℝ}
    (hδ : 0 ≤ δ) (hR : 0 < R) (hR1 : R ≤ 1) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    C*(2*δ/R)^γ*(2*H*R+F*R^2) ≤ C*(2 : ℝ)^γ*(2*H+F)*δ^γ := by
  have hAmp : 2*H*R+F*R^2 ≤ (2*H+F)*R := by
    nlinarith [mul_le_mul_of_nonneg_left hR1 (mul_nonneg hF hR.le)]
  calc
    _ ≤ C*(2*δ/R)^γ*((2*H+F)*R) := mul_le_mul_of_nonneg_left hAmp (by positivity)
    _ = (C*(2*H+F))*((2*δ/R)^γ*R) := by ring
    _ ≤ (C*(2*H+F))*((2 : ℝ)^γ*δ^γ) :=
      mul_le_mul_of_nonneg_left (scaled_power_times_radius_le hδ hR hR1 hγ hγ1) (by positivity)
    _ = _ := by ring

end Yau.LeafProofs.L16ExpBoundaryHolderAux
