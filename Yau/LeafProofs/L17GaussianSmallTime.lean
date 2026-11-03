import Yau.LeafProofs.L17GaussianInverseCorrection

/-! One spatial scale and one parabolic time scale work for both fixed Holder exponents. -/

open Set Metric Filter
open scoped Topology
noncomputable section
namespace Yau.LeafProofs.L17Aux

theorem exists_common_gaussian_small_scales (E1 E2 : ℝ) :
    ∃ ε S : ℝ, 0 < ε ∧ 0 < S ∧ S ≤ 1 ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ε →
      E1*(ρ+S^(1/2 : ℝ)+S^(1/4 : ℝ)) < 1/4 ∧
      E2*(ρ+S^(1/2 : ℝ)+S^(3/8 : ℝ)) < 1/4 := by
  let B := max (1 : ℝ) (max E1 E2)
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hE1 : E1 ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hE2 : E2 ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hc : Continuous (fun s : ℝ => B*(s^(1/2 : ℝ)+s^(1/4 : ℝ))) :=
    continuous_const.mul ((Real.continuous_rpow_const (by norm_num)).add (Real.continuous_rpow_const (by norm_num)))
  have hz : B*((0 : ℝ)^(1/2 : ℝ)+0^(1/4 : ℝ)) < 1/8 := by norm_num
  have hNear : ∀ᶠ s in 𝓝 (0 : ℝ), B*(s^(1/2 : ℝ)+s^(1/4 : ℝ)) < 1/8 :=
    hc.continuousAt.eventually (isOpen_Iio.mem_nhds hz)
  obtain ⟨δ,hδ,hδBound⟩ := Metric.mem_nhds_iff.mp hNear
  let S := min (δ/2) (1/2 : ℝ)
  have hS : 0 < S := lt_min (by positivity) (by norm_num)
  have hSone : S ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hSδ : S < δ := (min_le_left _ _).trans_lt (by linarith)
  have hSball : S ∈ ball (0 : ℝ) δ := by
    rw [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hS]
    exact hSδ
  have hSmall : B*(S^(1/2 : ℝ)+S^(1/4 : ℝ)) < 1/8 := hδBound hSball
  refine ⟨(1/8 : ℝ)/B,S,div_pos (by norm_num) hB,hS,hSone,?_⟩
  intro ρ hρ hρε
  have hρB : B*ρ < 1/8 := by
    simpa only [mul_comm] using (lt_div_iff₀ hB).mp hρε
  have hPow : S^(3/8 : ℝ) ≤ S^(1/4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hS hSone (by norm_num)
  have hSum : 0 ≤ ρ+S^(1/2 : ℝ)+S^(1/4 : ℝ) := by positivity
  have hSum2 : 0 ≤ ρ+S^(1/2 : ℝ)+S^(3/8 : ℝ) := by positivity
  constructor
  · apply (mul_le_mul_of_nonneg_right hE1 hSum).trans_lt
    nlinarith
  · calc
      _ ≤ B*(ρ+S^(1/2 : ℝ)+S^(3/8 : ℝ)) := mul_le_mul_of_nonneg_right hE2 hSum2
      _ ≤ B*(ρ+S^(1/2 : ℝ)+S^(1/4 : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hB.le
      _ < _ := by nlinarith

end Yau.LeafProofs.L17Aux
