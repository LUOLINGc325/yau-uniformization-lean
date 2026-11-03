import Mathlib

noncomputable section
open MeasureTheory Filter Set

namespace Yau.NodeProofs.P02Aux

theorem energy_affine_distance_majorant (ell d E : ℝ)
    (hell : 0 < ell) (hE : d ^ 2 ≤ E) :
    d ≤ (ell ^ 2 + E) / (2 * ell) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ell)).mpr
  nlinarith [sq_nonneg (ell - d)]

theorem energy_affine_contact (ell : ℝ) (hell : 0 < ell) :
    (ell ^ 2 + ell ^ 2) / (2 * ell) = ell := by
  apply (div_eq_iff (ne_of_gt (by positivity : (0 : ℝ) < 2 * ell))).mpr
  ring

theorem terminal_curvature_integral_lower
    (B : ℝ → ℝ) (κ ell Q : ℝ)
    (hκ : 0 < κ) (hell : 2 ≤ ell) (hQ : 0 ≤ Q)
    (hB : ContinuousOn B (Icc (0 : ℝ) 1))
    (hnonneg : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ B u)
    (hterminal : ∀ u ∈ Icc (1 - 1 / ell) 1,
      κ * ell ^ 2 * Q ≤ B u) :
    κ * ell * Q / 4 ≤ ∫ u in Icc (0 : ℝ) 1, u ^ 2 * B u := by
  have hell0 : 0 < ell := by linarith
  have hinv0 : 0 < 1 / ell := one_div_pos.mpr hell0
  have hinvhalf : 1 / ell ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hell
  let a : ℝ := 1 - 1 / ell
  let c : ℝ := κ * ell ^ 2 * Q / 4
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have haHalf : (1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hsub : Icc a 1 ⊆ Icc (0 : ℝ) 1 := by
    intro u hu
    exact ⟨ha0.trans hu.1, hu.2⟩
  have hF : ContinuousOn (fun u : ℝ => u ^ 2 * B u) (Icc 0 1) :=
    (continuous_id.pow 2).continuousOn.mul hB
  have hFi : IntegrableOn (fun u : ℝ => u ^ 2 * B u) (Icc 0 1) :=
    hF.integrableOn_Icc
  have hFiSmall := hFi.mono_set hsub
  have hcInt : IntegrableOn (fun _ : ℝ => c) (Icc a 1) :=
    continuous_const.integrableOn_Icc
  have hc0 : 0 ≤ κ * ell ^ 2 * Q :=
    mul_nonneg (mul_nonneg hκ.le (sq_nonneg ell)) hQ
  have hpoint : ∀ u ∈ Icc a 1, c ≤ u ^ 2 * B u := by
    intro u hu
    have huHalf : (1 / 2 : ℝ) ≤ u := haHalf.trans hu.1
    have huSq : (1 / 4 : ℝ) ≤ u ^ 2 := by nlinarith
    calc
      c = (1 / 4 : ℝ) * (κ * ell ^ 2 * Q) := by dsimp [c]; ring
      _ ≤ u ^ 2 * (κ * ell ^ 2 * Q) := mul_le_mul_of_nonneg_right huSq hc0
      _ ≤ u ^ 2 * B u := mul_le_mul_of_nonneg_left (hterminal u hu) (sq_nonneg u)
  have hsmall : (∫ _u in Icc a 1, c) ≤ ∫ u in Icc a 1, u ^ 2 * B u :=
    setIntegral_mono_on hcInt hFiSmall measurableSet_Icc hpoint
  have hnon : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Icc 0 1)]
      (fun u : ℝ => u ^ 2 * B u) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact mul_nonneg (sq_nonneg u) (hnonneg u hu)
  have hlarge : (∫ u in Icc a 1, u ^ 2 * B u) ≤
      ∫ u in Icc (0 : ℝ) 1, u ^ 2 * B u :=
    setIntegral_mono_set hFi hnon (Eventually.of_forall fun u hu => hsub hu)
  have heval : (∫ _u in Icc a 1, c) = κ * ell * Q / 4 := by
    rw [setIntegral_const, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr ha1), smul_eq_mul]
    dsimp [a, c]
    field_simp
    <;> ring
  exact heval ▸ hsmall.trans hlarge

theorem normalized_energy_trace_bound (κ ell Q A : ℝ)
    (hκ : 0 < κ) (hell : 0 < ell) (hQ : 0 ≤ Q)
    (hlarge : 16 / κ ≤ ell) (hA : κ * ell * Q / 4 ≤ A) :
    (4 * Q - 2 * A) / (2 * ell) ≤ -κ * Q / 8 := by
  have hκell : 16 ≤ κ * ell := by
    have h := (div_le_iff₀ hκ).mp hlarge
    nlinarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ell)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hκell) hQ]

end Yau.NodeProofs.P02Aux
