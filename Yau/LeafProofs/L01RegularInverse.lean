import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Set Filter Asymptotics
open scoped Topology InnerProductSpace

namespace Yau.LeafProofs.L01Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative at one point of a firm map is itself firm. -/
theorem firm_derivative (P : E → E)
    (hfirm : ∀ y w, ‖P y - P w‖ ^ 2 ≤ ⟪P y - P w, y - w⟫_ℝ)
    (y₀ : E) (T : E →L[ℝ] E) (hT : HasFDerivAt P T y₀) (v : E) :
    ‖T v‖ ^ 2 ≤ ⟪T v, v⟫_ℝ := by
  have hlim := hT.lim_real v
  apply le_of_tendsto_of_tendsto (hlim.norm.pow 2) (hlim.inner tendsto_const_nhds)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have h := hfirm (y₀ + t⁻¹ • v) y₀
  rw [add_sub_cancel_left] at h
  calc
    ‖t • (P (y₀ + t⁻¹ • v) - P y₀)‖ ^ 2 =
        t ^ 2 * ‖P (y₀ + t⁻¹ • v) - P y₀‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow]
    _ ≤ t ^ 2 * ⟪P (y₀ + t⁻¹ • v) - P y₀, t⁻¹ • v⟫_ℝ :=
      mul_le_mul_of_nonneg_left h (sq_nonneg t)
    _ = ⟪t • (P (y₀ + t⁻¹ • v) - P y₀), v⟫_ℝ := by
      rw [inner_smul_right, real_inner_smul_left]
      field_simp

/-- Invertibility makes the firm derivative uniformly positive in every direction. -/
theorem positive_bound_of_firm_equiv (T : E ≃L[ℝ] E)
    (hfirm : ∀ v, ‖T v‖ ^ 2 ≤ ⟪T v, v⟫_ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪T v, v⟫_ℝ := by
  let b : ℝ := 1 + ‖(T.symm : E →L[ℝ] E)‖
  have hb : 0 < b := by dsimp [b]; positivity
  let c := b⁻¹
  have hc : 0 < c := inv_pos.mpr hb
  refine ⟨c, hc, fun v => ?_⟩
  have hv : ‖v‖ ≤ b * ‖T v‖ := by
    have h := (T.symm : E →L[ℝ] E).le_opNorm (T v)
    change ‖T.symm (T v)‖ ≤ ‖(T.symm : E →L[ℝ] E)‖ * ‖T v‖ at h
    rw [T.symm_apply_apply] at h
    dsimp [b]
    nlinarith [norm_nonneg (T v)]
  have hl : c * ‖v‖ ≤ ‖T v‖ := by
    have h := mul_le_mul_of_nonneg_left hv hc.le
    simpa only [c, ← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul] using h
  have hs : c ^ 2 * ‖v‖ ^ 2 ≤ ‖T v‖ ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hl)
      (add_nonneg (norm_nonneg (T v)) (mul_nonneg hc.le (norm_nonneg v)))
    nlinarith only [hprod]
  exact hs.trans (hfirm v)

/-- One derivative and its positive lower bound give a radial estimate on a closed ball. -/
theorem exists_local_radial_bound (P : E → E) (y₀ : E) (T : E →L[ℝ] E)
    (hT : HasFDerivAt P T y₀) {c : ℝ} (hc : 0 < c)
    (hpos : ∀ v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪T v, v⟫_ℝ) :
    ∃ a ρ : ℝ, 0 < a ∧ 0 < ρ ∧
      ∀ u, ‖u‖ ≤ ρ → a * ‖u‖ ^ 2 ≤ ⟪P (y₀ + u) - P y₀, u⟫_ℝ := by
  let a := c ^ 2 / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have herr := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hT).bound ha
  obtain ⟨R, hR, herror⟩ := Metric.eventually_nhds_iff.mp herr
  refine ⟨a, R / 2, ha, half_pos hR, ?_⟩
  intro u hu
  have he : ‖P (y₀ + u) - P y₀ - T u‖ ≤ a * ‖u‖ :=
    herror (by simpa only [dist_zero_right] using hu.trans_lt (half_lt_self hR))
  have hinner := neg_le_of_abs_le
    (abs_real_inner_le_norm (P (y₀ + u) - P y₀ - T u) u)
  have hmul := mul_le_mul_of_nonneg_right he (norm_nonneg u)
  have hp := hpos u
  simp only [inner_sub_left] at hinner
  simp only [inner_sub_left]
  dsimp [a] at *
  nlinarith

/-- Monotonicity propagates a local radial bound to every inverse fiber. -/
theorem preimage_norm_le_of_local_radial_bound (P : E → E) (y₀ : E)
    (hmono : ∀ y w, 0 ≤ ⟪P y - P w, y - w⟫_ℝ)
    {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ)
    (hlocal : ∀ u, ‖u‖ ≤ ρ → a * ‖u‖ ^ 2 ≤ ⟪P (y₀ + u) - P y₀, u⟫_ℝ) :
    ∀ q, ‖P q - P y₀‖ < a * ρ → ‖q - y₀‖ ≤ a⁻¹ * ‖P q - P y₀‖ := by
  intro q hnear
  let h := q - y₀
  have hsmall : ‖h‖ ≤ ρ := by
    by_contra hlarge
    have hn : 0 < ‖h‖ := hρ.trans (lt_of_not_ge hlarge)
    let t := ρ / ‖h‖
    have ht : 0 < t := div_pos hρ hn
    have ht₁ : t < 1 := (div_lt_one hn).mpr (lt_of_not_ge hlarge)
    have htn : t * ‖h‖ = ρ := div_mul_cancel₀ _ hn.ne'
    let u := t • h
    have hnormu : ‖u‖ = ρ := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, htn]
    have hloc := hlocal u (by rw [hnormu])
    have hradial : a * ρ * ‖h‖ ≤ ⟪P (y₀ + u) - P y₀, h⟫_ℝ := by
      rw [hnormu] at hloc
      change a * ρ ^ 2 ≤ ⟪P (y₀ + u) - P y₀, t • h⟫_ℝ at hloc
      rw [inner_smul_right] at hloc
      have hmul := mul_le_mul_of_nonneg_right hloc hn.le
      have heq : (t * ⟪P (y₀ + u) - P y₀, h⟫_ℝ) * ‖h‖ =
          ρ * ⟪P (y₀ + u) - P y₀, h⟫_ℝ := by rw [mul_right_comm, htn]
      rw [heq] at hmul
      apply (mul_le_mul_iff_right₀ hρ).mp
      nlinarith only [hmul]
    have hsegment : q - (y₀ + u) = (1 - t) • h := by
      dsimp [u, h]
      module
    have hm := hmono q (y₀ + u)
    rw [hsegment, inner_smul_right] at hm
    have hm' : 0 ≤ ⟪P q - P (y₀ + u), h⟫_ℝ :=
      (mul_nonneg_iff_of_pos_left (sub_pos.mpr ht₁)).mp hm
    have htotal : a * ρ * ‖h‖ ≤ ⟪P q - P y₀, h⟫_ℝ := by
      simp only [inner_sub_left] at hm' hradial ⊢
      linarith
    have hupper := real_inner_le_norm (P q - P y₀) h
    have hfar : a * ρ ≤ ‖P q - P y₀‖ :=
      (mul_le_mul_iff_left₀ hn).mp (htotal.trans hupper)
    exact hnear.not_ge hfar
  have hloc := hlocal h hsmall
  have heq : y₀ + h = q := by dsimp [h]; abel
  rw [heq] at hloc
  by_cases hn : ‖h‖ = 0
  · change ‖h‖ ≤ _
    rw [hn]
    positivity
  · have hnpos : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg h) (Ne.symm hn)
    have hupper := real_inner_le_norm (P q - P y₀) h
    have hbound : a * ‖h‖ ≤ ‖P q - P y₀‖ := by
      apply (mul_le_mul_iff_left₀ hnpos).mp
      nlinarith only [hloc, hupper]
    change ‖h‖ ≤ _
    have hb := (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hbound)
    simpa only [div_eq_mul_inv, mul_comm] using hb

/-- A firm map with one invertible derivative controls all sufficiently near inverse fibers. -/
theorem preimage_norm_le_of_firm_of_hasFDerivAt_equiv
    (P : E → E)
    (hfirm : ∀ y w, ‖P y - P w‖ ^ 2 ≤ ⟪P y - P w, y - w⟫_ℝ)
    (y₀ : E) (T : E ≃L[ℝ] E)
    (hT : HasFDerivAt P T.toContinuousLinearMap y₀) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ q, ‖P q - P y₀‖ < δ → ‖q - y₀‖ ≤ C * ‖P q - P y₀‖ := by
  obtain ⟨c, hc, hpos⟩ := positive_bound_of_firm_equiv T
    (firm_derivative P hfirm y₀ T.toContinuousLinearMap hT)
  obtain ⟨a, ρ, ha, hρ, hlocal⟩ := exists_local_radial_bound P y₀
    T.toContinuousLinearMap hT hc hpos
  refine ⟨a⁻¹, a * ρ, inv_pos.mpr ha, mul_pos ha hρ, ?_⟩
  exact preimage_norm_le_of_local_radial_bound P y₀
    (fun y w => (sq_nonneg ‖P y - P w‖).trans (hfirm y w)) ha hρ hlocal

end Yau.LeafProofs.L01Aux
