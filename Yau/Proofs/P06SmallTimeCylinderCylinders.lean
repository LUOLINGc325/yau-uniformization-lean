import Yau.Proofs.P06SmallTimeCylinderJointEstimate
import Mathlib.MeasureTheory.Integral.Prod

/-! Literal fixed inner and outer cylinders and their finite local energy.
The interval length is retained until the final norm estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.SmallTimeCylinder
open Yau.Parabolic Yau.LeafProofs.L16Aux CylinderReg
variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

theorem timeScale_image_Ioo (O : Set (Space n)) (a b τ : ℝ) (hτ : 0 < τ) :
    timeScale τ hτ.ne' '' (O ×ˢ Set.Ioo a b) = O ×ˢ Set.Ioo (τ * a) (τ * b) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq.1, mul_lt_mul_of_pos_left hq.2.1 hτ, mul_lt_mul_of_pos_left hq.2.2 hτ⟩
  · intro hp
    refine ⟨(timeScale τ hτ.ne').symm p, ?_, (timeScale τ hτ.ne').apply_symm_apply p⟩
    change p.1 ∈ O ∧ p.2 / τ ∈ Set.Ioo a b
    exact ⟨hp.1, (lt_div_iff₀ hτ).mpr (by nlinarith [hp.2.1]),
      (div_lt_iff₀ hτ).mpr (by nlinarith [hp.2.2])⟩

theorem timeScale_outer_cylinder (O : Set (Space n)) (τ : ℝ) (hτ : 0 < τ) :
    timeScale τ hτ.ne' '' (O ×ˢ Set.Ioo (1 / 4 : ℝ) 2) =
      O ×ˢ Set.Ioo (τ / 4) (2 * τ) := by
  have hl : τ * (1 / 4 : ℝ) = τ / 4 := by ring
  have hu : τ * 2 = 2 * τ := by ring
  simpa only [hl, hu] using timeScale_image_Ioo O (1 / 4) 2 τ hτ

theorem mem_timeScale_inner_cylinder (K : Set (Space n))
    (τ : ℝ) (hτ : 0 < τ) {p : Point n}
    (hp : p ∈ K ×ˢ Set.Icc (τ / 2) (3 * τ / 2)) :
    p ∈ timeScale τ hτ.ne' '' (K ×ˢ Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ)) := by
  refine ⟨(timeScale τ hτ.ne').symm p, ?_, (timeScale τ hτ.ne').apply_symm_apply p⟩
  change p.1 ∈ K ∧ p.2 / τ ∈ Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ)
  exact ⟨hp.1, (le_div_iff₀ hτ).mpr (by nlinarith [hp.2.1]),
    (div_le_iff₀ hτ).mpr (by nlinarith [hp.2.2])⟩

theorem outer_cylinder_subset (O : Set (Space n))
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    O ×ˢ Set.Ioo (τ / 4) (2 * τ) ⊆ O ×ˢ Set.Ioo (0 : ℝ) 2 := by
  intro p hp
  exact ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩

theorem valueSquare_integrableOn_cylinder (O : Set (Space n))
    (hO : IsCompact (closure O)) (U : Point n → α → ℝ)
    (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r)) (a b : ℝ) :
    IntegrableOn (valueSquare U) (O ×ˢ Set.Ioo a b) := by
  have hCont : Continuous (valueSquare U) := (ContDiff.sum fun r _ => (hU r).pow 2).continuous
  have hInt : IntegrableOn (valueSquare U) (closure O ×ˢ Set.Icc a b) :=
    hCont.continuousOn.integrableOn_compact (hO.prod isCompact_Icc)
  exact hInt.mono_set (Set.prod_mono subset_closure Set.Ioo_subset_Icc_self)

theorem cylinder_energy_le_of_slice_bound (O : Set (Space n))
    (hO : IsCompact (closure O)) (U : Point n → α → ℝ)
    (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r)) (τ : ℝ) (hτ : 0 < τ) (L : ℝ)
    (hL : ∀ s ∈ Set.Ioo (τ / 4) (2 * τ),
      (∫ z in O, valueSquare U (z,s)) ≤ L ^ 2) :
    (∫ p in O ×ˢ Set.Ioo (τ / 4) (2 * τ), valueSquare U p) ≤ 2 * τ * L ^ 2 := by
  have hInt := valueSquare_integrableOn_cylinder O hO U hU (τ / 4) (2 * τ)
  have hProd : Integrable (valueSquare U)
      (((volume : Measure (Space n)).restrict O).prod
        ((volume : Measure ℝ).restrict (Set.Ioo (τ / 4) (2 * τ)))) := by
    simpa only [IntegrableOn, Measure.volume_eq_prod, Measure.prod_restrict] using hInt
  have hFubini : (∫ p in O ×ˢ Set.Ioo (τ / 4) (2 * τ), valueSquare U p) =
      ∫ s in Set.Ioo (τ / 4) (2 * τ), ∫ z in O, valueSquare U (z,s) := by
    simpa only [Measure.volume_eq_prod, Measure.prod_restrict] using
      integral_prod_symm (valueSquare U) hProd
  have hConst : IntegrableOn (fun _ : ℝ => L ^ 2) (Set.Ioo (τ / 4) (2 * τ)) :=
    integrableOn_const (by simp)
  calc
    _ = ∫ s in Set.Ioo (τ / 4) (2 * τ), ∫ z in O, valueSquare U (z,s) := hFubini
    _ ≤ ∫ _ in Set.Ioo (τ / 4) (2 * τ), L ^ 2 :=
      setIntegral_mono_on hProd.integral_prod_right hConst isOpen_Ioo.measurableSet hL
    _ = (2 * τ - τ / 4) * L ^ 2 := by
      rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg L)

end Yau.NodeProofs.P06Aux.SmallTimeCylinder
