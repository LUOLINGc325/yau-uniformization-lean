import Yau.Blueprint.ParabolicSpaces
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Actual spatial and within-time derivatives under positive parabolic rescaling. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open Set Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic

variable {n : ℕ}

def parabolicUnscale (ρ : ℝ) (u : Point n → ℝ) (p : Point n) : ℝ :=
  ρ ^ 2 * u (ρ⁻¹ • p.1, (ρ ^ 2)⁻¹ * p.2)

theorem spatialD_parabolicUnscale {ρ : ℝ} (hρ : ρ ≠ 0) (u : Point n → ℝ) (p : Point n) :
    spatialD (parabolicUnscale ρ u) p =
      ρ • spatialD u (ρ⁻¹ • p.1, (ρ ^ 2)⁻¹ * p.2) := by
  change fderiv ℝ ((ρ ^ 2) • (fun x : Space n =>
    (fun y => u (y, (ρ ^ 2)⁻¹ * p.2)) (ρ⁻¹ • x))) p.1 = _
  rw [fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (ρ ^ 2), Pi.smul_apply]
  have hder := fderiv_comp_smul (𝕜 := ℝ)
    (f := fun y : Space n => u (y, (ρ ^ 2)⁻¹ * p.2)) (x := p.1) ρ⁻¹
  rw [hder, smul_smul]
  have hscalar : ρ ^ 2 * ρ⁻¹ = ρ := by field_simp
  rw [hscalar]
  rfl

theorem spatialDD_parabolicUnscale {ρ : ℝ} (hρ : ρ ≠ 0) (u : Point n → ℝ) (p : Point n) :
    spatialDD (parabolicUnscale ρ u) p =
      spatialDD u (ρ⁻¹ • p.1, (ρ ^ 2)⁻¹ * p.2) := by
  have hfun : (fun x : Space n => spatialD (parabolicUnscale ρ u) (x, p.2)) =
      (fun x => ρ • spatialD u (ρ⁻¹ • x, (ρ ^ 2)⁻¹ * p.2)) :=
    funext (fun x => spatialD_parabolicUnscale hρ u (x, p.2))
  change fderiv ℝ (fun x : Space n => spatialD (parabolicUnscale ρ u) (x, p.2)) p.1 = _
  rw [hfun]
  change fderiv ℝ (ρ • (fun x : Space n =>
    spatialD u (ρ⁻¹ • x, (ρ ^ 2)⁻¹ * p.2))) p.1 = _
  rw [fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ)
    (f := fun x : Space n => spatialD u (ρ⁻¹ • x, (ρ ^ 2)⁻¹ * p.2)) ρ, Pi.smul_apply]
  have hder := fderiv_comp_smul (𝕜 := ℝ)
    (f := fun y : Space n => spatialD u (y, (ρ ^ 2)⁻¹ * p.2)) (x := p.1) ρ⁻¹
  rw [hder, smul_smul, mul_inv_cancel₀ hρ, one_smul]
  rfl

theorem parabolic_timeScale_mem_Icc {ρ T t : ℝ} (hρ : ρ ≠ 0) (ht : t ∈ Icc 0 T) :
    (ρ ^ 2)⁻¹ * t ∈ Icc (0 : ℝ) (T / ρ ^ 2) := by
  have hsq : 0 < ρ ^ 2 := sq_pos_of_ne_zero hρ
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hsq.le) ht.1
  · rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left ht.2 (inv_nonneg.mpr hsq.le)

theorem parabolicUnscale_hasDerivWithinAt {ρ T t b : ℝ}
    (hρ : ρ ≠ 0) (u : Point n → ℝ) (x : Space n)
    (hu : HasDerivWithinAt (fun tau => u (ρ⁻¹ • x, tau)) b
      (Icc (0 : ℝ) (T / ρ ^ 2)) ((ρ ^ 2)⁻¹ * t)) :
    HasDerivWithinAt (fun tau => parabolicUnscale ρ u (x, tau)) b (Icc (0 : ℝ) T) t := by
  have harg : HasDerivWithinAt (fun tau : ℝ => (ρ ^ 2)⁻¹ * tau) (ρ ^ 2)⁻¹ (Icc 0 T) t :=
    by simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul (ρ ^ 2)⁻¹).hasDerivWithinAt
  have hmap : MapsTo (fun tau : ℝ => (ρ ^ 2)⁻¹ * tau) (Icc 0 T) (Icc 0 (T / ρ ^ 2)) :=
    fun _ ht => parabolic_timeScale_mem_Icc hρ ht
  have h := (hu.comp t harg hmap).const_mul (ρ ^ 2)
  convert h using 1
  · rfl
  · field_simp

end Yau.LeafProofs.L17Aux
