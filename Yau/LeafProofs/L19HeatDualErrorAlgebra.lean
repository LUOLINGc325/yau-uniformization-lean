import Yau.LeafProofs.L19HeatDualCutoffs

/-! Scalar algebra for the decaying actual heat-duality boundary error. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- Enlarging the true annulus increases the actual squared scalar integral. -/
theorem integral_sq_annulus_le_expanded (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) {R : ℝ} (hR : 0 ≤ R)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) :
    (∫ x in {x | R ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 2 * R}, f x ^ 2 ∂μ) ≤
      ∫ x in {x | R / 2 ≤ inducedDistance g.form o x ∧ inducedDistance g.form o x ≤ 4 * R}, f x ^ 2 ∂μ := by
  apply setIntegral_mono_set
    (smoothFn_integrableOn_compact g μ hμ (smoothFn_pow hf 2)
      (scalarHeat_annulus_isCompact g o (R / 2) (4 * R)))
    (ae_of_all _ fun x => sq_nonneg (f x))
  exact ae_of_all _ (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)

/-- Exponential Young balancing turns scalar growth and gradient decay
into one strictly decaying Gaussian boundary error. -/
theorem balanced_gaussian_four_energy_bound
    {β R B U V G H U₀ V₀ G₀ H₀ : ℝ} (hβ : 0 < β) (hB : 0 ≤ B)
    (_hU₀ : 0 ≤ U₀) (hV₀ : 0 ≤ V₀) (_hG₀ : 0 ≤ G₀) (hH₀ : 0 ≤ H₀)
    (hU : U ≤ U₀ * Real.exp ((β / 16) * R ^ 2))
    (hV : V ≤ V₀ * Real.exp (-(β / 4) * R ^ 2))
    (hG : G ≤ G₀ * Real.exp ((β / 16) * R ^ 2))
    (hH : H ≤ H₀ * Real.exp (-(β / 4) * R ^ 2)) :
    let δ := Real.exp (-(β / 8) * R ^ 2)
    (1 / 2 : ℝ) * (δ * U + δ⁻¹ * V + (δ * B / 4) * G + (B / (4 * δ)) * H) ≤
      ((1 / 2 : ℝ) * (U₀ + B / 4 * G₀ + (V₀ + B / 4 * H₀))) *
        Real.exp (-(β / 16) * R ^ 2) := by
  dsimp only
  let δ := Real.exp (-(β / 8) * R ^ 2)
  have hδ : 0 < δ := Real.exp_pos _
  have hp : δ * Real.exp ((β / 16) * R ^ 2) = Real.exp (-(β / 16) * R ^ 2) := by
    dsimp only [δ]
    rw [← Real.exp_add]
    congr 1
    ring
  have hq : δ⁻¹ * Real.exp (-(β / 4) * R ^ 2) = Real.exp (-(β / 8) * R ^ 2) := by
    dsimp only [δ]
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have h₁ := mul_le_mul_of_nonneg_left hU hδ.le
  have h₂ := mul_le_mul_of_nonneg_left hV (inv_nonneg.mpr hδ.le)
  have h₃ := mul_le_mul_of_nonneg_left hG (show 0 ≤ δ * B / 4 by positivity)
  have h₄ := mul_le_mul_of_nonneg_left hH (show 0 ≤ B / (4 * δ) by positivity)
  have he : (1 / 2 : ℝ) *
      (δ * (U₀ * Real.exp ((β / 16) * R ^ 2)) +
        δ⁻¹ * (V₀ * Real.exp (-(β / 4) * R ^ 2)) +
        (δ * B / 4) * (G₀ * Real.exp ((β / 16) * R ^ 2)) +
        (B / (4 * δ)) * (H₀ * Real.exp (-(β / 4) * R ^ 2))) =
      (1 / 2 : ℝ) * ((U₀ + B / 4 * G₀) * (δ * Real.exp ((β / 16) * R ^ 2)) +
        (V₀ + B / 4 * H₀) * (δ⁻¹ * Real.exp (-(β / 4) * R ^ 2))) := by
    field_simp
    ring
  change (1 / 2 : ℝ) * (δ * U + δ⁻¹ * V + (δ * B / 4) * G + (B / (4 * δ)) * H) ≤ _
  calc
    _ ≤ (1 / 2 : ℝ) *
        (δ * (U₀ * Real.exp ((β / 16) * R ^ 2)) +
          δ⁻¹ * (V₀ * Real.exp (-(β / 4) * R ^ 2)) +
          (δ * B / 4) * (G₀ * Real.exp ((β / 16) * R ^ 2)) +
          (B / (4 * δ)) * (H₀ * Real.exp (-(β / 4) * R ^ 2))) := by
      linarith only [h₁, h₂, h₃, h₄]
    _ = _ := he
    _ ≤ ((1 / 2 : ℝ) * (U₀ + B / 4 * G₀ + (V₀ + B / 4 * H₀))) *
        Real.exp (-(β / 16) * R ^ 2) := by
      rw [hp, hq]
      have hExp : Real.exp (-(β / 8) * R ^ 2) ≤ Real.exp (-(β / 16) * R ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hβ.le (sq_nonneg R)]
      have hh := mul_le_mul_of_nonneg_left hExp (show 0 ≤ V₀ + B / 4 * H₀ by positivity)
      nlinarith only [hh]

end Yau.LeafProofs.L19Aux
