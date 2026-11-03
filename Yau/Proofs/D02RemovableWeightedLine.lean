import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory Filter Set
open scoped Topology

noncomputable section
namespace Yau.NodeProofs.D02RemovableAux

/-- The complementary power in the radial Cauchy--Schwarz argument is
integrable exactly when the extra exponent is positive. -/
theorem radial_complement_integrable {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) :
    IntegrableOn (fun r : ℝ ↦ r ^ (σ - 1)) (Ioo 0 ρ) volume := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hρ]
  linarith

/-- Finite weighted radial energy gives actual finite radial length.
Young's inequality is the pointwise form of the same weighted L² estimate;
no radial limit or distance bound is an input. -/
theorem sqrt_integrable_of_weighted_energy {q : ℝ → ℝ} {ρ σ : ℝ}
    (hρ : 0 < ρ) (hσ : 0 < σ) (hq : AEStronglyMeasurable q (volume.restrict (Ioo 0 ρ)))
    (hq0 : ∀ᵐ r ∂volume.restrict (Ioo 0 ρ), 0 ≤ q r)
    (henergy : IntegrableOn (fun r ↦ q r * r ^ (1 - σ)) (Ioo 0 ρ) volume) :
    IntegrableOn (fun r ↦ Real.sqrt (q r)) (Ioo 0 ρ) volume := by
  have hpow := radial_complement_integrable hρ hσ
  have hdom := (henergy.add hpow).div_const 2
  apply hdom.mono' (Real.continuous_sqrt.comp_aestronglyMeasurable hq)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hq0] with r hr hqr
  let A := q r * r ^ (1 - σ)
  let B := r ^ (σ - 1)
  have hA : 0 ≤ A := mul_nonneg hqr (Real.rpow_nonneg hr.1.le _)
  have hB : 0 ≤ B := Real.rpow_nonneg hr.1.le _
  have hprod : A * B = q r := by
    dsimp [A, B]
    rw [mul_assoc, ← Real.rpow_add hr.1]
    simp
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  change Real.sqrt (q r) ≤ (A + B) / 2
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (A - B)]

end Yau.NodeProofs.D02RemovableAux
