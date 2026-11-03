import Yau.Blueprint.Analytic

/-! The negative initial-metric defect absorbs the actual error in the comparison-weight Hessian. -/
noncomputable section
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ}

theorem metric_defect_absorption
    (G H B : Matrix (Fin n) (Fin n) ℂ)
    (hG : G.PosSemidef) (hH : H.PosSemidef)
    (A E χ u : ℝ) (hA : 0 ≤ A) (hEA : E ≤ A) (hχ : 0 ≤ χ) (hu : 1 ≤ u)
    (hB : HermLE B (((χ/u^2 : ℝ) : ℂ) •
      (((-A : ℝ) : ℂ) • (G-H)+(E : ℂ) • G))) :
    HermLE B (((A*χ : ℝ) : ℂ) • H) := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hu2 : 0 < u^2 := sq_pos_of_pos hu0
  have hu2one : 1 ≤ u^2 := by nlinarith
  have hα : 0 ≤ χ/u^2 := div_nonneg hχ hu2.le
  have hαχ : χ/u^2 ≤ χ := by
    apply (div_le_iff₀ hu2).mpr
    nlinarith [mul_nonneg hχ (sub_nonneg.mpr hu2one)]
  have hGcoeff : 0 ≤ (χ/u^2)*(A-E) := mul_nonneg hα (sub_nonneg.mpr hEA)
  have hHcoeff : 0 ≤ A*χ-(χ/u^2)*A := by
    have hh := mul_le_mul_of_nonneg_left hαχ hA
    nlinarith
  have hPositive := (hG.smul (Complex.zero_le_real.mpr hGcoeff)).add
    (hH.smul (Complex.zero_le_real.mpr hHcoeff))
  unfold HermLE at hB ⊢
  have hTotal := hPositive.add hB
  convert hTotal using 1
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_neg]
  ring

end Yau.Proofs.F03Aux
