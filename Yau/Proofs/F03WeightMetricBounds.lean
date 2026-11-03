import Yau.Proofs.F03MetricDefectAbsorption
import Yau.Proofs.F03WeightParameters

/-! The compact error in the actual weight Hessian is bounded by the initial metric. -/
noncomputable section
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ}

theorem hermLE_coefficient_mono (G : Matrix (Fin n) (Fin n) ℂ)
    (hG : G.PosSemidef) {a b : ℝ} (hab : a ≤ b) :
    HermLE (Complex.ofReal a • G) (Complex.ofReal b • G) := by
  unfold HermLE
  simpa only [Complex.ofReal_sub,sub_smul] using
    hG.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hab))

theorem metric_defect_coarse_bound
    (G H B : Matrix (Fin n) (Fin n) ℂ)
    (hG : G.PosSemidef) (hDef : (G-H).PosSemidef)
    (A E χ u : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) (hχ : 0 ≤ χ) (hu : 1 ≤ u)
    (hB : HermLE B (Complex.ofReal (χ/u^2) •
      (Complex.ofReal (-A) • (G-H)+Complex.ofReal E • G))) :
    HermLE B (Complex.ofReal (E*χ) • G) := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hu2 : 0 < u^2 := sq_pos_of_pos hu0
  have hu2one : 1 ≤ u^2 := by nlinarith
  have hα : 0 ≤ χ/u^2 := div_nonneg hχ hu2.le
  have hαχ : χ/u^2 ≤ χ := by
    apply (div_le_iff₀ hu2).mpr
    nlinarith [mul_nonneg hχ (sub_nonneg.mpr hu2one)]
  have hDefCoeff : 0 ≤ (χ/u^2)*A := mul_nonneg hα hA
  have hGCoeff : 0 ≤ E*χ-(χ/u^2)*E := by
    have hh := mul_le_mul_of_nonneg_left hαχ hE
    nlinarith
  have hPositive := (hDef.smul (Complex.zero_le_real.mpr hDefCoeff)).add
    (hG.smul (Complex.zero_le_real.mpr hGCoeff))
  unfold HermLE at hB ⊢
  convert hPositive.add hB using 1
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_neg]
  ring

end Yau.Proofs.F03Aux
