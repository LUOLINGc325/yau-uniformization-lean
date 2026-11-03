import Yau.Proofs.F01ACanonicalShift
import Yau.Proofs.F01ActualGrowthShifts

/-! The majorant affects the allowed regularization parameter, while the
canonical shift keeps its inverse-linear dependence on epsilon. -/
noncomputable section

namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint Yau.Proofs.P04Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def canonicalRegularizerShiftCoefficient (c K : ℝ) : ℝ := 2 * (1 + (c * K) ^ 2)

theorem canonicalRegularizerShiftCoefficient_pos (c K : ℝ) :
    0 < canonicalRegularizerShiftCoefficient c K := by
  unfold canonicalRegularizerShiftCoefficient
  positivity

theorem canonicalGrowthShift_one_le (c K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    1 ≤ canonicalGrowthShift c K ε := by
  unfold canonicalGrowthShift
  nlinarith [sq_nonneg (c * K), inv_nonneg.mpr hε.le,
    mul_nonneg (sq_nonneg (c * K)) (inv_nonneg.mpr hε.le)]

theorem canonicalRegularizerShiftCoefficient_eq (c K ε : ℝ) :
    canonicalRegularizerShiftCoefficient c K * (1 + ε⁻¹) =
      2 * canonicalGrowthShift c K ε := by
  unfold canonicalRegularizerShiftCoefficient canonicalGrowthShift
  ring

/-- The exponential bound holds at zeros as well as at nonzero norms. -/
theorem canonical_norm_exponential_shift (g : SmoothMetric M) (S : CanonicalSection M)
    (o : M.Carrier) (u : M.Carrier → ℝ) {c K ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (hcompare : ∀ x, 1 + distFrom g.form o x ≤ K * u x)
    (hgrowth : ∀ x, Real.log (canonicalNormSq g.form S x) ≤ c * (1 + distFrom g.form o x))
    (x : M.Carrier) :
    canonicalNormSq g.form S x ≤ Real.exp (ε * u x ^ 2 + canonicalGrowthShift c K ε) := by
  by_cases hzero : canonicalNormSq g.form S x = 0
  · rw [hzero]
    exact (Real.exp_pos _).le
  · have hp : 0 < canonicalNormSq g.form S x :=
      lt_of_le_of_ne (canonicalNormSq_nonneg _ _ _) (Ne.symm hzero)
    apply (Real.log_le_iff_le_exp hp).mp
    linarith [canonicalGrowthShift_controls hc hε (hcompare x) (hgrowth x)]

theorem canonical_log_uniform_shift (g : SmoothMetric M) (S : CanonicalSection M)
    (o : M.Carrier) (u : M.Carrier → ℝ) {c K ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (hcompare : ∀ x, 1 + distFrom g.form o x ≤ K * u x)
    (hgrowth : ∀ x, Real.log (canonicalNormSq g.form S x) ≤ c * (1 + distFrom g.form o x))
    (x : M.Carrier) :
    Real.log (canonicalNormSq g.form S x) - ε * u x ^ 2 -
      canonicalRegularizerShiftCoefficient c K * (1 + ε⁻¹) ≤ 0 := by
  rw [canonicalRegularizerShiftCoefficient_eq]
  linarith [canonicalGrowthShift_controls hc hε (hcompare x) (hgrowth x),
    canonicalGrowthShift_one_le c K hε]

/-- The same canonical coefficient works for all epsilon and all sufficiently
small positive delta. Its order is epsilon inverse, including at section zeros. -/
theorem canonical_regularizer_uniform_shift
    (g : SmoothMetric M) (S : CanonicalSection M) (Ξ u : M.Carrier → ℝ) (o : M.Carrier)
    {c cΞ K ε δ : ℝ} (hc : 0 ≤ c) (hcΞ : 0 ≤ cΞ) (hK : 0 < K) (hε : 0 < ε)
    (hcompare : ∀ x, 1 + distFrom g.form o x ≤ K * u x)
    (hgrowth : ∀ x, Real.log (canonicalNormSq g.form S x) ≤ c * (1 + distFrom g.form o x))
    (hΞgrowth : ∀ x, Ξ x ≤ cΞ * (1 + distFrom g.form o x ^ ((3 : ℝ) / 2)))
    (hδ : 0 < δ)
    (hδsmall : δ ≤ Real.exp (canonicalGrowthShift c K ε - majorantGrowthShift cΞ K ε))
    (x : M.Carrier) :
    canonicalRegularizer g S Ξ δ x - ε * u x ^ 2 -
      canonicalRegularizerShiftCoefficient c K * (1 + ε⁻¹) ≤ 0 := by
  rw [canonicalRegularizerShiftCoefficient_eq]
  apply canonical_regularizer_uniform_shift_of_bounds g S Ξ u
    (canonicalGrowthShift_one_le c K hε) hδ hδsmall
    (canonical_norm_exponential_shift g S o u hc hε hcompare hgrowth)
  intro y
  linarith [majorantGrowthShift_controls hcΞ hK hε (g.induced_distance_nonneg o y)
    (hcompare y) (hΞgrowth y)]

end Yau.NodeProofs.F01Aux
