import Yau.Proofs.F01ClosedMetricLowerOrder

/-! Actual relative Hermitian metric sandwiches compose with their
computed product constant. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem relative_matrix_sandwich_compose
    {G K H : Matrix ι ι ℂ} {C D : ℝ} (hD : 0 ≤ D)
    (hK : (K - ((C⁻¹ : ℝ) : ℂ) • G).PosSemidef ∧ ((C : ℂ) • G - K).PosSemidef)
    (hH : (H - ((D⁻¹ : ℝ) : ℂ) • K).PosSemidef ∧ ((D : ℂ) • K - H).PosSemidef) :
    (H - (((C * D)⁻¹ : ℝ) : ℂ) • G).PosSemidef ∧
      (((C * D : ℝ) : ℂ) • G - H).PosSemidef := by
  constructor
  · have hh := hH.1.add (hK.1.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hD)))
    have he : H - (((C * D)⁻¹ : ℝ) : ℂ) • G =
        (H - ((D⁻¹ : ℝ) : ℂ) • K) + ((D⁻¹ : ℝ) : ℂ) • (K - ((C⁻¹ : ℝ) : ℂ) • G) := by
      simp only [mul_inv_rev, Complex.ofReal_mul, mul_smul, smul_sub]
      abel
    rw [he]
    exact hh
  · have hh := (hK.2.smul (Complex.zero_le_real.mpr hD)).add hH.2
    have he : (((C * D : ℝ) : ℂ) • G - H) =
        (D : ℂ) • ((C : ℂ) • G - K) + ((D : ℂ) • K - H) := by
      rw [Complex.ofReal_mul, smul_sub, smul_smul]
      have hc : (C : ℂ) * D = (D : ℂ) * C := mul_comm _ _
      rw [hc]
      abel
    rw [he]
    exact hh

end Yau.NodeProofs.F01Aux
