import Yau.Proofs.E01QuadraticFiber

/-! Unit-sphere constraints equal the original all-vector constraints. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem homogeneous_minorant_of_sphere
    (v : ComplexVector n → EReal) (hzero : (0 : EReal) ≤ v 0)
    (hhom : ∀ r : ℝ, 0 < r → ∀ η : ComplexVector n,
      v ((r : ℂ) • η) = ((r ^ 2 : ℝ) : EReal) * v η)
    (D : Herm n)
    (hsphere : ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1,
      (ellipsoidQuadratic D η : EReal) ≤ v η) :
    ∀ η : ComplexVector n, (ellipsoidQuadratic D η : EReal) ≤ v η := by
  intro η
  by_cases hη : η = 0
  · simpa only [hη, ellipsoidQuadratic_zero_vector, EReal.coe_zero] using hzero
  · have hnorm : 0 < ‖η‖ := norm_pos_iff.mpr hη
    let η₁ : ComplexVector n := ((‖η‖⁻¹ : ℝ) : ℂ) • η
    have hη₁ : η₁ ∈ Metric.sphere (0 : ComplexVector n) 1 := by
      simp [η₁, norm_smul, hnorm.ne']
    have hre : (‖η‖ : ℂ) • η₁ = η := by
      dsimp only [η₁]
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hnorm.ne',
        Complex.ofReal_one, one_smul]
    have hq : ellipsoidQuadratic D η = ‖η‖ ^ 2 * ellipsoidQuadratic D η₁ := by
      simpa only [hre] using ellipsoidQuadratic_real_vector_smul D ‖η‖ η₁
    have hv : v η = ((‖η‖ ^ 2 : ℝ) : EReal) * v η₁ := by
      simpa only [hre] using hhom ‖η‖ hnorm η₁
    rw [hq, EReal.coe_mul, hv]
    exact mul_le_mul_of_nonneg_left (hsphere η₁ hη₁)
      (EReal.coe_nonneg.mpr (sq_nonneg ‖η‖))

theorem homogeneous_minorant_iff_sphere
    (v : ComplexVector n → EReal) (hzero : (0 : EReal) ≤ v 0)
    (hhom : ∀ r : ℝ, 0 < r → ∀ η : ComplexVector n,
      v ((r : ℂ) • η) = ((r ^ 2 : ℝ) : EReal) * v η)
    (D : Herm n) :
    (∀ η : ComplexVector n, (ellipsoidQuadratic D η : EReal) ≤ v η) ↔
      ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1,
        (ellipsoidQuadratic D η : EReal) ≤ v η := by
  exact ⟨fun h η _ => h η, homogeneous_minorant_of_sphere v hzero hhom D⟩

end Yau.NodeProofs.E01Aux
