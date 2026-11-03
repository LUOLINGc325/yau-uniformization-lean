import Yau.Proofs.G04FormInnerMatrix
import Mathlib.Analysis.Matrix.Order

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace Yau.NodeProofs.G04Aux
open Yau Matrix
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem exists_hermitian_whitening (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ,
      S.IsHermitian ∧ IsUnit S ∧ S * S = H⁻¹ ∧ S * H * S = 1 := by
  let S := CFC.sqrt H⁻¹
  have hS : S.IsHermitian :=
    ((Matrix.nonneg_iff_posSemidef).mp (CFC.sqrt_nonneg H⁻¹)).1
  have hsq : S * S = H⁻¹ := CFC.sqrt_mul_sqrt_self H⁻¹ hH.inv.posSemidef.nonneg
  have hu : IsUnit S := (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
    (by simpa only [pow_two, hsq] using hH.inv.isUnit)
  have hSHS : S * H * S = 1 := by
    apply hu.mul_left_cancel
    calc
      S * (S * H * S) = (S * S) * H * S := by noncomm_ring
      _ = S * 1 := by
        rw [hsq, Matrix.nonsing_inv_mul _ (hH.isUnit.map Matrix.detMonoidHom)]
        simp
  exact ⟨S, hS, hu, hsq, hSHS⟩

theorem whitening_trace (H A S : Matrix (Fin n) (Fin n) ℂ) (hS : S * S = H⁻¹) :
    (Matrix.trace (S * A * S)).re = traceWith H A := by
  rw [Matrix.trace_mul_cycle, hS]
  rfl

theorem whitening_square_trace (H A S : Matrix (Fin n) (Fin n) ℂ) (hS : S * S = H⁻¹) :
    (Matrix.trace ((S * A * S) ^ 2)).re = (Matrix.trace ((H⁻¹ * A) ^ 2)).re := by
  have hp : (S * A * S) ^ 2 = S * (A * (S * S) * A) * S := by
    simp only [pow_two]
    noncomm_ring
  rw [hp, Matrix.trace_mul_cycle, hS]
  congr 1
  simp only [pow_two]
  noncomm_ring

theorem whitening_order_iff (H A S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsHermitian) (hu : IsUnit S) (hSHS : S * H * S = 1) (C : ℝ) :
    ((A - (-C : ℂ) • H).PosSemidef ∧ ((C : ℂ) • H - A).PosSemidef) ↔
      ((S * A * S - (-C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef ∧
        ((C : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - S * A * S).PosSemidef) := by
  have h₁ := hu.posSemidef_star_left_conjugate_iff (x := A - (-C : ℂ) • H)
  have h₂ := hu.posSemidef_star_left_conjugate_iff (x := (C : ℂ) • H - A)
  rw [hS.star_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hSHS] at h₁ h₂
  exact and_congr h₁.symm h₂.symm

end Yau.NodeProofs.G04Aux
