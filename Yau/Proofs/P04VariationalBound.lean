import Yau.Proofs.P04CompactQuadratic
import Yau.Proofs.P04FlatNakano

noncomputable section
open Set WithLp
open scoped Topology InnerProductSpace Matrix ComplexOrder ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem scalarCoefficientPairing_eq_inner (F U : Fin n → ℂ) :
    (∑ i, star (F i)*U i)=⟪(toLp 2 F : ComplexVector n),toLp 2 U⟫_ℂ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change star (F i)*U i=U i*star (F i)
  exact mul_comm _ _

/-- A uniform genuine quadratic lower bound controls the finite-dimensional
variational supremum, including the empty coefficient space. -/
theorem scalar_variational_bound (L : Matrix (Fin n) (Fin n) ℂ)
    {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ v : ComplexVector n, δ*‖v‖^2 ≤ matrixQuadratic L v)
    (F U : Fin n → ℂ) :
    2*(∑ i, star (F i)*U i).re-
      (star U ⬝ᵥ (L*ᵥU)).re ≤ ‖(toLp 2 F : ComplexVector n)‖^2/δ := by
  let f : ComplexVector n := toLp 2 F
  let u : ComplexVector n := toLp 2 U
  let q : ℝ := matrixQuadratic L u
  let C : ℝ := ‖f‖^2/δ
  have hC : 0 ≤ C := div_nonneg (sq_nonneg _) hδ.le
  have hq : δ*‖u‖^2 ≤ q := hlower u
  have hqn : 0 ≤ q := (mul_nonneg hδ.le (sq_nonneg _)).trans hq
  have hpair : (⟪f,u⟫_ℂ).re^2 ≤ ‖f‖^2*‖u‖^2 := by
    have hRe := Complex.re_sq_le_normSq (⟪f,u⟫_ℂ)
    rw [Complex.normSq_eq_norm_sq] at hRe
    have hnorm := norm_inner_le_norm (𝕜 := ℂ) f u
    nlinarith [norm_nonneg (⟪f,u⟫_ℂ),norm_nonneg f,norm_nonneg u]
  have hcancel : C*(δ*‖u‖^2)=‖f‖^2*‖u‖^2 := by
    dsimp only [C]
    field_simp
  have hprod : (⟪f,u⟫_ℂ).re^2 ≤ C*q :=
    hpair.trans (hcancel ▸ mul_le_mul_of_nonneg_left hq hC)
  have hyoung := two_mul_le_add_of_sq_le_mul hC hqn hprod
  rw [scalarCoefficientPairing_eq_inner]
  change 2*(⟪f,u⟫_ℂ).re-q ≤ C
  linarith

end Yau.Proofs.P04Aux
