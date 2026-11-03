import Yau.Proofs.Y03NormalizeEndpoint
import Yau.Proofs.Y03SVD

/-! Ordered diagonal rates are monotone under a unitary quadratic-form comparison. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem nonzero_kernel_of_dimension {a b : ℕ} (hab : b < a)
    (L : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ)) : ∃ v, v ≠ 0 ∧ L v = 0 := by
  by_contra! hn
  have hinj : Function.Injective L := by
    intro v w hvw
    apply sub_eq_zero.1
    by_contra hne
    exact hn (v - w) hne (by rw [map_sub, hvw, sub_self])
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
  omega

theorem unitary_row_norm_square_sum {U : Herm n} (hU : Unitary U) (v : Fin n → ℂ) :
    (∑ i, ‖(v ᵥ* U) i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
  have hq := matrixForm_conjugate (1 : Herm n) U.conjTranspose (star v)
  rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_one, hU.2] at hq
  simpa only [matrixForm_one, Matrix.mulVec_conjTranspose, star_star, Pi.star_apply, norm_star] using hq

theorem ordered_rates_le_of_unitary_order {U : Herm n} (hU : Unitary U)
    {μ ν : Fin n → ℝ} (hμ : Monotone μ) (hν : Monotone ν)
    (horder : ∀ v : Fin n → ℂ,
      (∑ l, μ l * ‖(v ᵥ* U) l‖ ^ 2) ≤ ∑ j, ν j * ‖v j‖ ^ 2) :
    ∀ i, μ i ≤ ν i := by
  intro i
  let J : (Fin (i.val + 1) → ℂ) →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi fun j =>
    if hj : j.val ≤ i.val then LinearMap.proj ⟨j.val, Nat.lt_succ_iff.2 hj⟩ else 0
  let R : (Fin n → ℂ) →ₗ[ℂ] (Fin i.val → ℂ) := LinearMap.pi fun l =>
    LinearMap.proj ⟨l.val, l.isLt.trans i.isLt⟩
  let L := R.comp (U.vecMulLinear.comp J)
  obtain ⟨w, hw, hL⟩ := nonzero_kernel_of_dimension (Nat.lt_succ_self i.val) L
  let v := J w
  have hv : v ≠ 0 := by
    intro hvzero
    apply hw
    funext a
    have ha : a.val ≤ i.val := Nat.lt_succ_iff.1 a.isLt
    have hj : a.val < n := a.isLt.trans_le (Nat.succ_le_of_lt i.isLt)
    have hz := congrFun hvzero ⟨a.val, hj⟩
    simpa only [v, J, LinearMap.pi_apply, LinearMap.proj_apply, ha, dite_eq_left,
      Pi.zero_apply] using hz
  have hvzero (j : Fin n) (hj : i < j) : v j = 0 := by
    simp only [v, J, LinearMap.pi_apply]
    rw [dite_eq_right (by omega)]
    rfl
  have holdzero (l : Fin n) (hl : l < i) : (v ᵥ* U) l = 0 := by
    have hz := congrFun hL ⟨l.val, hl⟩
    simpa only [L, R, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply,
      Matrix.vecMulLinear_apply, Pi.zero_apply, v] using hz
  have hsome : ∃ j, v j ≠ 0 := by
    by_contra! hz
    exact hv (funext hz)
  obtain ⟨j, hj⟩ := hsome
  have hnorm : 0 < ∑ j, ‖v j‖ ^ 2 :=
    Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨j, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hj) 2⟩
  have hLower : μ i * (∑ l, ‖(v ᵥ* U) l‖ ^ 2) ≤ ∑ l, μ l * ‖(v ᵥ* U) l‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    by_cases hl : l < i
    · rw [holdzero l hl]; simp
    · exact mul_le_mul_of_nonneg_right (hμ (le_of_not_gt hl)) (sq_nonneg _)
  have hUpper : (∑ j, ν j * ‖v j‖ ^ 2) ≤ ν i * ∑ j, ‖v j‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ≤ i
    · exact mul_le_mul_of_nonneg_right (hν hj) (sq_nonneg _)
    · rw [hvzero j (lt_of_not_ge hj)]; simp
  have hb := hLower.trans ((horder v).trans hUpper)
  rw [unitary_row_norm_square_sum hU v] at hb
  exact le_of_mul_le_mul_right hb hnorm

end Yau.Blueprint.Alignment.Y03Proof
