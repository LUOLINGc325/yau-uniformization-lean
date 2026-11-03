import Yau.LeafProofs.L21LeviHessian
import Yau.LeafProofs.L21HermitianGram

/-! The singular weight Hessian is contracted exactly as a sum of two
positive Gram matrices. No Hessian operator-norm comparison is used. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem leviHessian_boundaryWeight {K : ℝ} {x : X n}
    (hx : x ∈ Metric.ball (0 : X n) 1)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    leviHessianPart A (boundaryWeight K) i j x =
      (2 * K * (rho x)⁻¹ ^ 2 : ℝ) *
        (∑ a : Yau.RIdx n, dbarRealCoefficient A i a x * star (dbarRealCoefficient A j a x)) +
      (8 * K * (rho x)⁻¹ ^ 3 : ℝ) *
        (∑ a : Yau.RIdx n, ∑ b : Yau.RIdx n,
          dbarRealCoefficient A i a x * star (dbarRealCoefficient A j b x) *
            (inner ℝ x (Yau.realVec a) : ℂ) * (inner ℝ x (Yau.realVec b) : ℂ)) := by
  classical
  let α : ℝ := 2 * K * (rho x)⁻¹ ^ 2
  let β : ℝ := 8 * K * (rho x)⁻¹ ^ 3
  have hterm (a b : Yau.RIdx n) :
      dbarRealCoefficient A i a x * star (dbarRealCoefficient A j b x) *
        fderiv ℝ (fderiv ℝ (fun y : X n => (boundaryWeight K y : ℂ))) x (Yau.realVec a) (Yau.realVec b) =
      (α : ℂ) * (if a = b then dbarRealCoefficient A i a x * star (dbarRealCoefficient A j b x) else 0) +
        (β : ℂ) * (dbarRealCoefficient A i a x * star (dbarRealCoefficient A j b x) *
          (inner ℝ x (Yau.realVec a) : ℂ) * (inner ℝ x (Yau.realVec b) : ℂ)) := by
    rw [second_boundaryWeight_ofReal hx]
    change _ * ((α * (if a = b then 1 else 0) +
      β * inner ℝ x (Yau.realVec a) * inner ℝ x (Yau.realVec b) : ℝ) : ℂ) = _
    split_ifs <;> push_cast <;> ring
  unfold leviHessianPart
  simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

theorem leviHessian_boundaryWeight_quadratic {K : ℝ} {x : X n}
    (hx : x ∈ Metric.ball (0 : X n) 1)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → ℂ) :
    (∑ i, ∑ j, star (ξ i) * leviHessianPart A (boundaryWeight K) i j x * ξ j).re =
      (2 * K * (rho x)⁻¹ ^ 2) *
        (∑ a : Yau.RIdx n, ‖rowCombination A x (fun i => star (ξ i)) a‖ ^ 2) +
      (8 * K * (rho x)⁻¹ ^ 3) *
        ‖∑ a : Yau.RIdx n, rowCombination A x (fun i => star (ξ i)) a *
          (inner ℝ x (Yau.realVec a) : ℂ)‖ ^ 2 := by
  let α : ℝ := 2 * K * (rho x)⁻¹ ^ 2
  let β : ℝ := 8 * K * (rho x)⁻¹ ^ 3
  let p := fun i a => dbarRealCoefficient A i a x
  let r := fun a : Yau.RIdx n => inner ℝ x (Yau.realVec a)
  have hc : (∑ i, ∑ j, star (ξ i) * leviHessianPart A (boundaryWeight K) i j x * ξ j) =
      (α : ℂ) * (∑ i, ∑ j, star (ξ i) * (∑ a, p i a * star (p j a)) * ξ j) +
        (β : ℂ) * (∑ i, ∑ j, star (ξ i) *
          (∑ a, ∑ b, p i a * star (p j b) * (r a : ℂ) * (r b : ℂ)) * ξ j) := by
    calc
      _ = ∑ i, ∑ j, ((α : ℂ) * (star (ξ i) * (∑ a, p i a * star (p j a)) * ξ j) +
          (β : ℂ) * (star (ξ i) *
            (∑ a, ∑ b, p i a * star (p j b) * (r a : ℂ) * (r b : ℂ)) * ξ j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [leviHessian_boundaryWeight hx]
        dsimp only [α, β, p, r]
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hc]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, finite_hermitian_gram, finite_hermitian_rank_one]
  rfl

theorem leviHessian_boundaryWeight_lower_bound {K : ℝ} (hK : 0 ≤ K) {x : X n}
    (hx : x ∈ Metric.ball (0 : X n) 1)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → ℂ) :
    K * (rho x)⁻¹ ^ 2 * (∑ i, ‖ξ i‖ ^ 2) ≤
      (∑ i, ∑ j, star (ξ i) * leviHessianPart A (boundaryWeight K) i j x * ξ j).re := by
  rw [leviHessian_boundaryWeight_quadratic hx]
  have hP := principal_symbol_lower_bound A x (fun i => star (ξ i))
  simp only [norm_star] at hP
  have hρ := rho_pos hx
  calc
    _ = (2 * K * (rho x)⁻¹ ^ 2) * ((1 / 2 : ℝ) * ∑ i, ‖ξ i‖ ^ 2) := by ring
    _ ≤ (2 * K * (rho x)⁻¹ ^ 2) *
        (∑ a : Yau.RIdx n, ‖rowCombination A x (fun i => star (ξ i)) a‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    _ ≤ _ := le_add_of_nonneg_right (by positivity)

end Yau.LeafProofs.L21Aux
