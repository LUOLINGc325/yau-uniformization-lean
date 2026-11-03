import Yau.LeafProofs.L10InteriorH2

/-! The H² energy controls exactly the original Fréchet Sobolev norm. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Yau.LeafProofs

theorem iteratedFDeriv_one_sq_le_ellipticGradientEnergy {n : ℕ}
    (u : ComplexVector n → ℂ) (x : ComplexVector n) :
    ‖iteratedFDeriv ℝ 1 u x‖^2 ≤ ellipticGradientEnergy u x := by
  classical
  have h := multilinear_norm_sq_le_basis_energy (complexVector_realOrthonormalBasis n)
    (iteratedFDeriv ℝ 1 u x)
  simp only [complexVector_realOrthonormalBasis_apply] at h
  have hsum : (∑ w : Fin 1 → RIdx n,
      ‖iteratedFDeriv ℝ 1 u x (fun j => realVec (w j))‖^2) =
      ∑ i, ‖fderiv ℝ u x (realVec i)‖^2 := by
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (RIdx n))
    intro w
    rw [iteratedFDeriv_one_apply]
    rfl
  exact h.trans_eq hsum

theorem iteratedFDeriv_two_sq_le_ellipticHessianEnergy {n : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O) {x : ComplexVector n} (hx : x ∈ O) :
    ‖iteratedFDeriv ℝ 2 u x‖^2 ≤ ellipticHessianEnergy u x := by
  classical
  have h := multilinear_norm_sq_le_basis_energy (complexVector_realOrthonormalBasis n)
    (iteratedFDeriv ℝ 2 u x)
  simp only [complexVector_realOrthonormalBasis_apply] at h
  have hsum : (∑ w : Fin 2 → RIdx n,
      ‖iteratedFDeriv ℝ 2 u x (fun j => realVec (w j))‖^2) =
      ∑ p : RIdx n × RIdx n, ‖ellipticHessianField u x p.2 p.1‖^2 := by
    apply Fintype.sum_equiv (finTwoArrowEquiv (RIdx n))
    intro w
    rw [ellipticHessianField_eq_tensor hO hu hx]
    congr 2
    apply congrArg (iteratedFDeriv ℝ 2 u x)
    funext j
    fin_cases j <;> rfl
  rw [Fintype.sum_prod_type] at hsum
  have hsum' : (∑ i, ∑ k, ‖ellipticHessianField u x k i‖^2) = ellipticHessianEnergy u x := by
    rw [Finset.sum_comm]
    rfl
  exact h.trans_eq (hsum.trans hsum')

theorem sobolevNormSq_two_le_ellipticEnergy {n : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O)
    (hi : ∀ k ≤ 2, IntegrableOn (fun x => ‖iteratedFDeriv ℝ k u x‖^2) O (lebesgueC n)) :
    LeafCandidates.sobolevNormSq O u 2 ≤
      (∫ x in O, ‖u x‖^2 ∂lebesgueC n) +
        (∫ x in O, ellipticGradientEnergy u x ∂lebesgueC n) +
        ∫ x in O, ellipticHessianEnergy u x ∂lebesgueC n := by
  have h1 : (∫ x in O, ‖iteratedFDeriv ℝ 1 u x‖^2 ∂lebesgueC n) ≤
      ∫ x in O, ellipticGradientEnergy u x ∂lebesgueC n :=
    integral_mono (hi 1 (by norm_num)) (ellipticGradientEnergy_integrableOn hO hu (hi 1 (by norm_num)))
      (iteratedFDeriv_one_sq_le_ellipticGradientEnergy u)
  have h2 : (∫ x in O, ‖iteratedFDeriv ℝ 2 u x‖^2 ∂lebesgueC n) ≤
      ∫ x in O, ellipticHessianEnergy u x ∂lebesgueC n := by
    apply integral_mono_ae (hi 2 (by norm_num)) (ellipticHessianEnergy_integrableOn hO hu (hi 2 (by norm_num)))
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact iteratedFDeriv_two_sq_le_ellipticHessianEnergy hO hu hx
  simp only [LeafCandidates.sobolevNormSq, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, norm_iteratedFDeriv_zero]
  linarith

end Yau.LeafProofs
