import Yau.Proofs.F01WeightedCovectorCauchy

/-! The triangle and real-scaling inequalities for the actual weighted
complex covector norm used at a Rayleigh penalty contact. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {n : ℕ}

theorem weightedCovectorSquare_add (weights : Fin n → ℝ) (ξ η : Fin n → ℂ) :
    weightedCovectorSquare weights (fun i => ξ i + η i) =
      weightedCovectorSquare weights ξ + weightedCovectorSquare weights η +
        2 * weightedCovectorPair weights ξ η := by
  unfold weightedCovectorSquare weightedCovectorPair
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.star_def,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem weightedCovectorSquare_real_mul (weights : Fin n → ℝ) (ξ : Fin n → ℂ) (s : ℝ) :
    weightedCovectorSquare weights (fun i => (s : ℂ) * ξ i) =
      s ^ 2 * weightedCovectorSquare weights ξ := by
  unfold weightedCovectorSquare
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem weightedCovector_sqrt_add_le (weights : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (ξ η : Fin n → ℂ) :
    Real.sqrt (weightedCovectorSquare weights (fun i => ξ i + η i)) ≤
      Real.sqrt (weightedCovectorSquare weights ξ) + Real.sqrt (weightedCovectorSquare weights η) := by
  have hA := weightedCovectorSquare_nonneg weights hw ξ
  have hB := weightedCovectorSquare_nonneg weights hw η
  have hC := weightedCovectorSquare_nonneg weights hw (fun i => ξ i + η i)
  have hp := weightedCovectorPair_le_sqrt weights hw ξ η
  have hformula := weightedCovectorSquare_add weights ξ η
  have hsquare : weightedCovectorSquare weights (fun i => ξ i + η i) ≤
      (Real.sqrt (weightedCovectorSquare weights ξ) + Real.sqrt (weightedCovectorSquare weights η)) ^ 2 := by
    nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB]
  have hroot := Real.sqrt_le_sqrt hsquare
  rw [Real.sqrt_sq (by positivity)] at hroot
  exact hroot

theorem weightedCovector_sqrt_real_mul (weights : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (ξ : Fin n → ℂ) {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt (weightedCovectorSquare weights (fun i => (s : ℂ) * ξ i)) =
      s * Real.sqrt (weightedCovectorSquare weights ξ) := by
  rw [weightedCovectorSquare_real_mul, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

end Yau.NodeProofs.F01Aux
