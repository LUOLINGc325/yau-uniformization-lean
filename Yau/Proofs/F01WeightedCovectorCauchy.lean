import spec.CHAIN.CONTRACTS

/-! Cauchy--Schwarz for the actual finite weighted complex covector
quadratic form, proved by its two real coordinates in each complex direction. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {n : ℕ}

def weightedCovectorSquare (weights : Fin n → ℝ) (ξ : Fin n → ℂ) : ℝ :=
  ∑ i, weights i * Complex.normSq (ξ i)

def weightedCovectorPair (weights : Fin n → ℝ) (ξ η : Fin n → ℂ) : ℝ :=
  ∑ i, weights i * (ξ i * star (η i)).re

def weightedRealCoordinate (weights : Fin n → ℝ) (ξ : Fin n → ℂ) (p : Fin n × Fin 2) : ℝ :=
  Real.sqrt (weights p.1) * if p.2 = 0 then (ξ p.1).re else (ξ p.1).im

theorem weightedCovectorSquare_nonneg (weights : Fin n → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (ξ : Fin n → ℂ) : 0 ≤ weightedCovectorSquare weights ξ :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Complex.normSq_nonneg _))

theorem weightedRealCoordinate_square (weights : Fin n → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (ξ : Fin n → ℂ) :
    (∑ p : Fin n × Fin 2, weightedRealCoordinate weights ξ p ^ 2) =
      weightedCovectorSquare weights ξ := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, weightedRealCoordinate,
    Fin.reduceEq, ↓reduceIte, weightedCovectorSquare]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.normSq_apply]
  nlinarith [Real.sq_sqrt (hw i)]

theorem weightedRealCoordinate_pair (weights : Fin n → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (ξ η : Fin n → ℂ) :
    (∑ p : Fin n × Fin 2, weightedRealCoordinate weights ξ p * weightedRealCoordinate weights η p) =
      weightedCovectorPair weights ξ η := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, weightedRealCoordinate,
    Fin.reduceEq, ↓reduceIte, weightedCovectorPair]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  calc
    Real.sqrt (weights i) * (ξ i).re * (Real.sqrt (weights i) * (η i).re) +
        Real.sqrt (weights i) * (ξ i).im * (Real.sqrt (weights i) * (η i).im) =
          Real.sqrt (weights i) ^ 2 * ((ξ i).re * (η i).re + (ξ i).im * (η i).im) := by ring
    _ = _ := by rw [Real.sq_sqrt (hw i)]; ring

theorem weightedCovectorPair_le_sqrt (weights : Fin n → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (ξ η : Fin n → ℂ) :
    weightedCovectorPair weights ξ η ≤
      Real.sqrt (weightedCovectorSquare weights ξ) * Real.sqrt (weightedCovectorSquare weights η) := by
  have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (weightedRealCoordinate weights ξ) (weightedRealCoordinate weights η)
  rw [weightedRealCoordinate_pair weights hw, weightedRealCoordinate_square weights hw,
    weightedRealCoordinate_square weights hw] at hh
  exact hh

end Yau.NodeProofs.F01Aux
