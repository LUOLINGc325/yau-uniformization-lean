import Yau.Proofs.Y06CoefficientLimits

/-! Fixed finite coefficient spaces for bounded-degree polynomial maps. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter MvPolynomial Yau.Proofs.Y02Aux
open scoped Topology

variable {n : ℕ}

def degreeMonomials (n D : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finsupp.finite_of_degree_le D).toFinset

theorem mem_degreeMonomials {D : ℕ} (β : Fin n →₀ ℕ) :
    β ∈ degreeMonomials n D ↔ β.degree ≤ D := by
  simp [degreeMonomials]

def coefficientPolynomial (D : ℕ) (c : Fin n → (Fin n →₀ ℕ) → ℂ) : PolyMap n :=
  fun i => ∑ β ∈ degreeMonomials n D, monomial β (c i β)

theorem coefficientPolynomial_coeff (D : ℕ) (c : Fin n → (Fin n →₀ ℕ) → ℂ)
    (i : Fin n) (β : Fin n →₀ ℕ) :
    (coefficientPolynomial D c i).coeff β = if β.degree ≤ D then c i β else 0 := by
  classical
  simp [coefficientPolynomial, coeff_sum, coeff_monomial, eq_comm, mem_degreeMonomials]

theorem coefficientPolynomial_degree (D : ℕ) (c : Fin n → (Fin n →₀ ℕ) → ℂ) :
    (coefficientPolynomial D c).degree ≤ D := by
  classical
  unfold PolyMap.degree
  apply Finset.sup_le
  intro i hi
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro β hβ
  have hn := mem_support_iff.mp hβ
  rw [coefficientPolynomial_coeff] at hn
  by_contra hnot
  exact hn (ite_eq_right hnot)

theorem coeff_zero_of_degree_gt {P : PolyMap n} {D : ℕ} (hP : P.degree ≤ D)
    (i : Fin n) (β : Fin n →₀ ℕ) (hβ : ¬β.degree ≤ D) : (P i).coeff β = 0 := by
  by_contra hn
  exact hβ ((le_totalDegree (mem_support_iff.mpr hn)).trans ((component_degree_le P i).trans hP))

theorem coefficientPolynomial_reconstruct {P : PolyMap n} {D : ℕ} (hP : P.degree ≤ D) :
    coefficientPolynomial D (fun i β => (P i).coeff β) = P := by
  classical
  funext i
  ext β
  rw [coefficientPolynomial_coeff]
  by_cases hβ : β.degree ≤ D
  · exact ite_eq_left hβ
  · rw [ite_eq_right hβ, coeff_zero_of_degree_gt hP i β hβ]

theorem coefficient_norm_le_coeffNorm (P : PolyMap n) (i : Fin n) (β : Fin n →₀ ℕ) :
    ‖(P i).coeff β‖ ≤ P.coeffNorm := by
  classical
  apply le_trans _ (polynomialCoeffNorm_le_coeffNorm P i)
  by_cases hz : (P i).coeff β = 0
  · rw [hz, norm_zero]
    exact polynomialCoeffNorm_nonneg _
  · exact Finset.single_le_sum (fun γ hγ => norm_nonneg _) (mem_support_iff.mpr hz)

theorem coeffNorm_fixed_sum {P : PolyMap n} {D : ℕ} (hP : P.degree ≤ D) :
    P.coeffNorm = ∑ i, ∑ β ∈ degreeMonomials n D, ‖(P i).coeff β‖ := by
  classical
  change (∑ i, polynomialCoeffNorm (P i)) = _
  apply Finset.sum_congr rfl
  intro i hi
  symm
  apply sum_norm_coeff_eq
  intro β hβ
  exact (mem_degreeMonomials β).mpr
    ((le_totalDegree hβ).trans ((component_degree_le P i).trans hP))

theorem coeffNorm_tendsto_of_bounded_degree {p : ℕ → PolyMap n} {q : PolyMap n} {D : ℕ}
    (hp : ∀ i, CoefficientTendsto (fun H => p H i) (q i))
    (hdegree : ∀ H, (p H).degree ≤ D) (hqdegree : q.degree ≤ D) :
    Tendsto (fun H => (p H).coeffNorm) atTop (𝓝 q.coeffNorm) := by
  classical
  have hpfn : (fun H => (p H).coeffNorm) =
      (fun H => ∑ i, ∑ β ∈ degreeMonomials n D, ‖(p H i).coeff β‖) :=
    funext (fun H => coeffNorm_fixed_sum (hdegree H))
  rw [hpfn, coeffNorm_fixed_sum hqdegree]
  exact tendsto_finsetSum _ (fun i hi =>
    tendsto_finsetSum _ (fun β hβ => (hp i β).norm))

end Yau.Proofs.Y06Aux
