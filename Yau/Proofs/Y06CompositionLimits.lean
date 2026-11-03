import Yau.Proofs.Y06BoundedCoefficients

/-! Bounded outer degree makes substitution a finite coefficient operation. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter MvPolynomial Yau.Proofs.Y02Aux
open scoped Topology

variable {n : ℕ}

theorem coefficientTendsto_C {c : ℕ → ℂ} {a : ℂ}
    (hc : Tendsto c atTop (𝓝 a)) : CoefficientTendsto (n := n) (fun H => C (c H)) (C a) := by
  intro β
  by_cases hβ : β = 0
  · subst β; simpa only [coeff_C, ite_true] using hc
  · simpa only [coeff_C, Ne.symm hβ, ite_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

theorem scalar_degree_expansion (p : MvPolynomial (Fin n) ℂ) {D : ℕ}
    (hp : p.totalDegree ≤ D) :
    p = ∑ β ∈ degreeMonomials n D, monomial β (p.coeff β) := by
  classical
  ext β
  have hzero (hβ : ¬β.degree ≤ D) : p.coeff β = 0 := by
    by_contra hn
    exact hβ ((le_totalDegree (mem_support_iff.mpr hn)).trans hp)
  simp only [coeff_sum, coeff_monomial]
  by_cases hβ : β.degree ≤ D
  · simp [mem_degreeMonomials, hβ, eq_comm]
  · simp [mem_degreeMonomials, hβ, eq_comm, hzero hβ]

theorem coefficientTendsto_bind_bounded
    {p : ℕ → MvPolynomial (Fin n) ℂ} {a : MvPolynomial (Fin n) ℂ}
    {Q : ℕ → PolyMap n} {R : PolyMap n} {D : ℕ}
    (hp : CoefficientTendsto p a) (hQ : ∀ i, CoefficientTendsto (fun H => Q H i) (R i))
    (hdegree : ∀ H, (p H).totalDegree ≤ D) (hadegree : a.totalDegree ≤ D) :
    CoefficientTendsto (fun H => bind₁ (Q H) (p H)) (bind₁ R a) := by
  classical
  have hexp (H : ℕ) : bind₁ (Q H) (p H) =
      ∑ β ∈ degreeMonomials n D, C ((p H).coeff β) * ∏ i ∈ β.support, (Q H i) ^ β i := by
    conv_lhs => rw [scalar_degree_expansion (p H) (hdegree H)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro β hβ
    rw [bind₁_monomial]
  have haexp : bind₁ R a =
      ∑ β ∈ degreeMonomials n D, C (a.coeff β) * ∏ i ∈ β.support, (R i) ^ β i := by
    conv_lhs => rw [scalar_degree_expansion a hadegree]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro β hβ
    rw [bind₁_monomial]
  simp_rw [hexp]
  rw [haexp]
  apply coefficientTendsto_sum
  intro β hβ
  exact coefficientTendsto_mul (coefficientTendsto_C (hp β))
    (coefficientTendsto_prod β.support _ _ (fun i hi => coefficientTendsto_pow (hQ i) (β i)))

theorem coefficientTendsto_comp_bounded {P Q : ℕ → PolyMap n} {R S : PolyMap n} {D : ℕ}
    (hP : ∀ i, CoefficientTendsto (fun H => P H i) (R i))
    (hQ : ∀ i, CoefficientTendsto (fun H => Q H i) (S i))
    (hdegree : ∀ H, (P H).degree ≤ D) (hRdegree : R.degree ≤ D) :
    ∀ i, CoefficientTendsto (fun H => (P H).comp (Q H) i) (R.comp S i) := by
  intro i
  exact coefficientTendsto_bind_bounded (hP i) hQ
    (fun H => (component_degree_le (P H) i).trans (hdegree H))
    ((component_degree_le R i).trans hRdegree)

end Yau.Proofs.Y06Aux
