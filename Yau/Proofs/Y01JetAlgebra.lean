import Yau.Proofs.Y02Linear

/-! Finite coefficient truncation and substitution on the actual polynomial jets. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open MvPolynomial Yau.Proofs.Y02Aux

variable {n : ℕ}

def truncate (d : ℕ) (P : PolyMap n) : PolyMap n :=
  fun i => ⟨Finsupp.filter (fun a : Fin n →₀ ℕ => a.degree ≤ d) (P i).coeff⟩

theorem truncate_coeff (d : ℕ) (P : PolyMap n) (i : Fin n) (a : Fin n →₀ ℕ) :
    (truncate d P i).coeff a = if a.degree ≤ d then (P i).coeff a else 0 := rfl

theorem truncate_jetEq (d : ℕ) (P : PolyMap n) : PolyMap.JetEq (truncate d P) P d := by
  intro i a ha
  change a.degree ≤ d at ha
  rw [truncate_coeff, ite_eq_left ha]

theorem truncate_degree_le (d : ℕ) (P : PolyMap n) : (truncate d P).degree ≤ d := by
  classical
  unfold PolyMap.degree
  apply Finset.sup_le
  intro i hi
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro a ha
  exact (Finset.mem_filter.1 ha).2

theorem truncate_fixesZero {d : ℕ} {P : PolyMap n} (hP : P.FixesZero) :
    (truncate d P).FixesZero := by
  intro i
  rw [truncate_coeff, ite_eq_left (by simp)]
  exact hP i

theorem truncate_linearPart {d : ℕ} (hd : 1 ≤ d) (P : PolyMap n) :
    (truncate d P).linearPart = P.linearPart := by
  apply Matrix.ext
  intro i j
  exact truncate_jetEq d P i (Finsupp.single j 1) (by simpa using hd)

theorem truncate_coeffNorm_le (d : ℕ) (P : PolyMap n) :
    (truncate d P).coeffNorm ≤ P.coeffNorm := by
  classical
  unfold PolyMap.coeffNorm
  apply Finset.sum_le_sum
  intro i hi
  have hs : (truncate d P i).support ⊆ (P i).support :=
    Finset.filter_subset _ _
  change polynomialCoeffNorm (truncate d P i) ≤ polynomialCoeffNorm (P i)
  rw [← sum_norm_coeff_eq (truncate d P i) (P i).support hs]
  apply Finset.sum_le_sum
  intro a ha
  rw [truncate_coeff]
  split_ifs
  · exact le_rfl
  · simp

/-- Substitution of maps fixing zero preserves the coefficient filtration. -/
theorem scalarOrderAtLeast_bind {r : ℕ} {p : MvPolynomial (Fin n) ℂ}
    (hp : scalarOrderAtLeast r p) {Q : PolyMap n} (hQ : Q.FixesZero) :
    scalarOrderAtLeast r (bind₁ Q p) := by
  classical
  have hexp : bind₁ Q p = ∑ a ∈ p.support, bind₁ Q (monomial a (p.coeff a)) := by
    rw [← map_sum, support_sum_monomial_coeff]
  rw [hexp]
  apply scalarOrderAtLeast_sum
  intro a ha
  rw [bind₁_monomial]
  apply scalarOrderAtLeast_mul_left
  have hdeg : r ≤ a.degree := by
    by_contra hn
    have hz := hp a (by omega)
    exact (mem_support_iff.1 ha) hz
  apply scalarOrderAtLeast_mono _ hdeg
  have hprod := scalarOrderAtLeast_prod a.support (fun j => Q j ^ a j)
    (fun j => a j) (fun j hj => by
      have h1 : scalarOrderAtLeast 1 (Q j) := (scalarOrderAtLeast_one_iff _).2 (hQ j)
      simpa only [mul_one] using scalarOrderAtLeast_pow h1 (a j))
  exact hprod

/-- Substitution on the right only uses that the incoming map fixes zero. -/
theorem jetEq_comp_right {P R Q : PolyMap n} {d : ℕ}
    (h : PolyMap.JetEq P R d) (hQ : Q.FixesZero) :
    PolyMap.JetEq (P.comp Q) (R.comp Q) d := by
  apply (jetEq_iff_order _ _ _).2
  intro i
  have hsub := scalarOrderAtLeast_bind ((jetEq_iff_order _ _ _).1 h i) hQ
  simpa only [map_sub, PolyMap.comp, Pi.sub_apply] using hsub

/-- Postcomposition preserves the coefficient filtration by its polynomial
factorization; no coefficient-space identification is substituted for a germ. -/
theorem scalar_bind_sub_order {P Q : PolyMap n} {r : ℕ}
    (h : mapOrderAtLeast r (P - Q)) (p : MvPolynomial (Fin n) ℂ) :
    scalarOrderAtLeast r (bind₁ P p - bind₁ Q p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [bind₁_C_right, sub_self] using scalarOrderAtLeast_zero r
  | add p q hp hq =>
    simpa only [map_add, add_sub_add_comm] using scalarOrderAtLeast_add hp hq
  | mul_X p j hp =>
    have heq : bind₁ P (p * X j) - bind₁ Q (p * X j) =
        (bind₁ P p - bind₁ Q p) * P j + bind₁ Q p * (P j - Q j) := by
      simp only [map_mul, bind₁_X_right]
      ring
    rw [heq]
    exact scalarOrderAtLeast_add (scalarOrderAtLeast_mul_right hp _)
      (scalarOrderAtLeast_mul_left _ (h j))

theorem jetEq_comp_left (R : PolyMap n) {P Q : PolyMap n} {d : ℕ}
    (h : PolyMap.JetEq P Q d) :
    PolyMap.JetEq (R.comp P) (R.comp Q) d := by
  apply (jetEq_iff_order _ _ _).2
  intro i
  exact scalar_bind_sub_order ((jetEq_iff_order _ _ _).1 h) (R i)

theorem jetEq_comp {P P' Q Q' : PolyMap n} {d : ℕ}
    (hP : PolyMap.JetEq P P' d) (hQ : PolyMap.JetEq Q Q' d) (hzero : Q.FixesZero) :
    PolyMap.JetEq (P.comp Q) (P'.comp Q') d :=
  jetEq_trans (jetEq_comp_right hP hzero) (jetEq_comp_left P' hQ)

end Yau.Proofs.Y01Aux
