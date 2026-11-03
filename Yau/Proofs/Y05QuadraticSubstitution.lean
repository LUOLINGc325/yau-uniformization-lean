import Yau.Proofs.Y01InverseJets

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau MvPolynomial Yau.Proofs.Y02Aux

variable {n r : ℕ}

/-- Substitution into a quadratic remainder gains one coefficient order.
This is the finite nilpotence behind the inverse-jet iteration. -/
theorem quadratic_bind_sub_order {p : MvPolynomial (Fin n) ℂ}
    (hp : scalarOrderAtLeast 2 p) {P Q : PolyMap n}
    (hP : P.FixesZero) (hQ : Q.FixesZero) (hPQ : mapOrderAtLeast r (P - Q)) :
    scalarOrderAtLeast (r + 1) (bind₁ P p - bind₁ Q p) := by
  classical
  have hexp : bind₁ P p - bind₁ Q p = ∑ a ∈ p.support,
      (bind₁ P (monomial a (p.coeff a)) - bind₁ Q (monomial a (p.coeff a))) := by
    rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, support_sum_monomial_coeff]
  rw [hexp]
  apply scalarOrderAtLeast_sum
  intro a ha
  have hdeg : 2 ≤ a.degree := by
    by_contra hbad
    exact (mem_support_iff.mp ha) (hp a (by omega))
  have hex : ∃ j : Fin n, a j ≠ 0 := by
    by_contra hj
    push_neg at hj
    have ha0 : a = 0 := by ext j; exact hj j
    simp [ha0] at hdeg
  obtain ⟨j, hj⟩ := hex
  let b := a - Finsupp.single j 1
  have hba : b + Finsupp.single j 1 = a := Finsupp.sub_add_single_one_cancel hj
  have hb : 1 ≤ b.degree := by
    have H := congrArg (fun a : Fin n →₀ ℕ => a.degree) hba
    simp only [map_add, Finsupp.degree_single] at H
    omega
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hm : monomial a (p.coeff a) = X j * monomial b (p.coeff a) := by
    rw [X, monomial_mul_monomial, one_mul, add_comm, hba]
  have hrest : scalarOrderAtLeast 1 (monomial b (p.coeff a)) :=
    (scalarOrderAtLeast_one_iff _).mpr (by simp [coeff_monomial, hb0])
  have hrestP : scalarOrderAtLeast 1 (bind₁ P (monomial b (p.coeff a))) :=
    Yau.Proofs.Y01Aux.scalarOrderAtLeast_bind hrest hP
  have hrestPQ : scalarOrderAtLeast r
      (bind₁ P (monomial b (p.coeff a)) - bind₁ Q (monomial b (p.coeff a))) :=
    Yau.Proofs.Y01Aux.scalar_bind_sub_order hPQ _
  rw [hm, map_mul, map_mul, bind₁_X_right, bind₁_X_right]
  have H : P j * bind₁ P (monomial b (p.coeff a)) -
      Q j * bind₁ Q (monomial b (p.coeff a)) =
        (P j - Q j) * bind₁ P (monomial b (p.coeff a)) + Q j *
          (bind₁ P (monomial b (p.coeff a)) - bind₁ Q (monomial b (p.coeff a))) := by ring
  rw [H]
  apply scalarOrderAtLeast_add (scalarOrderAtLeast_mul (hPQ j) hrestP)
  simpa only [Nat.add_comm 1 r] using scalarOrderAtLeast_mul
    ((scalarOrderAtLeast_one_iff _).mpr (hQ j)) hrestPQ

theorem tangentId_comp_left_cancel {A P Q : PolyMap n} {d : ℕ}
    (hA : tangentId A) (hP : P.FixesZero) (hQ : Q.FixesZero)
    (h : PolyMap.JetEq (A.comp P) (A.comp Q) d) : PolyMap.JetEq P Q d := by
  have hR : mapOrderAtLeast 2 (A - PolyMap.id) := (tangentId_iff_order A).mp hA
  have hcomp : mapOrderAtLeast (d + 1) (A.comp P - A.comp Q) :=
    (jetEq_iff_order _ _ _).mp h
  have hbase : mapOrderAtLeast 1 (P - Q) := by
    intro i
    exact (scalarOrderAtLeast_one_iff _).mpr (by simp [coeff_sub, hP i, hQ i])
  have himprove (r : ℕ) (hr : r ≤ d)
      (hPQ : mapOrderAtLeast r (P - Q)) : mapOrderAtLeast (r + 1) (P - Q) := by
    intro i
    have hquad := quadratic_bind_sub_order (hR i) hP hQ hPQ
    have htop : scalarOrderAtLeast (r + 1) (A.comp P i - A.comp Q i) :=
      scalarOrderAtLeast_mono (hcomp i) (Nat.add_le_add_right hr 1)
    have heq : A.comp P i - A.comp Q i -
        (bind₁ P ((A - PolyMap.id : PolyMap n) i) -
          bind₁ Q ((A - PolyMap.id : PolyMap n) i)) = P i - Q i := by
      simp only [Pi.sub_apply, map_sub, PolyMap.comp, PolyMap.id, bind₁_X_right]
      ring
    change scalarOrderAtLeast (r + 1) (P i - Q i)
    rw [← heq]
    exact scalarOrderAtLeast_sub htop hquad
  apply (jetEq_iff_order _ _ _).mpr
  have hall : ∀ m, m ≤ d → mapOrderAtLeast (m + 1) (P - Q) := by
    intro m
    induction m with
    | zero => intro _; exact hbase
    | succ m ih =>
      intro hm
      exact himprove (m + 1) hm (ih (by omega))
  exact hall d le_rfl

end Yau.Proofs.Y05Aux
