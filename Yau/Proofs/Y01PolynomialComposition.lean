import Yau.Proofs.Y01JetAlgebra

/-! Polynomial composition, evaluation, zero coefficients and linear parts. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open MvPolynomial Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem polyMap_eval_comp (P Q : PolyMap n) (z : ComplexVector n) :
    (P.comp Q).eval z = P.eval (Q.eval z) := by
  ext i
  change (eval fun j => z j) (bind₁ Q (P i)) =
    (eval fun j => (eval fun l => z l) (Q j)) (P i)
  exact eval₂Hom_bind₁ (RingHom.id ℂ) (fun j => z j) Q (P i)

theorem fixesZero_iff_eval_zero (P : PolyMap n) : P.FixesZero ↔ P.eval 0 = 0 := by
  constructor
  · intro h
    ext i
    change (eval fun _ : Fin n => (0 : ℂ)) (P i) = 0
    rw [eval_zero']
    exact h i
  · intro h i
    have hi := congrArg (fun z : ComplexVector n => z i) h
    change (eval fun _ : Fin n => (0 : ℂ)) (P i) = 0 at hi
    rw [eval_zero'] at hi
    exact hi

theorem comp_fixesZero {P Q : PolyMap n} (hP : P.FixesZero) (hQ : Q.FixesZero) :
    (P.comp Q).FixesZero := by
  apply (fixesZero_iff_eval_zero _).2
  rw [polyMap_eval_comp, (fixesZero_iff_eval_zero _).1 hQ]
  exact (fixesZero_iff_eval_zero _).1 hP

theorem jetEq_fixesZero {P Q : PolyMap n} {d : ℕ}
    (h : PolyMap.JetEq P Q d) (hQ : Q.FixesZero) : P.FixesZero := by
  intro i
  exact (h i 0 (by simp)).trans (hQ i)

theorem jetEq_linearPart {P Q : PolyMap n} {d : ℕ}
    (hd : 1 ≤ d) (h : PolyMap.JetEq P Q d) : P.linearPart = Q.linearPart := by
  apply Matrix.ext
  intro i j
  exact h i (Finsupp.single j 1) (by simpa using hd)

theorem jetEq_linear_of_fixesZero {P : PolyMap n} (hP : P.FixesZero) :
    PolyMap.JetEq P (linearPoly P.linearPart) 1 := by
  intro i a ha
  change a.degree ≤ 1 at ha
  by_cases hz : a = 0
  · subst a
    exact (hP i).trans (linearPoly_fixesZero P.linearPart i).symm
  · have hdeg : a.degree = 1 := by
      have hne : a.degree ≠ 0 := fun h => hz ((Finsupp.degree_eq_zero_iff a).1 h)
      omega
    have hex : a ∈ Set.range (fun j : Fin n => Finsupp.single j 1) := by
      rw [Finsupp.range_single_one]
      exact hdeg
    obtain ⟨j, rfl⟩ := hex
    exact (congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j)
      (linearPoly_linearPart P.linearPart)).symm

theorem comp_linearPart {P Q : PolyMap n} (hP : P.FixesZero) (hQ : Q.FixesZero) :
    (P.comp Q).linearPart = P.linearPart * Q.linearPart := by
  have h := jetEq_comp (jetEq_linear_of_fixesZero hP) (jetEq_linear_of_fixesZero hQ) hQ
  have hlin := jetEq_linearPart (by omega : 1 ≤ 1) h
  rw [linearPoly_comp, linearPoly_linearPart] at hlin
  exact hlin

theorem truncate_comp_jetEq (d : ℕ) {P Q : PolyMap n} (hQ : Q.FixesZero) :
    PolyMap.JetEq ((truncate d P).comp (truncate d Q)) (P.comp Q) d :=
  jetEq_comp (truncate_jetEq d P) (truncate_jetEq d Q) (truncate_fixesZero hQ)

end Yau.Proofs.Y01Aux
