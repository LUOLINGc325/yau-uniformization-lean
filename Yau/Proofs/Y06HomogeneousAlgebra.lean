import Yau.Proofs.Y06Homogeneous

/-! Coefficient order, zero and linear parts of actual homogeneous updates. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n m : ℕ}

theorem homogeneous_order {P : PolyMap n} (hP : Homogeneous P m) : mapOrderAtLeast m P := by
  intro i β hβ
  by_contra hn
  have hdegree := hP i β hn
  change β.degree = m at hdegree
  omega

theorem homogeneous_fixesZero {P : PolyMap n} (hP : Homogeneous P m) (hm : 0 < m) :
    P.FixesZero := by
  intro i
  exact homogeneous_order hP i 0 (by simpa using hm)

theorem homogeneous_linearPart_zero {P : PolyMap n} (hP : Homogeneous P m) (hm : m ≠ 1) :
    P.linearPart = 0 := by
  ext i j
  change (P i).coeff (Finsupp.single j 1) = 0
  by_contra hn
  have hdegree := hP i (Finsupp.single j 1) hn
  have : (1 : ℕ) = m := by simpa using hdegree
  exact hm this.symm

theorem homogeneous_add {P Q : PolyMap n} (hP : Homogeneous P m) (hQ : Homogeneous Q m) :
    Homogeneous (P + Q) m := by
  apply (homogeneous_iff_components _).mpr
  intro i
  exact ((homogeneous_iff_components _).mp hP i).add ((homogeneous_iff_components _).mp hQ i)

theorem homogeneous_zero (m : ℕ) : Homogeneous (0 : PolyMap n) m := by
  intro i β hβ
  exact False.elim (hβ rfl)

theorem polynomial_degree_add_le (P Q : PolyMap n) : (P + Q).degree ≤ max P.degree Q.degree := by
  unfold PolyMap.degree
  apply Finset.sup_le
  intro i hi
  change (P i + Q i).totalDegree ≤ _
  exact (totalDegree_add _ _).trans (max_le_max (component_degree_le P i) (component_degree_le Q i))

theorem polynomial_linearPart_add (P Q : PolyMap n) : (P + Q).linearPart = P.linearPart + Q.linearPart := by
  ext i j
  rfl

theorem polynomial_fixesZero_add {P Q : PolyMap n} (hP : P.FixesZero) (hQ : Q.FixesZero) :
    (P + Q).FixesZero := by
  intro i
  change (P i).coeff 0 + (Q i).coeff 0 = 0
  rw [hP i, hQ i, add_zero]

end Yau.Proofs.Y06Aux
