import Yau.Proofs.Y02Homogeneous

/-! Coefficient order at the origin and the finite-jet filtration. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

abbrev ScalarPoly (n : ℕ) := MvPolynomial (Fin n) ℂ

def scalarOrderAtLeast {n : ℕ} (r : ℕ) (p : ScalarPoly n) : Prop :=
  ∀ a : Fin n →₀ ℕ, a.degree < r → p.coeff a = 0

def mapOrderAtLeast {n : ℕ} (r : ℕ) (P : PolyMap n) : Prop :=
  ∀ i, scalarOrderAtLeast r (P i)

def tangentId {n : ℕ} (P : PolyMap n) : Prop :=
  P.FixesZero ∧ P.linearPart = 1

def homogeneousPart {n : ℕ} (m : ℕ) (P : PolyMap n) : PolyMap n :=
  fun i => homogeneousComponent m (P i)

def firstDiscrepancy {n : ℕ} (m : ℕ) (J G : PolyMap n) : PolyMap n :=
  homogeneousPart m (J - G)

def positiveJacFlat {n : ℕ} (P : PolyMap n) (d : ℕ) : Prop :=
  ∀ a : Fin n →₀ ℕ, 1 ≤ a.degree → a.degree ≤ d - 1 → P.jacDet.coeff a = 0

def jacobianMatrix {n : ℕ} (P : PolyMap n) : Matrix (Fin n) (Fin n) (ScalarPoly n) :=
  fun i j => pderiv j (P i)

variable {n r s : ℕ} {p q : ScalarPoly n}

theorem scalarOrderAtLeast_zero_order (p : ScalarPoly n) : scalarOrderAtLeast 0 p := by
  intro a ha
  omega

theorem scalarOrderAtLeast_zero (r : ℕ) : scalarOrderAtLeast r (0 : ScalarPoly n) := by
  intro a ha
  simp

theorem scalarOrderAtLeast_mono (hp : scalarOrderAtLeast r p) (hsr : s ≤ r) :
    scalarOrderAtLeast s p := by
  intro a ha
  exact hp a (ha.trans_le hsr)

theorem scalarOrderAtLeast_add (hp : scalarOrderAtLeast r p) (hq : scalarOrderAtLeast r q) :
    scalarOrderAtLeast r (p + q) := by
  intro a ha
  change p.coeff a + q.coeff a = 0
  rw [hp a ha, hq a ha, add_zero]

theorem scalarOrderAtLeast_neg (hp : scalarOrderAtLeast r p) : scalarOrderAtLeast r (-p) := by
  intro a ha
  change -p.coeff a = 0
  rw [hp a ha, neg_zero]

theorem scalarOrderAtLeast_sub (hp : scalarOrderAtLeast r p) (hq : scalarOrderAtLeast r q) :
    scalarOrderAtLeast r (p - q) := by
  simpa only [sub_eq_add_neg] using scalarOrderAtLeast_add hp (scalarOrderAtLeast_neg hq)

theorem scalarOrderAtLeast_sum {ι : Type*} (S : Finset ι) (P : ι → ScalarPoly n)
    (hP : ∀ i ∈ S, scalarOrderAtLeast r (P i)) : scalarOrderAtLeast r (∑ i ∈ S, P i) := by
  intro a ha
  rw [coeff_sum]
  exact Finset.sum_eq_zero fun i hi => hP i hi a ha

theorem scalarOrderAtLeast_mul (hp : scalarOrderAtLeast r p) (hq : scalarOrderAtLeast s q) :
    scalarOrderAtLeast (r + s) (p * q) := by
  classical
  intro a ha
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨b, c⟩ hbc
  have heq : b + c = a := Finset.HasAntidiagonal.mem_antidiagonal.mp hbc
  have hdeg : b.degree + c.degree = a.degree := by
    rw [← map_add, heq]
  by_cases hb : b.degree < r
  · rw [hp b hb, zero_mul]
  · rw [hq c (by omega), mul_zero]

theorem scalarOrderAtLeast_mul_right (hp : scalarOrderAtLeast r p) (q : ScalarPoly n) :
    scalarOrderAtLeast r (p * q) := by
  simpa only [Nat.add_zero] using scalarOrderAtLeast_mul hp (scalarOrderAtLeast_zero_order q)

theorem scalarOrderAtLeast_mul_left (p : ScalarPoly n) (hq : scalarOrderAtLeast r q) :
    scalarOrderAtLeast r (p * q) := by
  simpa only [Nat.zero_add] using scalarOrderAtLeast_mul (scalarOrderAtLeast_zero_order p) hq

theorem scalarOrderAtLeast_smul (hp : scalarOrderAtLeast r p) (c : ℂ) :
    scalarOrderAtLeast r (c • p) := by
  rw [smul_eq_C_mul]
  exact scalarOrderAtLeast_mul_left _ hp

theorem scalarOrderAtLeast_prod {ι : Type*} (S : Finset ι) (P : ι → ScalarPoly n)
    (R : ι → ℕ) (hP : ∀ i ∈ S, scalarOrderAtLeast (R i) (P i)) :
    scalarOrderAtLeast (∑ i ∈ S, R i) (∏ i ∈ S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using scalarOrderAtLeast_zero_order (1 : ScalarPoly n)
  | @insert i S hi hS =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact scalarOrderAtLeast_mul (hP i (Finset.mem_insert_self i S))
      (hS (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

theorem scalarOrderAtLeast_pow (hp : scalarOrderAtLeast r p) (k : ℕ) :
    scalarOrderAtLeast (k * r) (p ^ k) := by
  induction k with
  | zero => simpa using scalarOrderAtLeast_zero_order (1 : ScalarPoly n)
  | succ k hk =>
    rw [pow_succ, Nat.succ_mul]
    exact scalarOrderAtLeast_mul hk hp

theorem scalarOrderAtLeast_pderiv (hp : scalarOrderAtLeast (r + 1) p) (j : Fin n) :
    scalarOrderAtLeast r (pderiv j p) := by
  intro a ha
  rw [coeff_pderiv, hp (a + Finsupp.single j 1) (by simpa using Nat.add_lt_add_right ha 1)]
  simp

theorem scalarOrderAtLeast_one_iff (p : ScalarPoly n) :
    scalarOrderAtLeast 1 p ↔ p.coeff 0 = 0 := by
  constructor
  · intro hp
    exact hp 0 (by simp)
  · intro hp a ha
    have heq : a = 0 := (Finsupp.degree_eq_zero_iff a).mp (by omega)
    simpa only [heq] using hp

theorem order_of_isHomogeneous {m : ℕ} (hp : p.IsHomogeneous m) : scalarOrderAtLeast m p := by
  intro a ha
  exact hp.coeff_eq_zero ha.ne

theorem jetEq_iff_order (P Q : PolyMap n) (d : ℕ) :
    PolyMap.JetEq P Q d ↔ mapOrderAtLeast (d + 1) (P - Q) := by
  constructor
  · intro h i a ha
    change (P i).coeff a - (Q i).coeff a = 0
    exact sub_eq_zero.mpr (h i a (by change a.degree ≤ d; omega))
  · intro h i a ha
    change a.degree ≤ d at ha
    exact sub_eq_zero.mp (h i a (by omega))

theorem tangentId_iff_jetEq (P : PolyMap n) : tangentId P ↔ PolyMap.JetEq P PolyMap.id 1 := by
  classical
  constructor
  · rintro ⟨hzero, hlinear⟩ i a ha
    change a.degree ≤ 1 at ha
    by_cases ha0 : a.degree = 0
    · have heq : a = 0 := (Finsupp.degree_eq_zero_iff a).mp ha0
      simpa [heq, PolyMap.id, coeff_X] using hzero i
    · have ha1 : a.degree = 1 := by omega
      have hex : a ∈ Set.range (fun j : Fin n => Finsupp.single j 1) := by
        rw [Finsupp.range_single_one]
        exact ha1
      obtain ⟨j, rfl⟩ := hex
      have hentry := congrFun (congrFun hlinear i) j
      simpa [PolyMap.linearPart, PolyMap.id, coeff_X, Matrix.one_apply,
        Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)] using hentry
  · intro h
    constructor
    · intro i
      have hi := h i 0 (by simp)
      simpa [PolyMap.id, coeff_X] using hi
    · apply Matrix.ext
      intro i j
      have hi := h i (Finsupp.single j 1) (by simp)
      simpa [PolyMap.linearPart, PolyMap.id, coeff_X, Matrix.one_apply,
        Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)] using hi

theorem tangentId_iff_order (P : PolyMap n) :
    tangentId P ↔ mapOrderAtLeast 2 (P - PolyMap.id) := by
  rw [tangentId_iff_jetEq, jetEq_iff_order]

end Yau.Proofs.Y02Aux
