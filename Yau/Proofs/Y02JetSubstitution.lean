import Yau.Proofs.Y02JetExtraction
import Yau.Proofs.Y02MonomialSlots

/-! Fixed-zero substitution respects jets; tangent substitution fixes the leading term. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ}

theorem comp_sub_left (P Q R : PolyMap n) : (P - Q).comp R = P.comp R - Q.comp R := by
  funext i
  exact map_sub (bind₁ R) (P i) (Q i)

theorem comp_add_left (P Q R : PolyMap n) : (P + Q).comp R = P.comp R + Q.comp R := by
  funext i
  exact map_add (bind₁ R) (P i) (Q i)

theorem scalarOrderAtLeast_bind {r : ℕ} (Q : PolyMap n) (hQ : Q.FixesZero)
    {p : ScalarPoly n} (hp : scalarOrderAtLeast r p) :
    scalarOrderAtLeast r (bind₁ Q p) := by
  classical
  have hexp : bind₁ Q p = ∑ a ∈ p.support, bind₁ Q (monomial a (p.coeff a)) := by
    rw [← map_sum, support_sum_monomial_coeff]
  rw [hexp]
  apply scalarOrderAtLeast_sum
  intro a ha
  have hdeg : r ≤ a.degree := by
    by_contra hbad
    exact (mem_support_iff.mp ha) (hp a (by omega))
  rw [bind₁_monomial]
  apply scalarOrderAtLeast_mono _ hdeg
  apply scalarOrderAtLeast_mul_left
  have hprod : scalarOrderAtLeast (∑ j ∈ a.support, a j) (∏ j ∈ a.support, Q j ^ a j) := by
    apply scalarOrderAtLeast_prod
    intro j hj
    simpa only [Nat.mul_one] using
      scalarOrderAtLeast_pow ((scalarOrderAtLeast_one_iff (Q j)).mpr (hQ j)) (a j)
  exact hprod

theorem jetEq_comp_right {P Q : PolyMap n} {d : ℕ}
    (h : PolyMap.JetEq P Q d) (R : PolyMap n) (hR : R.FixesZero) :
    PolyMap.JetEq (P.comp R) (Q.comp R) d := by
  rw [jetEq_iff_order, ← comp_sub_left]
  exact fun i => scalarOrderAtLeast_bind R hR ((jetEq_iff_order P Q d).mp h i)

theorem tangentId_comp {P Q : PolyMap n} (hP : tangentId P) (hQ : tangentId Q) :
    tangentId (P.comp Q) := by
  rw [tangentId_iff_order]
  have heq : P.comp Q - PolyMap.id = (P - PolyMap.id).comp Q + (Q - PolyMap.id) := by
    rw [comp_sub_left, id_comp]
    abel
  rw [heq]
  exact mapOrderAtLeast_add
    (fun i => scalarOrderAtLeast_bind Q hQ.1 ((tangentId_iff_order P).mp hP i))
    ((tangentId_iff_order Q).mp hQ)

theorem scalarOrderAtLeast_prod_one {ι : Type*} (S : Finset ι) (p : ι → ScalarPoly n)
    (hp : ∀ i ∈ S, scalarOrderAtLeast 1 (p i)) :
    scalarOrderAtLeast S.card (∏ i ∈ S, p i) := by
  simpa using scalarOrderAtLeast_prod S p (fun _ => 1) hp

theorem product_higher_difference_order {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p q : ι → ScalarPoly n)
    (hp : ∀ i ∈ S, scalarOrderAtLeast 1 (p i))
    (hq : ∀ i ∈ S, scalarOrderAtLeast 1 (q i))
    (hpq : ∀ i ∈ S, scalarOrderAtLeast 2 (p i - q i)) :
    scalarOrderAtLeast (S.card + 1) ((∏ i ∈ S, p i) - ∏ i ∈ S, q i) := by
  induction S using Finset.induction_on with
  | empty => simpa using
      (scalarOrderAtLeast_zero 1 : scalarOrderAtLeast 1 (0 : ScalarPoly n))
  | @insert i S hi ih =>
    have heq : (∏ j ∈ insert i S, p j) - (∏ j ∈ insert i S, q j) =
        (p i - q i) * (∏ j ∈ S, p j) + q i * ((∏ j ∈ S, p j) - ∏ j ∈ S, q j) := by
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      ring
    rw [heq, Finset.card_insert_of_notMem hi]
    apply scalarOrderAtLeast_add
    · have h := scalarOrderAtLeast_mul (hpq i (Finset.mem_insert_self i S))
        (scalarOrderAtLeast_prod_one S p (fun j hj => hp j (Finset.mem_insert_of_mem hj)))
      simpa only [Nat.add_comm 2 S.card, Nat.add_assoc] using h
    · have h := scalarOrderAtLeast_mul (hq i (Finset.mem_insert_self i S))
        (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
          (fun j hj => hq j (Finset.mem_insert_of_mem hj))
          (fun j hj => hpq j (Finset.mem_insert_of_mem hj)))
      simpa only [Nat.add_comm 1 (S.card + 1), Nat.add_assoc] using h

theorem monomial_bind_sub_order (Q : PolyMap n) (hQ : tangentId Q)
    (a : Fin n →₀ ℕ) (c : ℂ) :
    scalarOrderAtLeast (a.degree + 1) (bind₁ Q (monomial a c) - monomial a c) := by
  classical
  have hmono : monomial a c = C c * monomial a (1 : ℂ) := by simp [C_mul_monomial]
  rw [hmono, map_mul, bind₁_C_right, ← mul_sub]
  apply scalarOrderAtLeast_mul_left
  rw [← monomialWord_product a, map_prod]
  simp only [bind₁_X_right]
  have hQorder := (tangentId_iff_order Q).mp hQ
  have h := product_higher_difference_order Finset.univ
    (fun t : Fin a.degree => Q (monomialWord a t))
    (fun t : Fin a.degree => (X (monomialWord a t) : ScalarPoly n))
    (fun t ht => (scalarOrderAtLeast_one_iff _).mpr (hQ.1 _))
    (fun t ht => (scalarOrderAtLeast_one_iff _).mpr (by simp [coeff_X]))
    (fun t ht => hQorder (monomialWord a t))
  simpa only [Finset.card_univ, Fintype.card_fin] using h

theorem homogeneous_bind_sub_order {m : ℕ} (Q : PolyMap n) (hQ : tangentId Q)
    (p : ScalarPoly n) (hp : p.IsHomogeneous m) :
    scalarOrderAtLeast (m + 1) (bind₁ Q p - p) := by
  classical
  have heq : bind₁ Q p - p =
      ∑ a ∈ p.support, (bind₁ Q (monomial a (p.coeff a)) - monomial a (p.coeff a)) := by
    rw [Finset.sum_sub_distrib, ← map_sum, support_sum_monomial_coeff]
  rw [heq]
  apply scalarOrderAtLeast_sum
  intro a ha
  have ham : a.degree = m := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp ha)
  simpa only [ham] using monomial_bind_sub_order Q hQ a (p.coeff a)

theorem homogeneous_perturbation_comp {m : ℕ} (G H : PolyMap n)
    (hG : tangentId G) (hH : H ∈ homogeneousFields n m) :
    PolyMap.JetEq ((PolyMap.id + H).comp G) (G + H) m := by
  rw [jetEq_iff_order, comp_add_left, id_comp]
  have heq : G + H.comp G - (G + H) = H.comp G - H := by abel
  rw [heq]
  exact fun i => homogeneous_bind_sub_order G hG (H i) (hH i)

end Yau.Proofs.Y02Aux
