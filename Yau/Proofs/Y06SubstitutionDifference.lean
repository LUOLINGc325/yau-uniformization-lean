import Yau.Proofs.Y02JetSubstitution
import Yau.Proofs.Y06Homogeneous

/-! The polynomial order estimate behind a homogeneous-layer update. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem product_difference_order {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    (S : Finset ι) (p q : ι → MvPolynomial (Fin n) ℂ)
    (hp : ∀ i ∈ S, scalarOrderAtLeast 1 (p i))
    (hq : ∀ i ∈ S, scalarOrderAtLeast 1 (q i))
    (hdiff : ∀ i ∈ S, scalarOrderAtLeast m (p i - q i)) :
    scalarOrderAtLeast (S.card + m - 1) ((∏ i ∈ S, p i) - ∏ i ∈ S, q i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (scalarOrderAtLeast_zero (m - 1) : scalarOrderAtLeast (m - 1) (0 : MvPolynomial (Fin n) ℂ))
  | @insert i S hi ih =>
    have heq : (∏ j ∈ insert i S, p j) - (∏ j ∈ insert i S, q j) =
        (p i - q i) * (∏ j ∈ S, p j) + q i * ((∏ j ∈ S, p j) - ∏ j ∈ S, q j) := by
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      ring
    rw [heq, Finset.card_insert_of_notMem hi]
    apply scalarOrderAtLeast_add
    · have h := scalarOrderAtLeast_mul (hdiff i (Finset.mem_insert_self _ _))
        (scalarOrderAtLeast_prod_one S p (fun j hj => hp j (Finset.mem_insert_of_mem hj)))
      have hindex : m + S.card = S.card + 1 + m - 1 := by omega
      simpa only [hindex] using h
    · have h := scalarOrderAtLeast_mul (hq i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
          (fun j hj => hq j (Finset.mem_insert_of_mem hj))
          (fun j hj => hdiff j (Finset.mem_insert_of_mem hj)))
      have hindex : 1 + (S.card + m - 1) = S.card + 1 + m - 1 := by omega
      simpa only [hindex] using h

theorem monomial_bind_difference_order {m : ℕ} (hm : 1 ≤ m)
    (U V : PolyMap n) (hU : U.FixesZero) (hV : V.FixesZero)
    (hUV : mapOrderAtLeast m (U - V)) (β : Fin n →₀ ℕ) (c : ℂ) :
    scalarOrderAtLeast (β.degree + m - 1) (bind₁ U (monomial β c) - bind₁ V (monomial β c)) := by
  classical
  have hmono : monomial β c = C c * monomial β (1 : ℂ) := by simp [C_mul_monomial]
  rw [hmono, map_mul, map_mul, bind₁_C_right, bind₁_C_right, ← mul_sub]
  apply scalarOrderAtLeast_mul_left
  rw [← monomialWord_product β, map_prod, map_prod]
  simp only [bind₁_X_right]
  have h := product_difference_order hm Finset.univ
    (fun t : Fin β.degree => U (monomialWord β t))
    (fun t : Fin β.degree => V (monomialWord β t))
    (fun t ht => (scalarOrderAtLeast_one_iff _).mpr (hU _))
    (fun t ht => (scalarOrderAtLeast_one_iff _).mpr (hV _))
    (fun t ht => hUV (monomialWord β t))
  simpa only [Finset.card_univ, Fintype.card_fin] using h

theorem scalar_bind_difference_order {m r : ℕ} (hm : 1 ≤ m)
    (U V : PolyMap n) (hU : U.FixesZero) (hV : V.FixesZero)
    (hUV : mapOrderAtLeast m (U - V)) (p : MvPolynomial (Fin n) ℂ)
    (hp : scalarOrderAtLeast r p) :
    scalarOrderAtLeast (r + m - 1) (bind₁ U p - bind₁ V p) := by
  classical
  have heq : bind₁ U p - bind₁ V p = ∑ β ∈ p.support,
      (bind₁ U (monomial β (p.coeff β)) - bind₁ V (monomial β (p.coeff β))) := by
    rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, support_sum_monomial_coeff]
  rw [heq]
  apply scalarOrderAtLeast_sum
  intro β hβ
  have hdegree : r ≤ β.degree := by
    by_contra hnot
    exact (mem_support_iff.mp hβ) (hp β (by omega))
  apply scalarOrderAtLeast_mono (monomial_bind_difference_order hm U V hU hV hUV β (p.coeff β))
  omega

end Yau.Proofs.Y06Aux
