import Yau.Proofs.Y02CompositionBounds
import Yau.Proofs.Y02Linear
import Yau.Blueprint.Alignment

/-! Componentwise real bounds for ordinary polynomial total degrees. -/

noncomputable section

open scoped BigOperators

namespace Yau.Blueprint.Alignment.Y04Proof

open Yau MvPolynomial

theorem totalDegree_finsetSum_cast_le {ι : Type*} (S : Finset ι)
    (p : ι → MvPolynomial (Fin n) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hp : ∀ i ∈ S, ((p i).totalDegree : ℝ) ≤ R) :
    (((∑ i ∈ S, p i).totalDegree) : ℝ) ≤ R := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hR
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    have hdeg : (((p i + ∑ j ∈ S, p j).totalDegree):ℝ) ≤
        max ((p i).totalDegree : ℝ) ((∑ j ∈ S, p j).totalDegree : ℝ) := by
      exact_mod_cast totalDegree_add (p i) (∑ j ∈ S, p j)
    exact hdeg.trans (max_le (hp i (Finset.mem_insert_self i S))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))))

theorem totalDegree_bind_monomial_le_weight
    {n : ℕ} (P : PolyMap n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hP : ∀ i, ((P i).totalDegree : ℝ) ≤ w i)
    (β : Fin n →₀ ℕ) (c : ℂ) :
    ((bind₁ P (monomial β c)).totalDegree : ℝ) ≤
      ∑ i, (β i : ℝ)*w i := by
  classical
  rw [bind₁_monomial]
  calc
    _ ≤ ((C c).totalDegree : ℝ) + ((∏ i ∈ β.support, P i ^ β i).totalDegree : ℝ) := by
      exact_mod_cast totalDegree_mul (C c) (∏ i ∈ β.support, P i ^ β i)
    _ = ((∏ i ∈ β.support, P i ^ β i).totalDegree : ℝ) := by simp
    _ ≤ ∑ i ∈ β.support, ((P i ^ β i).totalDegree : ℝ) := by
      exact_mod_cast totalDegree_finsetProd β.support (fun i => P i ^ β i)
    _ ≤ ∑ i ∈ β.support, (β i : ℝ)*w i := by
      apply Finset.sum_le_sum
      intro i hi
      have hp : ((P i ^ β i).totalDegree : ℝ) ≤ (β i : ℝ) * (P i).totalDegree := by
        exact_mod_cast totalDegree_pow (P i) (β i)
      exact hp.trans (mul_le_mul_of_nonneg_left (hP i) (Nat.cast_nonneg _))
    _ = ∑ i, (β i : ℝ)*w i := by
      change β.sum (fun i e => (e:ℝ)*w i) = _
      exact Finsupp.sum_fintype β (fun i e => (e:ℝ)*w i) (by simp)

theorem totalDegree_bind_le_of_support_weight
    {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (P : PolyMap n)
    (w : Fin n → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hw : ∀ i, 0 ≤ w i) (hP : ∀ i, ((P i).totalDegree : ℝ) ≤ w i)
    (hp : ∀ β, p.coeff β ≠ 0 → ∑ i, (β i : ℝ)*w i ≤ R) :
    ((bind₁ P p).totalDegree : ℝ) ≤ R := by
  classical
  have hexp : bind₁ P p = ∑ β ∈ p.support, bind₁ P (monomial β (p.coeff β)) := by
    rw [← map_sum, support_sum_monomial_coeff]
  rw [hexp]
  exact totalDegree_finsetSum_cast_le p.support _ hR (fun β hβ =>
    (totalDegree_bind_monomial_le_weight P w hw hP β _).trans
      (hp β (mem_support_iff.mp hβ)))

theorem support_weight_le_of_allowed_diagonal
    {n : ℕ} {g : PolyMap n} {w : Fin n → ℝ} {δ : Fin n → ℂ}
    (hg0 : g.FixesZero) (hlin : g.linearPart = Matrix.diagonal δ)
    (hallow : Allowed g w) :
    ∀ i β, (g i).coeff β ≠ 0 → ∑ l, (β l : ℝ)*w l ≤ w i := by
  classical
  intro i β hβ
  by_cases hzero : β.degree = 0
  · have hβzero : β = 0 := (Finsupp.degree_eq_zero_iff β).mp hzero
    exact False.elim (hβ (hβzero ▸ hg0 i))
  by_cases hone : β.degree = 1
  · have hmem : β ∈ Set.range (fun l : Fin n => Finsupp.single l 1) := by
      rw [Finsupp.range_single_one]
      exact hone
    obtain ⟨l, rfl⟩ := hmem
    have hl : l = i := by
      by_contra hli
      have hc := congrFun (congrFun hlin i) l
      change (g i).coeff (Finsupp.single l 1) = (Matrix.diagonal δ) i l at hc
      have hc0 : (g i).coeff (Finsupp.single l 1) = 0 := by
        simpa [Matrix.diagonal_apply, Ne.symm hli] using hc
      exact hβ hc0
    subst l
    rw [← Finsupp.sum_fintype (Finsupp.single i (1:ℕ)) (fun l (e:ℕ) => (e:ℝ)*w l) (by simp)]
    simp
  · apply hallow i β (by change 2 ≤ β.degree; omega) hβ

theorem allowed_comp_component_degree
    {n : ℕ} {g P : PolyMap n} {w : Fin n → ℝ} {δ : Fin n → ℂ}
    (hw : ∀ i, 0 ≤ w i) (hg0 : g.FixesZero)
    (hlin : g.linearPart = Matrix.diagonal δ) (hallow : Allowed g w)
    (hP : ∀ i, ((P i).totalDegree : ℝ) ≤ w i) :
    ∀ i, (((g.comp P) i).totalDegree : ℝ) ≤ w i := by
  intro i
  exact totalDegree_bind_le_of_support_weight (g i) P w (w i) (hw i) hw hP
    (support_weight_le_of_allowed_diagonal hg0 hlin hallow i)

theorem linearPolynomial_eq_linearPoly {n : ℕ} (A : Herm n) :
    linearPolynomial A = Yau.Proofs.Y02Aux.linearPoly A := rfl

theorem linearPolynomial_one {n : ℕ} : linearPolynomial (1 : Herm n) = PolyMap.id :=
  (linearPolynomial_eq_linearPoly _).trans Yau.Proofs.Y02Aux.linearPoly_one

theorem linear_comp_component_degree
    {n : ℕ} {A : Herm n} {P : PolyMap n} {w v : Fin n → ℝ}
    (hv : ∀ i, 0 ≤ v i)
    (hA : ∀ i l, v i < w l → A i l = 0)
    (hP : ∀ l, ((P l).totalDegree : ℝ) ≤ w l) :
    ∀ i, ((((linearPolynomial A).comp P) i).totalDegree : ℝ) ≤ v i := by
  classical
  intro i
  rw [linearPolynomial_eq_linearPoly, Yau.Proofs.Y02Aux.linearPoly_comp_apply]
  apply totalDegree_finsetSum_cast_le Finset.univ _ (hv i)
  intro l hl
  by_cases hzero : A i l = 0
  · simpa [hzero] using hv i
  · have hwl : w l ≤ v i := by by_contra h; exact hzero (hA i l (lt_of_not_ge h))
    have hmul : ((C (A i l) * P l).totalDegree : ℝ) ≤
        ((C (A i l) : MvPolynomial (Fin n) ℂ).totalDegree : ℝ) + (P l).totalDegree := by
      exact_mod_cast totalDegree_mul (C (A i l)) (P l)
    simpa using hmul.trans (by simpa using (hP l).trans hwl)

theorem degree_le_of_component_degree
    {n : ℕ} {P : PolyMap n} {R : ℝ} (hR : 0 ≤ R)
    (hP : ∀ i, ((P i).totalDegree : ℝ) ≤ R) : (P.degree : ℝ) ≤ R := by
  classical
  unfold PolyMap.degree
  have h : ∀ S : Finset (Fin n), (((S.sup (fun i => (P i).totalDegree)) : ℕ):ℝ) ≤ R := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using hR
    | @insert i S hi ih => simpa only [Finset.sup_insert, Nat.cast_max] using max_le (hP i) ih
  exact h _

end Yau.Blueprint.Alignment.Y04Proof
