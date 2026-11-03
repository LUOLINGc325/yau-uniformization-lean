import Yau.Proofs.Y06AllowedProjection
import Yau.Proofs.Y03Triangular

/-! Positive allowed weights make every nonlinear variable strictly lower
than its output. Equal weights cause no ambiguity in the finite rank. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem allowed_input_weight_lt (w : Fin n → ℝ) (hw : ∀ i, 1 ≤ w i)
    (β : Fin n →₀ ℕ) (hdegree : 2 ≤ β.degree) {i j : Fin n} (hj : 0 < β j)
    (hallowed : (∑ l, (β l : ℝ) * w l) ≤ w i) : w j < w i := by
  classical
  have hsumdegree : (2 : ℝ) ≤ ∑ l, (β l : ℝ) := by
    have hnat : 2 ≤ ∑ l, β l := by simpa only [Finsupp.degree_eq_sum] using hdegree
    exact_mod_cast hnat
  have hβj : (1 : ℝ) ≤ β j := by exact_mod_cast hj
  have hrest : w j - 1 ≤ ∑ l, (β l : ℝ) * (w l - 1) := by
    calc
      _ = 1 * (w j - 1) := (one_mul _).symm
      _ ≤ (β j : ℝ) * (w j - 1) := mul_le_mul_of_nonneg_right hβj (by linarith [hw j])
      _ ≤ _ := Finset.single_le_sum (f := fun l => (β l : ℝ) * (w l - 1))
        (fun l hl => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hw l)))
        (Finset.mem_univ j)
  have hdecomp : (∑ l, (β l : ℝ) * w l) =
      (∑ l, (β l : ℝ) * (w l - 1)) + ∑ l, (β l : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hdecomp] at hallowed
  linarith

def nonlinearPart (P : PolyMap n) : PolyMap n := P - linearPolynomial P.linearPart

theorem nonlinearPart_order_two {P : PolyMap n} (hP : P.FixesZero) :
    mapOrderAtLeast 2 (nonlinearPart P) := by
  classical
  intro i β hβ
  change (P i).coeff β - (linearPoly P.linearPart i).coeff β = 0
  by_cases hzero : β.degree = 0
  · have heq : β = 0 := (Finsupp.degree_eq_zero_iff β).mp hzero
    subst β
    rw [hP i]
    have hlinzero := linearPoly_fixesZero P.linearPart i
    rw [hlinzero, sub_zero]
  · have hone : β.degree = 1 := by omega
    have hex : β ∈ Set.range (fun j : Fin n => Finsupp.single j 1) := by
      rw [Finsupp.range_single_one]
      exact hone
    obtain ⟨j, rfl⟩ := hex
    change P.linearPart i j - (linearForm (P.linearPart i)).coeff (Finsupp.single j 1) = 0
    rw [linearForm_coeff_single]
    exact sub_self _

theorem linearPolynomial_coeff_higher (A : Herm n) (i : Fin n) (β : Fin n →₀ ℕ)
    (hβ : 2 ≤ β.degree) : (linearPolynomial A i).coeff β = 0 := by
  by_contra hn
  have htotal := le_totalDegree (mem_support_iff.mpr hn)
  change β.degree ≤ (linearPolynomial A i).totalDegree at htotal
  have hlinear : (linearPolynomial A i).totalDegree ≤ 1 :=
    (component_degree_le (linearPoly A) i).trans (linearPoly_degree_le A)
  omega

theorem nonlinearPart_strict_variables {P : PolyMap n} {w : Fin n → ℝ}
    (hP : P.FixesZero) (hallowed : Allowed P w) (hw : ∀ i, 1 ≤ w i) :
    ∀ i j, j ∈ (nonlinearPart P i).vars → w j < w i := by
  intro i j hj
  obtain ⟨β, hβ, hjβ⟩ := (mem_vars_iff_mem_support j).mp hj
  have hn : (nonlinearPart P i).coeff β ≠ 0 := mem_support_iff.mp hβ
  have hdegree : 2 ≤ β.degree := by
    by_contra hnot
    exact hn (nonlinearPart_order_two hP i β (by omega))
  have hcoeff : (P i).coeff β ≠ 0 := by
    change (P i).coeff β - (linearPolynomial P.linearPart i).coeff β ≠ 0 at hn
    simpa only [linearPolynomial_coeff_higher _ _ _ hdegree, sub_zero] using hn
  exact allowed_input_weight_lt w hw β hdegree
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hjβ)) (hallowed i β hdegree hcoeff)

end Yau.Proofs.Y06Aux
