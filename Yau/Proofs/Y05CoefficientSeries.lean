import Yau.Proofs.Y05FiniteJets
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau MvPolynomial Yau.Proofs.Y02Aux
open scoped BigOperators

variable {n : ℕ}

def scalarMonomials (n d : ℕ) : Finset (Fin n →₀ ℕ) := by
  classical
  exact (Finset.univ.image (fun a : Fin n → Fin (d + 1) =>
    Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ)))).filter (fun a => a.degree ≤ d)

theorem mem_scalarMonomials {a : Fin n →₀ ℕ} {d : ℕ} :
    a ∈ scalarMonomials n d ↔ a.degree ≤ d := by
  classical
  refine ⟨fun ha => (Finset.mem_filter.mp ha).2, fun ha => ?_⟩
  have hbound (i : Fin n) : a i ≤ d := by
    have hi : a i ≤ a.degree := by
      by_cases hz : a i = 0
      · rw [hz]; exact Nat.zero_le _
      · exact Finset.single_le_sum (fun j _ => Nat.zero_le _)
          (Finsupp.mem_support_iff.mpr hz)
    exact hi.trans ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨fun i => ⟨a i, by have := hbound i; omega⟩,
    Finset.mem_univ _, ?_⟩, ha⟩
  ext i
  rfl

theorem norm_coefficient_le (P : MvPolynomial (Fin n) ℂ) (a : Fin n →₀ ℕ) :
    ‖P.coeff a‖ ≤ polynomialCoeffNorm P := by
  classical
  by_cases ha : a ∈ P.support
  · exact Finset.single_le_sum (fun b _ => norm_nonneg _) ha
  · rw [notMem_support_iff.mp ha, norm_zero]
    exact polynomialCoeffNorm_nonneg _

def coefficientSeriesPolynomial (d : ℕ) (B : ℕ → MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin n) ℂ :=
  ∑ a ∈ scalarMonomials n d, monomial a (∑' r, (B r).coeff a)

theorem coefficientSeriesPolynomial_coeff (d : ℕ) (B : ℕ → MvPolynomial (Fin n) ℂ)
    (a : Fin n →₀ ℕ) :
    (coefficientSeriesPolynomial d B).coeff a =
      if a.degree ≤ d then ∑' r, (B r).coeff a else 0 := by
  classical
  simp [coefficientSeriesPolynomial, coeff_sum, coeff_monomial, mem_scalarMonomials,
    eq_comm]

theorem coefficientSeriesPolynomial_degree (d : ℕ) (B : ℕ → MvPolynomial (Fin n) ℂ) :
    (coefficientSeriesPolynomial d B).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro a ha
  exact (totalDegree_monomial_le _ _).trans (mem_scalarMonomials.mp ha)

theorem coefficientSeriesPolynomial_zero (d : ℕ) (B : ℕ → MvPolynomial (Fin n) ℂ)
    (hB : ∀ r, (B r).coeff 0 = 0) : (coefficientSeriesPolynomial d B).coeff 0 = 0 := by
  simp [coefficientSeriesPolynomial_coeff, hB]

theorem coefficientSeriesPolynomial_hasSum {d : ℕ} {B : ℕ → MvPolynomial (Fin n) ℂ}
    (hdeg : ∀ r, (B r).totalDegree ≤ d) {b : ℕ → ℝ} (hb : Summable b)
    (hbound : ∀ r, polynomialCoeffNorm (B r) ≤ b r) :
    ∀ a, HasSum (fun r => (B r).coeff a) ((coefficientSeriesPolynomial d B).coeff a) := by
  intro a
  rw [coefficientSeriesPolynomial_coeff]
  by_cases ha : a.degree ≤ d
  · rw [if_pos ha]
    exact (Summable.of_norm (hb.of_nonneg_of_le (fun r => norm_nonneg _)
      (fun r => (norm_coefficient_le (B r) a).trans (hbound r)))).hasSum
  · rw [if_neg ha]
    have hz (r : ℕ) : (B r).coeff a = 0 := coeff_eq_zero_of_totalDegree_lt (by
      change (B r).totalDegree < a.degree; have := hdeg r; omega)
    simpa only [hz] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)

theorem coefficientSeriesPolynomial_norm_bound {d : ℕ} {B : ℕ → MvPolynomial (Fin n) ℂ}
    {b : ℕ → ℝ} (hb : Summable b)
    (hbound : ∀ r, polynomialCoeffNorm (B r) ≤ b r) :
    polynomialCoeffNorm (coefficientSeriesPolynomial d B) ≤
      ((scalarMonomials n d).card : ℝ) * ∑' r, b r := by
  classical
  apply (polynomialCoeffNorm_sum _ _).trans
  simp only [polynomialCoeffNorm_monomial]
  calc
    _ ≤ ∑ _a ∈ scalarMonomials n d, ∑' r, b r := by
      apply Finset.sum_le_sum
      intro a ha
      have hs : Summable (fun r => ‖(B r).coeff a‖) :=
        hb.of_nonneg_of_le (fun r => norm_nonneg _)
          (fun r => (norm_coefficient_le (B r) a).trans (hbound r))
      exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum
        (fun r => (norm_coefficient_le (B r) a).trans (hbound r)) hb)
    _ = _ := by simp

end Yau.Proofs.Y05Aux
