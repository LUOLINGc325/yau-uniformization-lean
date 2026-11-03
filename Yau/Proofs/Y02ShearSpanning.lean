import Yau.Proofs.Y02Curl
import Yau.Proofs.Y02MonomialSlots

/-! Homogeneous divergence-free polynomial fields are spanned by shear fields. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ}

def wedgeDir (l : Fin n → ℂ) (i j : Fin n) : Fin n → ℂ :=
  Pi.single i (l j) - Pi.single j (l i)

theorem wedgeDir_orthogonal (l : Fin n → ℂ) (i j : Fin n) :
    (∑ k, l k * wedgeDir l i j k) = 0 := by
  classical
  simp only [wedgeDir, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  simp [Pi.single_apply, mul_comm]

theorem curl_linearForm_pow_mem_span (l : Fin n → ℂ) (i j : Fin n) (m : ℕ) :
    curl i j (linearForm l ^ (m + 1)) ∈ Submodule.span ℂ (shearFields n m) := by
  rw [curl_linearForm_pow]
  simp only [Nat.add_sub_cancel]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨l, wedgeDir l i j, wedgeDir_orthogonal l i j, rfl⟩

theorem curl_monomial_mem_span (i j : Fin n) (m : ℕ) (a : Fin n →₀ ℕ)
    (ha : a.degree = m + 1) :
    curl i j (monomial a (1 : ℂ)) ∈ Submodule.span ℂ (shearFields n m) := by
  classical
  let S := Submodule.span ℂ (shearFields n m)
  have hscale : curl i j ((a.degree.factorial : ℂ) • monomial a (1 : ℂ)) ∈ S := by
    have hcast : ((a.degree.factorial : ℂ) • monomial a (1 : ℂ)) =
        (a.degree.factorial : MvPolynomial (Fin n) ℂ) * monomial a (1 : ℂ) := by
      simp [smul_eq_C_mul]
    rw [hcast, monomial_polarization, map_sum]
    apply S.sum_mem
    intro T hT
    have hsign : (-1 : MvPolynomial (Fin n) ℂ) ^ (a.degree - T.card) *
        linearForm (slotForm a T) ^ a.degree =
        ((-1 : ℂ) ^ (a.degree - T.card)) • linearForm (slotForm a T) ^ a.degree := by
      simp [smul_eq_C_mul]
    rw [hsign, map_smul]
    apply S.smul_mem
    rw [ha]
    exact curl_linearForm_pow_mem_span _ i j m
  rw [map_smul] at hscale
  have hnonzero : (a.degree.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero a.degree
  have hinv := S.smul_mem ((a.degree.factorial : ℂ)⁻¹) hscale
  simpa only [smul_smul, inv_mul_cancel₀ hnonzero, one_smul] using hinv

theorem curl_homogeneous_mem_span (i j : Fin n) (m : ℕ)
    (H : MvPolynomial (Fin n) ℂ) (hH : H.IsHomogeneous (m + 1)) :
    curl i j H ∈ Submodule.span ℂ (shearFields n m) := by
  classical
  have hexp : H = ∑ a ∈ H.support, H.coeff a • monomial a (1 : ℂ) := by
    conv_lhs => rw [← support_sum_monomial_coeff H]
    apply Finset.sum_congr rfl
    intro a ha
    simp [smul_eq_C_mul, C_mul_monomial]
  rw [hexp, map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [map_smul]
  apply Submodule.smul_mem
  apply curl_monomial_mem_span i j m a
  rw [Finsupp.degree_eq_weight_one]
  exact hH (mem_support_iff.mp ha)

theorem homogeneous_ker_le_span_shearFields (m : ℕ) (hm : 2 ≤ m) :
    homogeneousFields n m ⊓ LinearMap.ker (divergence n) ≤
      Submodule.span ℂ (shearFields n m) := by
  intro P hP
  have hsum : (∑ i, ∑ j, curl i j (X j * P i)) ∈
      Submodule.span ℂ (shearFields n m) := by
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro j hj
    apply curl_homogeneous_mem_span i j m
    simpa only [add_comm] using (isHomogeneous_X ℂ j).mul (hP.1 i)
  rw [homogeneous_sum_curl (by omega) P hP.1] at hsum
  have hdiv : divergence n P = 0 := hP.2
  have hfun : (fun k => (n + m - 1) • P k - X k * divergence n P) =
      ((n + m - 1 : ℕ) : ℂ) • P := by
    funext k
    simp [hdiv, nsmul_eq_mul, smul_eq_C_mul]
  rw [hfun] at hsum
  have hnonzero : ((n + m - 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : n + m - 1 ≠ 0)
  have hinv := (Submodule.span ℂ (shearFields n m)).smul_mem
    (((n + m - 1 : ℕ) : ℂ)⁻¹) hsum
  simpa only [smul_smul, inv_mul_cancel₀ hnonzero, one_smul] using hinv

theorem shearFields_span_eq (m : ℕ) (hm : 2 ≤ m) :
    Submodule.span ℂ (shearFields n m) =
      homogeneousFields n m ⊓ LinearMap.ker (divergence n) :=
  le_antisymm (shearFields_span_le m) (homogeneous_ker_le_span_shearFields m hm)

end Yau.Proofs.Y02Aux
