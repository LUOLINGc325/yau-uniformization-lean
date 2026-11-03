import Yau.LeafProofs.L21CorrectedLevi

/-! Conjugation of the corrected matrix uses the actual mixed bracket and
its actual conjugate coefficient relation. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem conjugateD_star (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (f : X n → ℂ) (x : X n) :
    conjugateD A i (fun y => star (f y)) x = star (dbarA A i f x) := by
  simp only [conjugateD, dbarA_eq_real_rows, star_sum, star_mul, fderiv_star_apply, mul_comm]

theorem star_conjugateD_ofReal (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (φ : X n → ℝ) (i : Fin n) (x : X n) :
    star (conjugateD A i (fun y => (φ y : ℂ)) x) = dbarA A i (fun y => (φ y : ℂ)) x := by
  have h := mixedFrame_dbarA_star A i (fun y => (φ y : ℂ)) x
  simpa only [Complex.star_def, Complex.conj_ofReal] using h.symm

theorem correctedLevi_hermitian (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (φ : X n → ℝ) (c d : Fin n → Fin n → Fin n → X n → ℂ)
    (x : X n) (i j : Fin n)
    (hconj : ∀ k, star (d j i k x) = -c i j k x)
    (hbr : dbarA A i (conjugateD A j (fun y => (φ y : ℂ))) x -
      conjugateD A j (dbarA A i (fun y => (φ y : ℂ))) x =
      ∑ k, (c i j k x * dbarA A k (fun y => (φ y : ℂ)) x +
        d i j k x * conjugateD A k (fun y => (φ y : ℂ)) x)) :
    star (correctedLevi A φ d j i x) = correctedLevi A φ d i j x := by
  have hstar : star (dbarA A j (conjugateD A i (fun y => (φ y : ℂ))) x) =
      conjugateD A j (dbarA A i (fun y => (φ y : ℂ))) x := by
    rw [← conjugateD_star]
    congr 1
    funext y
    exact star_conjugateD_ofReal A φ i y
  simp only [correctedLevi, star_sub, star_sum, star_mul, hstar,
    hconj, star_conjugateD_ofReal, mul_neg, neg_mul, Finset.sum_neg_distrib, mul_comm]
  simp only [Finset.sum_add_distrib, mul_comm] at hbr
  linear_combination -hbr

end Yau.LeafProofs.L21Aux
