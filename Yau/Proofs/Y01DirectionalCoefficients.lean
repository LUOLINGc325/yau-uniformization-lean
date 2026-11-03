import Yau.Proofs.Y01CoefficientWords

/-! Coordinate derivative words are evaluations of the actual Fréchet jets. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open MvPolynomial
open scoped ContDiff

variable {n : ℕ}

def wordDirections : (w : List (Fin n)) → Fin w.length → ComplexVector n
  | [] => fun i => Fin.elim0 i
  | i :: w => Fin.snoc (wordDirections w) (stdVec i)

theorem fderiv_polyEval_stdVec (p : MvPolynomial (Fin n) ℂ) (i : Fin n)
    (z : ComplexVector n) : fderiv ℂ (polyEval p) z (stdVec i) = polyEval (pderiv i p) z := by
  classical
  rw [fderiv_polyEval]
  simp [stdVec, Finset.sum_ite_eq']

theorem iteratedFDeriv_word (w : List (Fin n)) (p : MvPolynomial (Fin n) ℂ)
    (z : ComplexVector n) :
    iteratedFDeriv ℂ w.length (polyEval p) z (wordDirections w) = polyEval (wordPartial w p) z := by
  induction w generalizing p with
  | nil => simp only [List.length_nil, iteratedFDeriv_zero_apply, wordPartial]
  | cons i w ih =>
    have hd : ContDiff ℂ (w.length : WithTop ℕ∞) (fun z => fderiv ℂ (polyEval p) z) :=
      (polyEval_contDiff p).fderiv_right (by
        exact_mod_cast (le_top : ((w.length + 1 : ℕ) : ℕ∞) ≤ ⊤))
    have hlin := (ContinuousLinearMap.apply ℂ ℂ (stdVec i)).iteratedFDeriv_comp_left
      (x := z) hd.contDiffAt (le_refl (w.length : WithTop ℕ∞))
    have hfun : ((ContinuousLinearMap.apply ℂ ℂ (stdVec i)) ∘
        (fun z => fderiv ℂ (polyEval p) z)) = polyEval (pderiv i p) := by
      funext z
      exact fderiv_polyEval_stdVec p i z
    rw [hfun] at hlin
    have hv := congrArg (fun L => L (wordDirections w)) hlin
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_apply, ContinuousLinearMap.apply_apply] at hv
    change iteratedFDeriv ℂ (w.length + 1) (polyEval p) z
      (Fin.snoc (wordDirections w) (stdVec i)) = polyEval (wordPartial w (pderiv i p)) z
    rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last, ← hv]
    exact ih (pderiv i p)

theorem stdVec_norm (i : Fin n) : ‖stdVec i‖ = 1 := by
  change ‖(PiLp.single 2 i (1 : ℂ) : ComplexVector n)‖ = 1
  simp

theorem wordDirections_norm (w : List (Fin n)) (j : Fin w.length) : ‖wordDirections w j‖ = 1 := by
  induction w with
  | nil => exact Fin.elim0 j
  | cons i w ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [wordDirections, Fin.snoc_last] using stdVec_norm i
    · simpa only [wordDirections, Fin.snoc_castSucc] using ih j

theorem scalar_coeff_norm_le_jet (p : MvPolynomial (Fin n) ℂ) (a : Fin n →₀ ℕ) :
    ‖p.coeff a‖ ≤ ‖iteratedFDeriv ℂ a.degree (polyEval p) 0‖ := by
  classical
  obtain ⟨w, hcount, hlength⟩ := exists_coefficient_word a
  obtain ⟨c, hc, hcoeff⟩ := wordPartial_coeff_zero w p
  have hcR : 1 ≤ (c : ℝ) := by exact_mod_cast hc
  have hvalue : iteratedFDeriv ℂ w.length (polyEval p) 0 (wordDirections w) =
      (c : ℂ) * p.coeff a := by
    rw [iteratedFDeriv_word, polyEval_zero, hcoeff, hcount]
  have hprod : (∏ j : Fin w.length, ‖wordDirections w j‖) = 1 := by
    simp only [wordDirections_norm, Finset.prod_const_one]
  have hnorm := (iteratedFDeriv ℂ w.length (polyEval p) 0).le_opNorm (wordDirections w)
  rw [hvalue, hprod, mul_one, hlength] at hnorm
  have hcC : ‖(c : ℂ)‖ = (c : ℝ) := by simp
  rw [norm_mul, hcC] at hnorm
  exact (le_mul_of_one_le_left (norm_nonneg _) hcR).trans hnorm

end Yau.Proofs.Y01Aux
