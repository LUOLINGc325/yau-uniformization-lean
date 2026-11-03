import Yau.Proofs.Y01PolynomialCalculus
import Yau.Proofs.Y01GermComposition

/-! Actual coefficient jets imply equality of the Fréchet derivatives at zero. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open MvPolynomial Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n : ℕ}

theorem scalar_order_iteratedFDeriv_zero (m : ℕ)
    (p : MvPolynomial (Fin n) ℂ) (hp : scalarOrderAtLeast (m + 1) p) :
    iteratedFDeriv ℂ m (polyEval p) 0 = 0 := by
  classical
  induction m generalizing p with
  | zero =>
    ext v
    simp only [iteratedFDeriv_zero_apply, polyEval_zero, ContinuousMultilinearMap.zero_apply]
    exact hp 0 (by simp)
  | succ m ih =>
    have hf : (fun z => fderiv ℂ (polyEval p) z) =
        fun z => ∑ j, polyEval (pderiv j p) z •
          (EuclideanSpace.proj j : ComplexVector n →L[ℂ] ℂ) :=
      funext (fderiv_polyEval p)
    have hsum : iteratedFDeriv ℂ m
        (fun z => ∑ j, polyEval (pderiv j p) z •
          (EuclideanSpace.proj j : ComplexVector n →L[ℂ] ℂ)) 0 = 0 := by
      rw [iteratedFDeriv_fun_sum_apply (fun j hj =>
        ((polyEval_contDiff (pderiv j p)).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.smul_const _)]
      apply Finset.sum_eq_zero
      intro j hj
      rw [iteratedFDeriv_smul_const_apply
        ((polyEval_contDiff (pderiv j p)).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
      rw [ih (pderiv j p) (scalarOrderAtLeast_pderiv hp j)]
      ext v x
      simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
    ext v
    rw [iteratedFDeriv_succ_apply_right, hf, hsum]
    simp

theorem scalar_jetEq_iteratedFDeriv {p q : MvPolynomial (Fin n) ℂ} {d m : ℕ}
    (h : ∀ a : Fin n →₀ ℕ, a.degree ≤ d → p.coeff a = q.coeff a)
    (hm : m ≤ d) : iteratedFDeriv ℂ m (polyEval p) 0 =
      iteratedFDeriv ℂ m (polyEval q) 0 := by
  have horder : scalarOrderAtLeast (m + 1) (p - q) := by
    intro a ha
    change p.coeff a - q.coeff a = 0
    exact sub_eq_zero.mpr (h a (by omega))
  have hz := scalar_order_iteratedFDeriv_zero m (p - q) horder
  have heval : polyEval (p - q) = polyEval p - polyEval q := by
    funext z
    exact map_sub _ _ _
  rw [heval, iteratedFDeriv_sub_apply
    ((polyEval_contDiff p).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((polyEval_contDiff q).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt] at hz
  exact sub_eq_zero.mp hz

theorem jetEq_germJetEq {P Q : PolyMap n} {d : ℕ} (h : PolyMap.JetEq P Q d) :
    GermJetEq P.eval Q.eval d := by
  intro m hm
  ext v i
  have hs := scalar_jetEq_iteratedFDeriv (fun a ha => h i a ha) hm
  have hP := (EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).iteratedFDeriv_comp_left (x := 0)
    ((polyMap_eval_contDiff P).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt (le_refl (m : WithTop ℕ∞))
  have hQ := (EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).iteratedFDeriv_comp_left (x := 0)
    ((polyMap_eval_contDiff Q).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt (le_refl (m : WithTop ℕ∞))
  have hPv := congrArg (fun L => L v) hP
  have hQv := congrArg (fun L => L v) hQ
  have hsv := congrArg (fun L => L v) hs
  exact hPv.symm.trans (hsv.trans hQv)

end Yau.Proofs.Y01Aux
