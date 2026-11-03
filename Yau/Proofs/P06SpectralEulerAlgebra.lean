import Yau.Proofs.P06SpectralReal

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace

namespace Yau.NodeProofs.P06Aux.ComplexHilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

@[simp] theorem complexify_add (S T : H →L[ℝ] H) :
    complexify (S + T) = complexify S + complexify T := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext <;> simp only [add_apply, re_add, im_add, complexify_re, complexify_im]

@[simp] theorem complexify_smul (r : ℝ) (T : H →L[ℝ] H) :
    complexify (r • T) = r • complexify T := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext <;> simp only [smul_apply, re_real_smul, im_real_smul, complexify_re, complexify_im]

@[simp] theorem complexify_mul (S T : H →L[ℝ] H) :
    complexify (S * T) = complexify S * complexify T := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext <;> simp only [mul_apply_eq_comp, complexify_re, complexify_im]

@[simp] theorem complexify_one : complexify (1 : H →L[ℝ] H) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext <;> simp only [one_apply_eq_self, complexify_re, complexify_im]

@[simp] theorem complexify_pow (T : H →L[ℝ] H) (j : ℕ) :
    complexify (T ^ j) = complexify T ^ j := by
  induction j with
  | zero => simp
  | succ j hj => simp only [pow_succ, complexify_mul, hj]

@[simp] theorem realRestriction_complexify (T : H →L[ℝ] H) :
    Spectral.realRestrictionCLM (complexify T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  exact (complexify_re T (ofRealCLM x)).trans (congrArg T (re_ofReal x))

end Yau.NodeProofs.P06Aux.ComplexHilbert
