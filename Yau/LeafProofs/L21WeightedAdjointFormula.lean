import Yau.LeafProofs.L21WeightedAdjoint

/-! Expansion of the actual divergence adjoint into its principal and
zeroth-order terms. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem fderiv_star_apply (f : X n → ℂ) (x v : X n) :
    fderiv ℝ (fun y => star (f y)) x v = star (fderiv ℝ f x v) := by
  rw [fderiv_star, ContinuousLinearMap.comp_apply]
  rfl

theorem fderiv_ofReal_apply {φ : X n → ℝ} {x : X n}
    (hφ : DifferentiableAt ℝ φ x) (v : X n) :
    fderiv ℝ (fun y => (φ y : ℂ)) x v = (fderiv ℝ φ x v : ℂ) := by
  exact congrArg (fun L : X n →L[ℝ] ℂ => L v)
    (Complex.ofRealCLM.hasFDerivAt.comp x hφ.hasFDerivAt).fderiv

theorem fderiv_weightDensity {φ : X n → ℝ} {x : X n}
    (hφ : DifferentiableAt ℝ φ x) (v : X n) :
    fderiv ℝ (weightDensity φ) x v =
      -weightDensity φ x * (fderiv ℝ φ x v : ℂ) := by
  have he := congrArg (fun L : X n →L[ℝ] ℂ => L v)
    (Complex.ofRealCLM.hasFDerivAt.comp x hφ.hasFDerivAt.neg.exp).fderiv
  change fderiv ℝ (fun y => (Real.exp (-φ y) : ℂ)) x v =
    -(Real.exp (-φ x) : ℂ) * (fderiv ℝ φ x v : ℂ)
  simpa only [Function.comp_def, Pi.neg_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply,
    _root_.neg_apply, Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_neg,
    smul_eq_mul, neg_mul, mul_neg] using he

theorem star_weightDensity (φ : X n → ℝ) (x : X n) :
    star (weightDensity φ x) = weightDensity φ x := by
  change star (Real.exp (-φ x) : ℂ) = (Real.exp (-φ x) : ℂ)
  exact Complex.conj_ofReal _

theorem fderiv_weighted_row
    {φ : X n → ℝ} {p v : X n → ℂ} {x : X n}
    (hφ : DifferentiableAt ℝ φ x) (hp : DifferentiableAt ℝ p x)
    (hv : DifferentiableAt ℝ v x) (a : X n) :
    fderiv ℝ (fun y => star (v y) * p y * weightDensity φ y) x a =
      (star (fderiv ℝ v x a) * p x + star (v x) * fderiv ℝ p x a -
        star (v x) * p x * (fderiv ℝ φ x a : ℂ)) * weightDensity φ x := by
  have hs : DifferentiableAt ℝ (fun y => star (v y)) x := hv.star
  have hw : DifferentiableAt ℝ (weightDensity φ) x :=
    Complex.ofRealCLM.differentiableAt.comp x hφ.neg.exp
  rw [fderiv_fun_mul (c := fun y => star (v y) * p y) (d := weightDensity φ) (hs.mul hp) hw,
    fderiv_fun_mul (c := fun y => star (v y)) (d := p) hs hp]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    fderiv_star_apply, fderiv_weightDensity hφ]
  ring

theorem weightedDStarDiv_eq
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (φ : X n → ℝ)
    (i : Fin n) (v : X n → ℂ) (x : X n)
    (hA : ∀ a : Yau.RIdx n, DifferentiableAt ℝ (dbarRealCoefficient A i a) x)
    (hφ : DifferentiableAt ℝ φ x) (hv : DifferentiableAt ℝ v x) :
    weightedDStarDiv A φ i v x = weightedDStar A φ i v x := by
  apply star_injective
  apply mul_right_cancel₀ (weightDensity_ne_zero φ x)
  have hl : star (weightedDStarDiv A φ i v x) * weightDensity φ x =
      -(∑ a : Yau.RIdx n,
        fderiv ℝ (fun y => star (v y) * dbarRealCoefficient A i a y * weightDensity φ y)
          x (Yau.realVec a)) := by
    simpa only [mul_one] using weightedDStarDiv_pairing_pointwise A φ i (fun _ => 1) v x
  rw [hl]
  simp_rw [fderiv_weighted_row hφ (hA _) hv]
  rw [← Finset.sum_mul, ← neg_mul]
  congr 1
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  simp only [weightedDStar, conjugateD, conjugateDivergence,
    star_add, star_neg, star_sub, star_mul, star_sum, star_star,
    fderiv_star_apply, fderiv_ofReal_apply hφ, hreal]
  rw [← Finset.sum_neg_distrib]
  have hrow (a : Yau.RIdx n) :
      -(star (fderiv ℝ v x (Yau.realVec a)) * dbarRealCoefficient A i a x +
        star (v x) * fderiv ℝ (dbarRealCoefficient A i a) x (Yau.realVec a) -
        star (v x) * dbarRealCoefficient A i a x * (fderiv ℝ φ x (Yau.realVec a) : ℂ)) =
      -(dbarRealCoefficient A i a x * star (fderiv ℝ v x (Yau.realVec a))) +
        (dbarRealCoefficient A i a x * (fderiv ℝ φ x (Yau.realVec a) : ℂ) -
          fderiv ℝ (dbarRealCoefficient A i a) x (Yau.realVec a)) * star (v x) := by ring
  simp_rw [hrow]
  simp only [sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.sum_mul]
  simp_rw [mul_comm (dbarRealCoefficient A i _ x)]
  ring

end Yau.LeafProofs.L21Aux
