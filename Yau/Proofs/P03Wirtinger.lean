import Yau.Geometry.Calculus

open scoped Topology

noncomputable section

namespace Yau.NodeProofs.P03Aux

section Complexification

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem realLinear_complex_smul (L : V →L[ℝ] ℂ) (c : ℂ) (v : V) :
    L (c • v) = (c.re : ℂ) * L v + (c.im : ℂ) * L (Complex.I • v) := by
  have he : c • v = c.re • v + c.im • (Complex.I • v) := by
    calc
      c • v = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • v :=
        congrArg (fun t : ℂ => t • v) (Complex.re_add_im c).symm
      _ = _ := by
        rw [add_smul, mul_smul]
        exact congrArg₂ (· + ·) (algebraMap_smul ℂ c.re v)
          (algebraMap_smul ℂ c.im (Complex.I • v))
  rw [he, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- A real continuous linear map satisfying the CR identity is complex
linear on the same domain, in arbitrary finite or infinite dimension. -/
def complexifyCR (L : V →L[ℝ] ℂ)
    (hI : ∀ v, L (Complex.I • v) = Complex.I * L v) : V →L[ℂ] ℂ where
  toFun := L
  map_add' := L.map_add
  map_smul' c v := by
    change L (c • v) = c * L v
    rw [realLinear_complex_smul, hI, ← mul_assoc, ← add_mul, Complex.re_add_im]
  cont := L.cont

theorem complexifyCR_restrictScalars (L : V →L[ℝ] ℂ)
    (hI : ∀ v, L (Complex.I • v) = Complex.I * L v) :
    (complexifyCR L hI).restrictScalars ℝ = L := by
  ext v
  rfl

theorem differentiableAt_complex_of_wirtBar_zero {f : V → ℂ} {z : V}
    (hf : DifferentiableAt ℝ f z) (hbar : ∀ v, wirtBar f z v = 0) :
    DifferentiableAt ℂ f z := by
  have hI (v : V) : fderiv ℝ f z (Complex.I • v) = Complex.I * fderiv ℝ f z v := by
    have hs : fderiv ℝ f z v + Complex.I * fderiv ℝ f z (Complex.I • v) = 0 := by
      exact (mul_eq_zero.mp (hbar v)).resolve_left (by norm_num)
    have hmul := congrArg (fun t : ℂ => Complex.I * t) hs
    have he : Complex.I * fderiv ℝ f z v - fderiv ℝ f z (Complex.I • v) = 0 := by
      simpa only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul,
        mul_zero, ← sub_eq_add_neg] using hmul
    exact (sub_eq_zero.mp he).symm
  exact (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt
    (complexifyCR_restrictScalars (fderiv ℝ f z) hI)).differentiableAt

theorem wirtBar_eq_zero_of_complex_differentiable (f : V → ℂ) (z v : V)
    (hf : DifferentiableAt ℂ f z) : wirtBar f z v = 0 := by
  unfold wirtBar
  rw [hf.fderiv_restrictScalars (𝕜 := ℝ)]
  change (1 / 2 : ℂ) *
    (fderiv ℂ f z v + Complex.I * fderiv ℂ f z (Complex.I • v)) = 0
  rw [map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

theorem wirtBar_add_direction (f : V → ℂ) (z v w : V) :
    wirtBar f z (v + w) = wirtBar f z v + wirtBar f z w := by
  unfold wirtBar
  rw [map_add, smul_add, map_add]
  ring

theorem wirtBar_smul_direction (f : V → ℂ) (z v : V) (c : ℂ) :
    wirtBar f z (c • v) = star c * wirtBar f z v := by
  have he : Complex.I • (c • v) = (Complex.I * c) • v := (mul_smul _ _ _).symm
  unfold wirtBar
  rw [realLinear_complex_smul (fderiv ℝ f z) c v, he,
    realLinear_complex_smul (fderiv ℝ f z) (Complex.I * c) v]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

theorem wirtBar_sum_direction {ι : Type*} (f : V → ℂ) (z : V)
    (s : Finset ι) (w : ι → V) :
    wirtBar f z (∑ i ∈ s, w i) = ∑ i ∈ s, wirtBar f z (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wirtBar]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, wirtBar_add_direction, ih]

end Complexification

theorem wirtBar_direction_coordinates {n : ℕ} (f : ComplexVector n → ℂ)
    (z v : ComplexVector n) :
    wirtBar f z v = ∑ i : Fin n, star (v i) * wirtBar f z (stdVec i) := by
  have hv : (∑ i : Fin n, v i • stdVec i) = v := by
    ext j
    simp [stdVec, PiLp.single_apply, Pi.single_apply, Finset.sum_apply', PiLp.smul_apply, eq_comm]
  calc
    wirtBar f z v = wirtBar f z (∑ i : Fin n, v i • stdVec i) := congrArg (wirtBar f z) hv.symm
    _ = ∑ i : Fin n, wirtBar f z (v i • stdVec i) := wirtBar_sum_direction f z Finset.univ _
    _ = _ := Finset.sum_congr rfl (fun i _ => wirtBar_smul_direction f z (stdVec i) (v i))

theorem differentiableAt_complex_of_wirtBar_basis_zero {n : ℕ}
    {f : ComplexVector n → ℂ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (hbar : ∀ i, wirtBar f z (stdVec i) = 0) :
    DifferentiableAt ℂ f z := by
  apply differentiableAt_complex_of_wirtBar_zero hf
  intro v
  simp [wirtBar_direction_coordinates, hbar]

end Yau.NodeProofs.P03Aux
