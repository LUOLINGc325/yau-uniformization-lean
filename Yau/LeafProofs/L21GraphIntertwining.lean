import Yau.LeafProofs.L21GraphDifferential

/-! The kernel of the actual graph operator is precisely the complex-linear
intertwining condition in the original leaf. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def graphRealLinear (C : X n →L[ℝ] X n) : X n →L[ℝ] X n :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ (X n) + C)

theorem stdComplex_isInvertible (n : ℕ) : (stdComplex n).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := -stdComplex n)
  · ext v
    simp [stdComplex, smul_smul, Complex.I_mul_I]
  · ext v
    simp [stdComplex, smul_smul, Complex.I_mul_I]

theorem cayley_graphRealLinear_eq (J : X n →L[ℝ] X n)
    (hi : (J + stdComplex n).IsInvertible) :
    graphRealLinear (cayleyMap J) = (J + stdComplex n).inverse.comp (stdComplex n) := by
  ext1 v
  apply hi.injective
  change J (graphReal (cayleyMap J) v) + Complex.I • graphReal (cayleyMap J) v =
    (J + stdComplex n) ((J + stdComplex n).inverse (stdComplex n v))
  rw [structure_graphReal J hi, hi.self_apply_inverse]
  simp only [stdComplex_apply, graphReal, graphImag]
  module

theorem cayley_graphRealLinear_isInvertible (J : X n →L[ℝ] X n)
    (hi : (J + stdComplex n).IsInvertible) :
    (graphRealLinear (cayleyMap J)).IsInvertible := by
  rw [cayley_graphRealLinear_eq J hi]
  exact hi.inverse.comp (stdComplex_isInvertible n)

theorem realLinear_eq_sum_of_basis (L : X n →L[ℝ] ℂ)
    (hI : ∀ i, L (Complex.I • Yau.stdVec i) = Complex.I * L (Yau.stdVec i))
    (v : X n) : L v = ∑ i, v i * L (Yau.stdVec i) := by
  have hv : v = ∑ i, ((v i).re • Yau.stdVec i +
      (v i).im • (Complex.I • Yau.stdVec i)) := by
    ext k
    simp [Yau.stdVec, Pi.single_apply, Complex.real_smul, Finset.sum_add_distrib, eq_comm]
  conv_lhs => rw [hv]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_add, map_smul, map_smul, hI]
  simp only [Complex.real_smul]
  calc
    (v i).re * L (Yau.stdVec i) + (v i).im * (Complex.I * L (Yau.stdVec i)) =
        ((v i).re + (v i).im * Complex.I) * L (Yau.stdVec i) := by ring
    _ = v i * L (Yau.stdVec i) := by rw [Complex.re_add_im]

theorem realLinear_I_of_basis (L : X n →L[ℝ] ℂ)
    (hI : ∀ i, L (Complex.I • Yau.stdVec i) = Complex.I * L (Yau.stdVec i))
    (v : X n) : L (Complex.I • v) = Complex.I * L v := by
  rw [realLinear_eq_sum_of_basis L hI, realLinear_eq_sum_of_basis L hI]
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem graph_kernel_iff_intertwines (J : X n →L[ℝ] X n)
    (hJ2 : ∀ v, J (J v) = -v) (hi : (J + stdComplex n).IsInvertible)
    (L : X n →L[ℝ] ℂ) :
    (∀ i, L (graphReal (cayleyMap J) (Yau.stdVec i)) +
      Complex.I * L (graphImag (cayleyMap J) (Yau.stdVec i)) = 0) ↔
    (∀ v, L (J v) = Complex.I * L v) := by
  constructor
  · intro h
    let R := graphRealLinear (cayleyMap J)
    let M := L.comp R
    have hI (i : Fin n) : M (Complex.I • Yau.stdVec i) = Complex.I * M (Yau.stdVec i) := by
      change L (graphReal (cayleyMap J) (Complex.I • Yau.stdVec i)) =
        Complex.I * L (graphReal (cayleyMap J) (Yau.stdVec i))
      rw [graphReal_I_of_anticommutes _ (cayley_anticommutes J hJ2 hi)]
      have hh := congrArg (fun z : ℂ => Complex.I * z) (h i)
      have hz : Complex.I * L (graphReal (cayleyMap J) (Yau.stdVec i)) -
          L (graphImag (cayleyMap J) (Yau.stdVec i)) = 0 := by
        simpa only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul,
          mul_zero, sub_eq_add_neg] using hh
      exact (sub_eq_zero.mp hz).symm
    intro v
    obtain ⟨u, hu⟩ := (cayley_graphRealLinear_isInvertible J hi).surjective v
    have hj : J (R u) = R (Complex.I • u) := by
      change J (graphReal (cayleyMap J) u) = graphReal (cayleyMap J) (Complex.I • u)
      rw [structure_graphReal J hi,
        graphReal_I_of_anticommutes _ (cayley_anticommutes J hJ2 hi)]
    rw [← hu, hj]
    exact realLinear_I_of_basis M hI u
  · intro h i
    rw [← structure_graphReal J hi, h]
    rw [← mul_assoc, Complex.I_mul_I]
    ring

theorem dbarA_cayley_eq_zero_iff
    (J : X n → X n →L[ℝ] X n) (x : X n)
    (hJ2 : ∀ v, J x (J x v) = -v) (hi : (J x + stdComplex n).IsInvertible)
    (f : X n → ℂ) :
    (∀ i, dbarA (graphMatrix (fun y => cayleyMap (J y))) i f x = 0) ↔
      (∀ v, fderiv ℝ f x (J x v) = Complex.I * fderiv ℝ f x v) := by
  simp only [dbarA_graphMatrix_eq]
  exact graph_kernel_iff_intertwines (J x) hJ2 hi (fderiv ℝ f x)

end Yau.LeafProofs.L21Aux
