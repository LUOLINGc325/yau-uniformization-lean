import Yau.LeafProofs.L21GraphAlgebra

/-! The graph of an almost complex structure in real coordinates.  A Cayley
transform gives its coefficients directly, before constructing any atlas. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def stdComplex (n : ℕ) : X n →L[ℝ] X n :=
  Complex.I • ContinuousLinearMap.id ℝ (X n)

@[simp] theorem stdComplex_apply (v : X n) :
    stdComplex n v = Complex.I • v := rfl

def cayleyMap (J : X n →L[ℝ] X n) : X n →L[ℝ] X n :=
  (J + stdComplex n).inverse.comp (stdComplex n - J)

theorem cayley_relation (J : X n →L[ℝ] X n)
    (h : (J + stdComplex n).IsInvertible) (v : X n) :
    J (cayleyMap J v) + Complex.I • cayleyMap J v = Complex.I • v - J v := by
  have hh := h.self_apply_inverse ((stdComplex n - J) v)
  exact hh

theorem cayley_anticommutes (J : X n →L[ℝ] X n)
    (hJ2 : ∀ v, J (J v) = -v) (h : (J + stdComplex n).IsInvertible)
    (v : X n) :
    cayleyMap J (Complex.I • v) = -Complex.I • cayleyMap J v := by
  have ht := congrArg J (cayley_relation J h v)
  simp only [map_add, map_sub, hJ2] at ht
  apply h.injective
  change J (cayleyMap J (Complex.I • v)) +
      Complex.I • cayleyMap J (Complex.I • v) =
    J (-Complex.I • cayleyMap J v) + Complex.I • (-Complex.I • cayleyMap J v)
  rw [cayley_relation J h]
  simp only [neg_smul, map_neg, smul_neg, smul_smul, Complex.I_mul_I,
    neg_neg, neg_one_smul, one_smul]
  apply sub_eq_zero.mp
  have hz := sub_eq_zero.mpr ht
  convert hz using 1 <;> abel

def graphReal (C : X n →L[ℝ] X n) (v : X n) : X n :=
  (1 / 2 : ℝ) • (v + C v)

def graphImag (C : X n →L[ℝ] X n) (v : X n) : X n :=
  (1 / 2 : ℝ) • (Complex.I • (v - C v))

theorem structure_graphReal (J : X n →L[ℝ] X n)
    (h : (J + stdComplex n).IsInvertible) (v : X n) :
    J (graphReal (cayleyMap J) v) = graphImag (cayleyMap J) v := by
  change J ((1 / 2 : ℝ) • (v + cayleyMap J v)) =
    (1 / 2 : ℝ) • (Complex.I • (v - cayleyMap J v))
  rw [map_smul, map_add]
  congr 1
  rw [smul_sub]
  apply eq_sub_iff_add_eq.mpr
  calc
    J v + J (cayleyMap J v) + Complex.I • cayleyMap J v =
        (J (cayleyMap J v) + Complex.I • cayleyMap J v) + J v := by abel
    _ = Complex.I • v := eq_sub_iff_add_eq.mp (cayley_relation J h v)

theorem structure_graphImag (J : X n →L[ℝ] X n)
    (hJ2 : ∀ v, J (J v) = -v) (h : (J + stdComplex n).IsInvertible)
    (v : X n) :
    J (graphImag (cayleyMap J) v) = -graphReal (cayleyMap J) v := by
  rw [← structure_graphReal J h, hJ2]

theorem graphReal_I_of_anticommutes (C : X n →L[ℝ] X n)
    (hC : ∀ v, C (Complex.I • v) = -Complex.I • C v) (v : X n) :
    graphReal C (Complex.I • v) = graphImag C v := by
  simp only [graphReal, graphImag, hC, neg_smul, smul_sub, smul_add,
    smul_neg, sub_eq_add_neg]

theorem graph_constant_bar_part (C : X n →L[ℝ] X n) (v : X n) :
    graphReal C v - Complex.I • graphImag C v = v := by
  simp only [graphReal, graphImag]
  rw [smul_comm Complex.I (1 / 2 : ℝ)]
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul]
  module

end Yau.LeafProofs.L21Aux
