import Yau.LeafProofs.L18

noncomputable section

open scoped Topology ContDiff Manifold Matrix ComplexOrder
open Filter

namespace Yau.LeafProofs.L22Aux

/-- The actual real Hessian trace on a complex line, with the Wirtinger normalization. -/
def complexLeviQuadratic {n : ℕ} (f : ComplexVector n → ℝ)
    (z v : ComplexVector n) : ℝ :=
  (fderiv ℝ (fderiv ℝ f) z v v +
    fderiv ℝ (fderiv ℝ f) z (Complex.I • v) (Complex.I • v)) / 4

/-- The actual nested Wirtinger matrix of a real C² function is Hermitian. -/
theorem leviC_isHermitian {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) : (leviC f z).IsHermitian := by
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  apply Matrix.IsHermitian.ext
  intro i j
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re, leviC,
      (L18Aux.leviMatrix_entry_re_im hf stdVec j i).1,
      (L18Aux.leviMatrix_entry_re_im hf stdVec i j).1]
    rw [hs (stdVec i) (stdVec j), hs (Complex.I • stdVec i) (Complex.I • stdVec j)]
  · simp only [Complex.star_def, Complex.conj_im, leviC,
      (L18Aux.leviMatrix_entry_re_im hf stdVec j i).2,
      (L18Aux.leviMatrix_entry_re_im hf stdVec i j).2]
    rw [hs (stdVec i) (Complex.I • stdVec j), hs (Complex.I • stdVec i) (stdVec j)]
    ring

/-- Real part of the matrix quadratic form, expanded in the actual real coordinate basis. -/
theorem leviC_quadratic_re {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (v : ComplexVector n) :
    (star (WithLp.ofLp v) ⬝ᵥ (leviC f z *ᵥ WithLp.ofLp v)).re =
      complexLeviQuadratic f z v := by
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  have hre (i j : Fin n) := (L18Aux.leviMatrix_entry_re_im hf stdVec i j).1
  have him (i j : Fin n) := (L18Aux.leviMatrix_entry_re_im hf stdVec i j).2
  unfold complexLeviQuadratic
  rw [L12Aux.realBilin_eq_sum (fderiv ℝ (fderiv ℝ f) z) v v,
    L12Aux.realBilin_eq_sum (fderiv ℝ (fderiv ℝ f) z) (Complex.I • v) (Complex.I • v)]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum,
    Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, leviC, hre, him,
    Fintype.sum_prod_type, Fin.sum_univ_two, realCoord, realVec,
    PiLp.smul_apply, smul_eq_mul, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
    neg_mul, mul_neg, neg_neg, ite_true, one_ne_zero, ite_false,
    one_smul]
  simp only [← Finset.sum_add_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs (stdVec j) (stdVec i), hs (Complex.I • stdVec j) (Complex.I • stdVec i),
    hs (stdVec j) (Complex.I • stdVec i), hs (Complex.I • stdVec j) (stdVec i)]
  dsimp only [stdVec]
  ring

/-- The matrix value itself is the real line-Hessian trace. -/
theorem leviC_quadratic {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (v : ComplexVector n) :
    star (WithLp.ofLp v) ⬝ᵥ (leviC f z *ᵥ WithLp.ofLp v) =
      (complexLeviQuadratic f z v : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using leviC_quadratic_re hf v
  · have h := congrArg Complex.im
      ((leviC_isHermitian hf).star_dotProduct_mulVec_comm (WithLp.ofLp v) (WithLp.ofLp v))
    simp only [Complex.star_def, Complex.conj_im] at h
    simpa only [Complex.ofReal_im] using (show
      (star (WithLp.ofLp v) ⬝ᵥ (leviC f z *ᵥ WithLp.ofLp v)).im = 0 by linarith)

/-- Semidefiniteness in the project's original matrix definition. -/
theorem leviC_posSemidef_iff {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) :
    (leviC f z).PosSemidef ↔ ∀ v, 0 ≤ complexLeviQuadratic f z v := by
  constructor
  · intro h v
    have hh := h.dotProduct_mulVec_nonneg (WithLp.ofLp v)
    rw [leviC_quadratic hf v] at hh
    exact Complex.zero_le_real.mp hh
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (leviC_isHermitian hf)
    intro v
    have hh := leviC_quadratic hf (WithLp.toLp 2 v)
    simpa only [WithLp.ofLp_toLp] using hh.symm ▸ (Complex.zero_le_real.mpr (h _))

/-- Strict definiteness, valid also in complex dimension zero. -/
theorem leviC_posDef_iff {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) :
    (leviC f z).PosDef ↔ ∀ v, v ≠ 0 → 0 < complexLeviQuadratic f z v := by
  constructor
  · intro h v hv
    have hv' : WithLp.ofLp v ≠ 0 := by
      intro hzero
      apply hv
      simpa using congrArg (WithLp.toLp 2) hzero
    have hh := h.dotProduct_mulVec_pos hv'
    rw [leviC_quadratic hf v] at hh
    exact Complex.zero_lt_real.mp hh
  · intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (leviC_isHermitian hf)
    intro v hv
    have hv' : (WithLp.toLp 2 v : ComplexVector n) ≠ 0 := by
      intro hzero
      apply hv
      simpa using congrArg WithLp.ofLp hzero
    have hh := leviC_quadratic hf (WithLp.toLp 2 v)
    simpa only [WithLp.ofLp_toLp] using hh.symm ▸ (Complex.zero_lt_real.mpr (h _ hv'))

end Yau.LeafProofs.L22Aux
