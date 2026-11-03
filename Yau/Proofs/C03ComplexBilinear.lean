import Mathlib

/-! The two actual real directions 1 and I determine the full complex-plane
real Hessian; correcting only its diagonal entries is insufficient. -/

noncomputable section
open scoped Topology

namespace Yau.Proofs.C03Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem real_complex_linear_value (L : ℂ →L[ℝ] E) (z : ℂ) :
    L z = z.re • L 1 + z.im • L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    L z = L (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg L hz
    _ = _ := by rw [map_add, map_smul, map_smul]

theorem real_complex_linear_ext (L K : ℂ →L[ℝ] E)
    (h1 : L 1 = K 1) (hI : L Complex.I = K Complex.I) : L = K := by
  ext z
  rw [real_complex_linear_value L, real_complex_linear_value K, h1, hI]

theorem real_complex_bilinear_ext
    (L K : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (h11 : L 1 1 = K 1 1) (h1I : L 1 Complex.I = K 1 Complex.I)
    (hI1 : L Complex.I 1 = K Complex.I 1)
    (hII : L Complex.I Complex.I = K Complex.I Complex.I) : L = K := by
  apply real_complex_linear_ext
  · exact real_complex_linear_ext _ _ h11 h1I
  · exact real_complex_linear_ext _ _ hI1 hII

theorem real_complex_bilinear_scalar
    (L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (s : ℝ)
    (h11 : L 1 1 = s) (h1I : L 1 Complex.I = 0)
    (hI1 : L Complex.I 1 = 0) (hII : L Complex.I Complex.I = s) :
    L = s • innerSL ℝ := by
  apply real_complex_bilinear_ext
  · change L 1 1 = s * inner ℝ (1 : ℂ) (1 : ℂ)
    simpa using h11
  · change L 1 Complex.I = s * inner ℝ (1 : ℂ) Complex.I
    simpa [real_inner_eq_re_inner ℂ] using h1I
  · change L Complex.I 1 = s * inner ℝ Complex.I (1 : ℂ)
    simpa [real_inner_eq_re_inner ℂ] using hI1
  · change L Complex.I Complex.I = s * inner ℝ Complex.I Complex.I
    simpa using hII

end Yau.Proofs.C03Aux
