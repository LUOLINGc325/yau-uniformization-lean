import Yau.Geometry.Basic

noncomputable section

namespace Yau.NodeProofs.P03Aux

theorem real_finrank_complexVector (n : ℕ) :
    Module.finrank ℝ (ComplexVector n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (ComplexVector n)]
  simp only [Complex.finrank_real_complex, ComplexVector, finrank_euclideanSpace_fin]

theorem field_span_dimension_bound {n : ℕ} (hn : 0 < n) :
    Module.finrank ℝ (ComplexVector n) + (n - 1) * 2 < (2 * n) * 2 := by
  rw [real_finrank_complexVector]
  omega

theorem scalar_immersion_dimension_bound {n : ℕ} (hn : 0 < n) :
    Module.finrank ℝ (ComplexVector n) + (n - 1) * 2 < (2 * n + 1) * 2 := by
  rw [real_finrank_complexVector]
  omega

theorem scalar_pair_dimension_bound (n : ℕ) :
    Module.finrank ℝ (ComplexVector n × ComplexVector n) < (2 * n + 1) * 2 := by
  rw [Module.finrank_prod, real_finrank_complexVector]
  omega

end Yau.NodeProofs.P03Aux
