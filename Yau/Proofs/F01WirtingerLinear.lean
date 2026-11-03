import spec.CHAIN.CONTRACTS

/-! The genuine unbarred Wirtinger differential is complex linear in its
vector argument, including when the underlying function is only real smooth. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem realCLM_complex_smul (D : E →L[ℝ] ℂ) (a : ℂ) (v : E) :
    D (a • v) = (a.re : ℂ) * D v + (a.im : ℂ) * D (Complex.I • v) := by
  have ha : a • v = a.re • v + a.im • (Complex.I • v) := by
    conv_lhs => rw [← a.re_add_im]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [ha, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

def wirtingerLinear (D : E →L[ℝ] ℂ) : E →ₗ[ℂ] ℂ where
  toFun v := (1 / 2 : ℂ) * (D v - Complex.I * D (Complex.I • v))
  map_add' v w := by simp only [smul_add, map_add]; ring
  map_smul' a v := by
    change (1 / 2 : ℂ) * (D (a • v) - Complex.I * D (Complex.I • (a • v))) =
      a * ((1 / 2 : ℂ) * (D v - Complex.I * D (Complex.I • v)))
    rw [smul_comm Complex.I a, realCLM_complex_smul D a v,
      realCLM_complex_smul D a (Complex.I • v)]
    simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
    conv_rhs => rw [← a.re_add_im]
    ring_nf
    simp only [Complex.I_sq]
    ring

theorem wirtingerLinear_apply (F : E → ℂ) (z v : E) :
    wirtingerLinear (fderiv ℝ F z) v = wirt F z v := rfl

theorem wirt_eq_coordinate_contraction {n : ℕ} (F : ComplexVector n → ℂ)
    (z v : ComplexVector n) :
    wirt F z v = (fun i => wirt F z (stdVec i)) ⬝ᵥ WithLp.ofLp v := by
  have hv : v = ∑ i, v i • stdVec i := by
    ext j
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  change wirtingerLinear (fderiv ℝ F z) v = _
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

end Yau.NodeProofs.F01Aux
