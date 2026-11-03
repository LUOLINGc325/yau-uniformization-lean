import Yau.Proofs.P03NakanoRelativeAlgebra
import Yau.LeafProofs.L17ChartNaturality

open scoped Manifold Matrix ComplexOrder ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L22Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The project's real metric is twice the real part of its Hermitian
matrix. This factor is retained when comparing it with the Levi form. -/
theorem realMetricInChart_eq_two_re_hMat (g : HermitianField M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (v : ComplexVector n) :
    realMetricInChart g a z v v =
      2 * (star (WithLp.ofLp v) ⬝ᵥ (hMat g a z *ᵥ WithLp.ofLp v)).re := by
  have hv : (∑ i, v i • chartVec a (chartInv a z) (stdVec i)) =
      chartVec a (chartInv a z) v := by
    calc
      _ = ∑ i, chartVec a (chartInv a z) (v i • stdVec i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (chartVec_complex_smul _ _ _ _).symm
      _ = chartVec a (chartInv a z) (∑ i, v i • stdVec i) :=
        (chartVec_sum a (chartInv a z) Finset.univ _).symm
      _ = _ := congrArg (chartVec a (chartInv a z)) (L17Aux.complexVector_basis_sum v)
  have hq := L12Aux.hMat_quadratic g a z (WithLp.ofLp v)
  rw [hv] at hq
  rw [realMetricInChart_apply, underlyingRealRiemannianMetric_inner,
    realTangentEquiv_realChartVec a z v hz, ← hq]

/-- A relative lower bound for the actual real metric implies the required
Hermitian matrix lower bound, without losing the project's factor two. -/
theorem leviC_sub_base_metric_posSemidef (g : HermitianField M)
    {f : ComplexVector n → ℝ} (a : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hf : ContDiffAt ℝ 2 f z) (lam : ℝ) (hlam : 0 ≤ lam)
    (hbound : ∀ v : ComplexVector n,
      lam * realMetricInChart g a z v v ≤ complexLeviQuadratic f z v) :
    (leviC f z - (lam : ℂ) • hMat g a z).PosSemidef := by
  apply matrix_sub_real_smul_posSemidef _ _ (leviC_isHermitian hf) (L12Aux.hMat_isHermitian g a z)
  intro v
  have hb := hbound (WithLp.toLp 2 v)
  rw [realMetricInChart_eq_two_re_hMat g a hz, ← leviC_quadratic_re hf] at hb
  simp only [WithLp.ofLp_toLp] at hb
  have hG : 0 ≤ (star v ⬝ᵥ (hMat g a z *ᵥ v)).re :=
    (Complex.nonneg_iff.mp ((L12Aux.hMat_posDef g a z hz).posSemidef.dotProduct_mulVec_nonneg v)).1
  nlinarith [mul_nonneg hlam hG]

end Yau.NodeProofs.P03Aux
