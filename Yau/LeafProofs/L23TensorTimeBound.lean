import Yau.LeafProofs.L23TensorMixedMetric
import Yau.LeafProofs.L23TensorTimeCalculus
import Yau.LeafProofs.L23CurvatureCalculus

/-! The moving-metric contribution to a tensor norm has a uniform rank bound. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

theorem matrix_posSemidef_sub_of_quadratic_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G R : Matrix ι ι ℝ) (c : ℝ) (hG : G.IsSymm) (hR : R.IsSymm)
    (hq : ∀ V : ι → ℝ, V ⬝ᵥ (R *ᵥ V) ≤ c*(V ⬝ᵥ (G *ᵥ V))) :
    (c•G-R).PosSemidef := by
  have hHerm : (c•G-R).IsHermitian := by
    change (c•G-R)ᴴ=c•G-R
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    change c*G j i-R j i=c*G i j-R i j
    rw [hG.apply i j,hR.apply i j]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro V
  simpa only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,
    dotProduct_smul,smul_eq_mul] using sub_nonneg.mpr (hq V)

theorem matrix_inverse_dominance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G R : Matrix ι ι ℝ) (hG : G.PosDef) (c : ℝ)
    (hc : (c•G-R).PosSemidef) :
    (c•G⁻¹-(G⁻¹*R)*G⁻¹).PosSemidef := by
  let H := G⁻¹
  have hHsym : Hᵀ=H := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hG.inv.isHermitian.eq
  have hHG : H*G=1 := Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hG.det_pos.ne')
  have hm : Hᴴ*(c•G-R)*H=c•H-(H*R)*H := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,hHsym]
    calc
      _ = c•((H*G)*H)-(H*R)*H := by
        simp only [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]
      _ = _ := by rw [hHG,Matrix.one_mul]
  have hh := hc.conjTranspose_mul_mul_same H
  rwa [hm] at hh

variable {n : ℕ} {M : ComplexManifold n}

def chartRealRicciMatrix (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    Matrix (RIdx n) (RIdx n) ℝ := fun i j => realRicciCoeff h x z i j

theorem chartRealRicciMatrix_isSymm (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    (chartRealRicciMatrix h x z).IsSymm := by
  change (chartRealRicciMatrix h x z)ᵀ=chartRealRicciMatrix h x z
  ext i j
  change realRicciCoeff h x z j i=realRicciCoeff h x z i j
  rw [realRicciCoeff_eq_realRicciMatrix h x z hz,realRicciCoeff_eq_realRicciMatrix h x z hz]
  exact realRicciMatrix_symm h hh x z hz j i

theorem chartRealRicciMatrix_dominance (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    (((2*n : ℕ)*Real.sqrt (covTensorNormSq (realMetricFn h x z) (rmTensor h x z)))•
      realMetricFn h x z-chartRealRicciMatrix h x z).PosSemidef := by
  apply matrix_posSemidef_sub_of_quadratic_le _ _ _
    (L18Aux.realMetricFn_isSymm h x z) (chartRealRicciMatrix_isSymm h hh x hz)
  intro V
  have hb := realRicciCoeff_quadratic_abs_le h x z hz V
  have heq : (∑ i, ∑ j, realRicciCoeff h x z i j*V i*V j) =
      V ⬝ᵥ (chartRealRicciMatrix h x z *ᵥ V) := by
    simp only [dotProduct,Matrix.mulVec,chartRealRicciMatrix,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq] at hb
  exact (le_abs_self _).trans hb

theorem ricci_tensorMetricVariation_le {r : ℕ} (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (σ : ℝ) (hσ : 0 ≤ σ) (A : CovTensor n r) :
    tensorMetricVariation (realMetricFn h x z)⁻¹
      (σ•(((realMetricFn h x z)⁻¹*chartRealRicciMatrix h x z)*(realMetricFn h x z)⁻¹)) A A ≤
      σ*(r : ℝ)*(2*n : ℕ)*Real.sqrt (covTensorNormSq (realMetricFn h x z) (rmTensor h x z))*
        covTensorNormSq (realMetricFn h x z) A := by
  let G := realMetricFn h x z
  let H := G⁻¹
  let R := chartRealRicciMatrix h x z
  let c : ℝ := (2*n : ℕ)*Real.sqrt (covTensorNormSq G (rmTensor h x z))
  have hG := L12Aux.realMetricFn_posDef h x z hz
  have hbound := tensorConnectionAction_contraction_le H (H*R) c hG.inv.posSemidef
    (matrix_inverse_dominance G R hG c (chartRealRicciMatrix_dominance h hh x hz)) A
  rw [tensorMetricVariation_scaled_action]
  have hb := mul_le_mul_of_nonneg_left hbound hσ
  change σ*tensorContraction H (tensorConnectionAction (H*R) A) A ≤ _
  change σ*tensorContraction H (tensorConnectionAction (H*R) A) A ≤
    σ*((r : ℝ)*c*tensorContraction H A A) at hb
  dsimp only [c,H,G] at hb
  change σ*tensorContraction (realMetricFn h x z)⁻¹
    (tensorConnectionAction ((realMetricFn h x z)⁻¹*R) A) A ≤ _
  simpa only [tensorContraction,covTensorNormSq,mul_assoc] using hb

end Yau.LeafProofs.L23Aux
