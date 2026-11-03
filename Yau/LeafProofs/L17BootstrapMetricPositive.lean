import Yau.LeafProofs.L17BootstrapPositiveBaseHolder

noncomputable section
open Set Metric
open scoped Matrix Topology ComplexOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux
local instance metricPositiveMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

/-- Frobenius control bounds the actual complex quadratic form, including dimension zero. -/
theorem frobenius_quadratic_norm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (v : ComplexVector n) :
    ‖star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)‖≤‖A‖*‖v‖^2 := by
  let R : Matrix Unit (Fin n) ℂ := Matrix.replicateRow Unit (star (WithLp.ofLp v))
  let C : Matrix (Fin n) Unit ℂ := Matrix.replicateCol Unit (WithLp.ofLp v)
  have hForm : R*A*C=Matrix.replicateRow Unit
      (fun _ : Unit => star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)) := by
    ext i j
    simp only [R,C,Matrix.mul_apply,Matrix.replicateRow_apply,Matrix.replicateCol_apply,
      dotProduct,Matrix.mulVec]
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  have hNorm : ‖R*A*C‖=‖star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)‖ := by
    rw [hForm,Matrix.frobenius_norm_def]
    simp only [Matrix.replicateRow_apply,Fintype.sum_unique]
    rw [←Real.sqrt_eq_rpow,Real.rpow_two]
    exact Real.sqrt_sq (norm_nonneg (star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)))
  have hR : ‖R‖=‖v‖ := by
    rw [Matrix.frobenius_norm_replicateRow]
    rw [PiLp.norm_eq_of_L2,PiLp.norm_eq_of_L2]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    change ‖star (v i)‖^2=‖v i‖^2
    rw [norm_star]
  have hC : ‖C‖=‖v‖ := Matrix.frobenius_norm_replicateCol _
  rw [←hNorm]
  exact ((Matrix.frobenius_norm_mul (R*A) C).trans
    (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul R A) (norm_nonneg C))).trans_eq
      (by rw [hR,hC];ring)

theorem matrix_posDef_of_uniform_lower_and_norm_close {n : ℕ}
    {A H : Matrix (Fin n) (Fin n) ℂ} {lambda : ℝ} (hlambda : 0<lambda)
    (hA : (A-(lambda : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef)
    (hH : H.IsHermitian) (hClose : ‖H-A‖≤lambda/2) : H.PosDef := by
  have hAPos := L17BootstrapInverseHolderAux.matrix_posDef_of_uniform_lower hlambda hA
  have hLower (v : ComplexVector n) :
      lambda*‖v‖^2≤(star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)).re := by
    have h := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg (WithLp.ofLp v))).1
    simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,
      dotProduct_smul,smul_eq_mul,complex_quadratic_one,Complex.sub_re,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h
    linarith
  have hError (v : ComplexVector n) :
      |(star (WithLp.ofLp v) ⬝ᵥ ((H-A) *ᵥ WithLp.ofLp v)).re|≤‖H-A‖*‖v‖^2 :=
    (Complex.abs_re_le_norm _).trans (frobenius_quadratic_norm_le (H-A) v)
  have h := matrix_half_double_comparison hlambda hAPos (hH.sub hAPos.isHermitian)
    hLower hError hClose
  simpa only [add_sub_cancel] using h.1

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T gamma : ℝ)

theorem local_metric_posDef_of_norm_close
    (A H : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    {lambda : ℝ} (hlambda : 0<lambda)
    (hA : ∀ q : LocalCylinder P T,
      (A q-(lambda : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef)
    (hH : ∀ q : LocalCylinder P T, (H q).IsHermitian) (hClose : ‖H-A‖≤lambda)
    (q : LocalCylinder P T) : (H q).PosDef := by
  apply matrix_posDef_of_uniform_lower_and_norm_close hlambda (hA q) (hH q)
  have hEval := (localValue_norm_le _ (H-A).value q).trans
    (norm_value_le_half _ P T gamma (H-A))
  change ‖H q-A q‖≤_ at hEval
  exact hEval.trans (by nlinarith)

end Yau.LeafProofs.L17BootstrapMetricAux
