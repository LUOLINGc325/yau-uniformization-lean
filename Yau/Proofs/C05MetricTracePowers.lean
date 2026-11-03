import Yau.Proofs.C05RicciInverseEnergyChart
import Yau.Proofs.C05RicciSquareTimeEvolution
import Yau.Proofs.G01RawAlgebra

/-! Metric trace powers of the same Ricci endomorphism are independent of
the fixed chart. Their complex and physical real traces have factor two. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Matrix Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem metricMatrix_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G A J : Matrix ι ι ℝ) (hJ : J.det ≠ 0) :
    (Jᵀ * G * J)⁻¹ * (Jᵀ * A * J) = J⁻¹ * (G⁻¹ * A) * J := by
  have hJu := isUnit_iff_ne_zero.mpr hJ
  have hJTu := Matrix.isUnit_det_transpose J hJu
  have hi : (Jᵀ * G * J)⁻¹ * Jᵀ = J⁻¹ * G⁻¹ := by
    rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hJTu,Matrix.mul_one]
  calc
    _ = ((Jᵀ*G*J)⁻¹ * Jᵀ) * A * J := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hi]; simp only [Matrix.mul_assoc]

theorem realMatrix_trace_power_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G A J : Matrix ι ι ℝ) (hJ : J.det ≠ 0) (m : ℕ) :
    (((Jᵀ*G*J)⁻¹ * (Jᵀ*A*J))^m).trace = ((G⁻¹*A)^m).trace := by
  have hJu := isUnit_iff_ne_zero.mpr hJ
  have hJJ := Matrix.mul_nonsing_inv J hJu
  have hIJ := Matrix.nonsing_inv_mul J hJu
  have hp (B : Matrix ι ι ℝ) (m : ℕ) :
      (J⁻¹ * B * J)^m = J⁻¹ * B^m * J := by
    induction m with
    | zero => simp only [pow_zero,Matrix.mul_one,hIJ]
    | succ m ih =>
        rw [pow_succ,ih,pow_succ]
        calc
          _ = J⁻¹ * B^m * (J*J⁻¹) * B * J := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hJJ]; simp only [Matrix.mul_assoc,Matrix.mul_one,Matrix.one_mul]
  rw [metricMatrix_congruence G A J hJ,hp,Matrix.trace_mul_cycle,hJJ,Matrix.one_mul]

theorem rawReal_pow (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    rawReal (A^m) = (rawReal A)^m := by
  induction m with
  | zero => exact rawReal_one
  | succ m ih => rw [pow_succ,rawReal_mul,ih,pow_succ]

def realRicciTracePower (k : HermitianField M) (c : M.Carrier)
    (m : ℕ) (z : ComplexVector n) : ℝ :=
  (((realMetricFn k c z)⁻¹ * Matrix.of (realRicciCoeff k c z))^m).trace

theorem realRicciTracePower_chart_change (k : HermitianField M) (hk : MetricSmooth k)
    (m : ℕ) (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    realRicciTracePower k c m z = realRicciTracePower k d m (realChartChange c d z) := by
  have hJ := Matrix.det_ne_zero_of_left_inverse (realChartJacobian_left_inverse c d hz hy)
  unfold realRicciTracePower
  rw [realMetricFn_chart_change k c d hz hy,realRicciMatrix_chart_change k hk c d hz hy]
  exact realMatrix_trace_power_congruence _ _ _ hJ m

theorem realRicciTracePower_center (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (m : ℕ) (x : M.Carrier) :
    realRicciTracePower k x m (chartPt x x) = 2 * (((gMat k x)⁻¹ * ricci k x)^m).trace.re := by
  have hR : Matrix.of (realRicciCoeff k x (chartPt x x)) = (2:ℝ) • rawReal (ricci k x) := by
    ext a b
    exact Yau.NodeProofs.G04Aux.realRicciCoeff_center_raw k hk hK x a b
  have hGinv : (realMetricFn k x (chartPt x x))⁻¹ = (1/2:ℝ) • rawReal (gMat k x)⁻¹ :=
    realMetricFn_inverse_eq k x _ (mem_extChartAt_target x)
  have hp : (realMetricFn k x (chartPt x x))⁻¹ * Matrix.of (realRicciCoeff k x (chartPt x x)) =
      rawReal ((gMat k x)⁻¹ * ricci k x) := by
    rw [hGinv,hR]
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    norm_num
    exact (rawReal_mul _ _).symm
  unfold realRicciTracePower
  rw [hp,← rawReal_pow,rawReal_trace]

theorem ricciCube_inChart (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    inChart c (ricciCube k) z = (1/2:ℝ) * realRicciTracePower k c 3 z := by
  let d := chartInv c z
  have he := realRicciTracePower_chart_change k hk 3 c d hz (mem_extChartAt_source d)
  change realRicciTracePower k c 3 z = realRicciTracePower k d 3 (chartPt d d) at he
  rw [he,realRicciTracePower_center k hk hK]
  change ricciCube k d = _
  simp only [ricciCube,pow_succ,pow_zero,Matrix.one_mul]
  ring

end Yau.Proofs.C05Aux
