import Yau.Proofs.C05IntrinsicTensorNorm

/-! A quantitative spatial inverse-energy error. Its right side
vanishes with the undifferentiated scalar covector. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def inverseEnergySpatialRemainder (k : HermitianField M) (c : M.Carrier)
    (C : ComplexVector n → CovTensor n 2) (p : ComplexVector n → CovTensor n 1)
    (z : ComplexVector n) : ℝ :=
  chartRealLaplacian k c
      (fun w => covTensorPair (realMetricFn k c w) (C w) (covectorSquare (p w))) z -
    2 * (∑ i, ∑ j, (realMetricFn k c z)⁻¹ i j *
      covTensorPair (realMetricFn k c z) (C z)
        (tensorConcatProduct (fun u => covariantD k c p z (Fin.cons i u))
          (fun u => covariantD k c p z (Fin.cons j u))))

theorem inverseEnergySpatialRemainder_eq (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (C : ComplexVector n → CovTensor n 2)
    (p : ComplexVector n → CovTensor n 1)
    (hC : ∀ v, ContDiffOn ℝ ∞ (fun z => C z v) (chartTarget c))
    (hp : ∀ v, ContDiffOn ℝ ∞ (fun z => p z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    inverseEnergySpatialRemainder k c C p z =
      covTensorPair (realMetricFn k c z) (roughLap k c C z) (covectorSquare (p z)) +
      covTensorPair (realMetricFn k c z) (C z)
        (tensorConcatProduct (roughLap k c p z) (p z)) +
      covTensorPair (realMetricFn k c z) (C z)
        (tensorConcatProduct (p z) (roughLap k c p z)) +
      2 * covTensorPair (realMetricFn k c z) (covariantD k c C z)
        (covariantD k c (fun w => covectorSquare (p w)) z) := by
  unfold inverseEnergySpatialRemainder
  rw [inverseEnergy_pair_laplacian k hk c C p hC hp hz]
  ring

theorem inverseEnergySpatialRemainder_abs_le (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (C : ComplexVector n → CovTensor n 2)
    (p : ComplexVector n → CovTensor n 1)
    (hC : ∀ v, ContDiffOn ℝ ∞ (fun z => C z v) (chartTarget c))
    (hp : ∀ v, ContDiffOn ℝ ∞ (fun z => p z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    let G := realMetricFn k c z
    |inverseEnergySpatialRemainder k c C p z| ≤
      Real.sqrt (2 * n : ℕ) * metricTensorNorm G (covariantD k c (covariantD k c C) z) *
        metricTensorNorm G (p z) ^ 2 +
      2 * metricTensorNorm G (C z) * Real.sqrt (2 * n : ℕ) *
        metricTensorNorm G (covariantD k c (covariantD k c p) z) * metricTensorNorm G (p z) +
      4 * metricTensorNorm G (covariantD k c C z) *
        metricTensorNorm G (covariantD k c p z) * metricTensorNorm G (p z) := by
  let G := realMetricFn k c z
  have hG : G.PosDef := Yau.LeafProofs.L12Aux.realMetricFn_posDef k c z hz
  let a := covTensorPair G (roughLap k c C z) (covectorSquare (p z))
  let b := covTensorPair G (C z) (tensorConcatProduct (roughLap k c p z) (p z))
  let d := covTensorPair G (C z) (tensorConcatProduct (p z) (roughLap k c p z))
  let e := covTensorPair G (covariantD k c C z)
    (covariantD k c (fun w => covectorSquare (p w)) z)
  have heq : inverseEnergySpatialRemainder k c C p z = a + b + d + 2 * e :=
    inverseEnergySpatialRemainder_eq k hk c C p hC hp hz
  have hnp : 0 ≤ metricTensorNorm G (p z) := metricTensorNorm_nonneg G _
  have hnC : 0 ≤ metricTensorNorm G (C z) := metricTensorNorm_nonneg G _
  have hnDC : 0 ≤ metricTensorNorm G (covariantD k c C z) := metricTensorNorm_nonneg G _
  have hroughC := metricTensorNorm_roughLap_le k c C hz
  have hroughp := metricTensorNorm_roughLap_le k c p hz
  have ha : |a| ≤ Real.sqrt (2 * n : ℕ) *
      metricTensorNorm G (covariantD k c (covariantD k c C) z) * metricTensorNorm G (p z) ^ 2 := by
    have hh := covTensorPair_abs_le_norm G hG (roughLap k c C z) (covectorSquare (p z))
    rw [metricTensorNorm_covectorSquare G hG] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hroughC (sq_nonneg _))
  have hb : |b| ≤ metricTensorNorm G (C z) *
      (Real.sqrt (2 * n : ℕ) * metricTensorNorm G
        (covariantD k c (covariantD k c p) z) * metricTensorNorm G (p z)) := by
    have hh := covTensorPair_abs_le_norm G hG (C z)
      (tensorConcatProduct (roughLap k c p z) (p z))
    rw [metricTensorNorm_concatProduct G hG] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hroughp hnp) hnC)
  have hd : |d| ≤ metricTensorNorm G (C z) *
      (Real.sqrt (2 * n : ℕ) * metricTensorNorm G
        (covariantD k c (covariantD k c p) z) * metricTensorNorm G (p z)) := by
    have hh := covTensorPair_abs_le_norm G hG (C z)
      (tensorConcatProduct (p z) (roughLap k c p z))
    rw [metricTensorNorm_concatProduct G hG] at hh
    have hh' := hh.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hroughp hnp) hnC)
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hh'
  have hpAt (v : Fin 1 → RIdx n) := ((hp v).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have he : |e| ≤ metricTensorNorm G (covariantD k c C z) *
      (2 * metricTensorNorm G (covariantD k c p z) * metricTensorNorm G (p z)) := by
    exact (covTensorPair_abs_le_norm G hG _ _).trans
      (mul_le_mul_of_nonneg_left (metricTensorNorm_covariantD_square_le k c p z G hG hpAt) hnDC)
  have hab := abs_add_le a b
  have habd := abs_add_le (a + b) d
  have habde := abs_add_le (a + b + d) (2 * e)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habde
  rw [heq]
  dsimp only
  nlinarith

end Yau.Proofs.C05Aux
