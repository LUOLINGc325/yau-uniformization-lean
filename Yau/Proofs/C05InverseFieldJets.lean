import Yau.Proofs.C05InverseDerivativeWord

/-! Actual covariant jets of the lowered inverse field. Smoothness and
the first-jet budget come from inversion and the genuine two-trace rule. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def inverseFieldJet (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ) :
    (m : ℕ) → ComplexVector n → CovTensor n (2 + m)
  | 0 => fun z => matrixCovTensor (loweredInverseMatrix (realMetricFn k c z) (A z))
  | m + 1 => covariantD k c (inverseFieldJet k c A m)

theorem inverseFieldJet_zero_contDiffOn (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (hA : ∀ a b, ContDiffOn ℝ ∞ (fun z => A z a b) (chartTarget c))
    (hdet : ∀ z ∈ chartTarget c, (A z).det ≠ 0) (v : Fin 2 → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => inverseFieldJet k c A 0 z v) (chartTarget c) := by
  have hInv := Yau.LeafProofs.L12Aux.contDiffOn_matrix_inv hA hdet
  change ContDiffOn ℝ ∞ (fun z => ∑ b : RIdx n,
    (∑ a : RIdx n, realMetricFn k c z (v 0) a * (A z)⁻¹ a b) *
      realMetricFn k c z b (v 1)) (chartTarget c)
  apply ContDiffOn.sum
  intro b _
  apply ContDiffOn.mul _ (hk c b (v 1))
  apply ContDiffOn.sum
  intro a _
  exact (hk c (v 0) a).mul (hInv a b)

theorem inverseFieldJet_contDiffOn (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (hA : ∀ a b, ContDiffOn ℝ ∞ (fun z => A z a b) (chartTarget c))
    (hdet : ∀ z ∈ chartTarget c, (A z).det ≠ 0) (m : ℕ)
    (v : Fin (2 + m) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => inverseFieldJet k c A m z v) (chartTarget c) := by
  induction m with
  | zero => exact inverseFieldJet_zero_contDiffOn k hk c A hA hdet v
  | succ m ih => exact covariantD_contDiffOn k hk c (inverseFieldJet k c A m) ih v

theorem metricTensorNorm_neg (G : Matrix (RIdx n) (RIdx n) ℝ) {r : ℕ} (A : CovTensor n r) :
    metricTensorNorm G (fun v => -A v) = metricTensorNorm G A := by
  have he : (fun v => -A v) = (fun v => (-1 : ℝ) * A v) := by funext v; ring
  rw [he]
  unfold metricTensorNorm
  rw [sqrt_covTensorNormSq_const_mul]
  norm_num

theorem inverseFieldJet_one_word (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hA : ∀ a b, DifferentiableAt ℝ (fun w => A w a b) z)
    (hdet : (A z).det ≠ 0) :
    inverseFieldJet k c A 1 z = fun v =>
      -inverseCompositionWord.eval (realMetricFn k c z)⁻¹
        (tensorConcatProduct (inverseFieldJet k c A 0 z) (inverseFieldJet k c A 0 z))
        (covariantD k c (fun w => matrixCovTensor (A w)) z) v := by
  funext v
  exact covariantD_loweredInverse_word k hk c A hz hA hdet v

theorem inverseFieldJet_one_norm_le (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hA : ∀ a b, DifferentiableAt ℝ (fun w => A w a b) z)
    (hdet : (A z).det ≠ 0) :
    let G := realMetricFn k c z
    metricTensorNorm G (inverseFieldJet k c A 1 z) ≤
      (2 * n : ℕ) * metricTensorNorm G (inverseFieldJet k c A 0 z) ^ 2 *
        metricTensorNorm G (covariantD k c (fun w => matrixCovTensor (A w)) z) := by
  dsimp only
  let G := realMetricFn k c z
  have hG := Yau.LeafProofs.L12Aux.realMetricFn_posDef k c z hz
  rw [inverseFieldJet_one_word k hk c A hz hA hdet, metricTensorNorm_neg]
  have hh := inverseCompositionWord.eval_norm_le G hG
    (tensorConcatProduct (inverseFieldJet k c A 0 z) (inverseFieldJet k c A 0 z))
    (covariantD k c (fun w => matrixCovTensor (A w)) z)
  change metricTensorNorm G _ ≤ _ at hh
  change metricTensorNorm G _ ≤ _
  apply hh.trans_eq
  change ((2 * n : ℕ) : ℝ) * metricTensorNorm G
      (tensorConcatProduct (inverseFieldJet k c A 0 z) (inverseFieldJet k c A 0 z)) *
        metricTensorNorm G (covariantD k c (fun w => matrixCovTensor (A w)) z) = _
  rw [metricTensorNorm_concatProduct G hG, pow_two]

end Yau.Proofs.C05Aux
