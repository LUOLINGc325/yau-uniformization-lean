import Yau.Proofs.C05CovariantProductLaplacian
import Yau.Proofs.C05RicciInverseTensor

/-! Exact spatial expansion of the inverse energy. Every term apart
from the Hessian square retains an undifferentiated scalar covector. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux Yau.LeafProofs.L19Aux
variable {n r : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem covTensorPair_add_right (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A B C : CovTensor n r) :
    covTensorPair G A (B + C) = covTensorPair G A B + covTensorPair G A C := by
  simp only [covTensorPair, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

def covectorSquare (p : CovTensor n 1) : CovTensor n 2 := tensorConcatProduct p p

theorem inverseEnergy_pair_laplacian (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (C : ComplexVector n → CovTensor n 2)
    (p : ComplexVector n → CovTensor n 1)
    (hC : ∀ v, ContDiffOn ℝ ∞ (fun z => C z v) (chartTarget c))
    (hp : ∀ v, ContDiffOn ℝ ∞ (fun z => p z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    chartRealLaplacian k c
        (fun w => covTensorPair (realMetricFn k c w) (C w) (covectorSquare (p w))) z =
      covTensorPair (realMetricFn k c z) (roughLap k c C z) (covectorSquare (p z)) +
      covTensorPair (realMetricFn k c z) (C z)
        (tensorConcatProduct (roughLap k c p z) (p z)) +
      covTensorPair (realMetricFn k c z) (C z)
        (tensorConcatProduct (p z) (roughLap k c p z)) +
      2 * (∑ i, ∑ j, (realMetricFn k c z)⁻¹ i j *
        covTensorPair (realMetricFn k c z) (C z)
          (tensorConcatProduct (fun u => covariantD k c p z (Fin.cons i u))
            (fun u => covariantD k c p z (Fin.cons j u)))) +
      2 * covTensorPair (realMetricFn k c z) (covariantD k c C z)
        (covariantD k c (fun w => covectorSquare (p w)) z) := by
  have hpp (v : Fin 2 → RIdx n) :
      ContDiffOn ℝ ∞ (fun w => covectorSquare (p w) v) (chartTarget c) :=
    (hp _).mul (hp _)
  have hrough : roughLap k c (fun w => covectorSquare (p w)) z =
      tensorConcatProduct (roughLap k c p z) (p z) +
        tensorConcatProduct (p z) (roughLap k c p z) +
      fun v => 2 * ∑ i, ∑ j, (realMetricFn k c z)⁻¹ i j * tensorConcatProduct
        (fun u => covariantD k c p z (Fin.cons i u))
        (fun u => covariantD k c p z (Fin.cons j u)) v := by
    funext v
    exact roughLap_concatProduct k hk c p p hp hp hz v
  rw [chartTensorPair_laplacian k hk c C _ hC hpp hz, hrough,
    covTensorPair_add_right, covTensorPair_add_right, covTensorPair_mul_right,
    covTensorPair_sum_right]
  simp_rw [covTensorPair_sum_right, covTensorPair_mul_right]
  ring

end Yau.Proofs.C05Aux
