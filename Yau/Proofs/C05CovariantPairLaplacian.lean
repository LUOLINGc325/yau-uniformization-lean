import Yau.LeafProofs.L23TensorLaplacian

/-! Product rules for the actual metric tensor pairing, including the
connection on the derivative slots. -/

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux Yau.LeafProofs.L19Aux
variable {n r : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem covTensorPair_sum_left {κ : Type*} [Fintype κ]
    (G : Matrix (RIdx n) (RIdx n) ℝ) (A : κ → CovTensor n r) (B : CovTensor n r) :
    covTensorPair G (fun v => ∑ k, A k v) B = ∑ k, covTensorPair G (A k) B := by
  unfold covTensorPair
  simp only [Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext v
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem chartTensorPair_covHessian (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A B : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j : RIdx n) :
    chartCovHessian k c (fun w => covTensorPair (realMetricFn k c w) (A w) (B w)) z i j =
      covTensorPair (realMetricFn k c z)
        (fun v => covariantD k c A z (Fin.cons i v))
        (fun v => covariantD k c B z (Fin.cons j v)) +
      covTensorPair (realMetricFn k c z)
        (fun v => covariantD k c A z (Fin.cons j v))
        (fun v => covariantD k c B z (Fin.cons i v)) +
      covTensorPair (realMetricFn k c z)
        (fun v => covariantD k c (covariantD k c A) z (Fin.cons i (Fin.cons j v))) (B z) +
      covTensorPair (realMetricFn k c z) (A z)
        (fun v => covariantD k c (covariantD k c B) z (Fin.cons i (Fin.cons j v))) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  let Aj := fun w v => covariantD k c A w (Fin.cons j v)
  let Bj := fun w v => covariantD k c B w (Fin.cons j v)
  have hAj (v : Fin r → RIdx n) := covariantD_contDiffOn k hk c A hA (Fin.cons j v)
  have hBj (v : Fin r → RIdx n) := covariantD_contDiffOn k hk c B hB (Fin.cons j v)
  have he : (fun w => rDeriv
      (fun u => covTensorPair (realMetricFn k c u) (A u) (B u)) w j) =ᶠ[𝓝 z]
      (fun w => covTensorPair (realMetricFn k c w) (Aj w) (B w) +
        covTensorPair (realMetricFn k c w) (A w) (Bj w)) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact rDeriv_covTensorPair k hk c A B hA hB hw j
  have hd₁ := ((chartTensorPair_contDiffOn k hk c Aj B hAj hB).contDiffAt
    (hO.mem_nhds hz)).differentiableAt (by simp)
  have hd₂ := ((chartTensorPair_contDiffOn k hk c A Bj hA hBj).contDiffAt
    (hO.mem_nhds hz)).differentiableAt (by simp)
  have hsecond := congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec i)) he.fderiv_eq
  change rDeriv (fun w => rDeriv
      (fun u => covTensorPair (realMetricFn k c u) (A u) (B u)) w j) z i =
    rDeriv (fun w => covTensorPair (realMetricFn k c w) (Aj w) (B w) +
      covTensorPair (realMetricFn k c w) (A w) (Bj w)) z i at hsecond
  rw [rDeriv_add hd₁ hd₂, rDeriv_covTensorPair k hk c Aj B hAj hB hz i,
    rDeriv_covTensorPair k hk c A Bj hA hBj hz i] at hsecond
  have hsplitA : (fun v => covariantD k c (covariantD k c A) z (Fin.cons i (Fin.cons j v))) =
      (fun v => covariantD k c Aj z (Fin.cons i v) -
        ∑ b, christoffel k c z b i j * covariantD k c A z (Fin.cons b v)) := by
    funext v
    exact covariantD_twice_cons_split k c A z i j v
  have hsplitB : (fun v => covariantD k c (covariantD k c B) z (Fin.cons i (Fin.cons j v))) =
      (fun v => covariantD k c Bj z (Fin.cons i v) -
        ∑ b, christoffel k c z b i j * covariantD k c B z (Fin.cons b v)) := by
    funext v
    exact covariantD_twice_cons_split k c B z i j v
  unfold chartCovHessian
  rw [hsecond, hsplitA, hsplitB, covTensorPair_sub_left,
    covTensorPair_sub_right, covTensorPair_sum_left, covTensorPair_sum_right]
  simp_rw [covTensorPair_mul_left, covTensorPair_mul_right,
    rDeriv_covTensorPair k hk c A B hA hB hz]
  simp only [mul_add, Finset.sum_add_distrib]
  dsimp only [Aj, Bj]
  ring

theorem chartTensorPair_laplacian (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A B : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    chartRealLaplacian k c (fun w => covTensorPair (realMetricFn k c w) (A w) (B w)) z =
      covTensorPair (realMetricFn k c z) (roughLap k c A z) (B z) +
      covTensorPair (realMetricFn k c z) (A z) (roughLap k c B z) +
      2 * covTensorPair (realMetricFn k c z) (covariantD k c A z) (covariantD k c B z) := by
  let G := realMetricFn k c z
  have hcross : (∑ i, ∑ j, G⁻¹ i j *
      covTensorPair G (fun v => covariantD k c A z (Fin.cons j v))
        (fun v => covariantD k c B z (Fin.cons i v))) =
      covTensorPair G (covariantD k c A z) (covariantD k c B z) := by
    rw [covTensorPair_succ, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [(Yau.LeafProofs.L18Aux.realMetricFn_isSymm k c z).inv.apply i j]
  have hroughA : covTensorPair G (roughLap k c A z) (B z) =
      ∑ i, ∑ j, G⁻¹ i j * covTensorPair G
        (fun v => covariantD k c (covariantD k c A) z (Fin.cons i (Fin.cons j v))) (B z) := by
    unfold roughLap
    rw [covTensorPair_sum_left]
    simp_rw [covTensorPair_sum_left, covTensorPair_mul_left]
    rfl
  have hroughB : covTensorPair G (A z) (roughLap k c B z) =
      ∑ i, ∑ j, G⁻¹ i j * covTensorPair G (A z)
        (fun v => covariantD k c (covariantD k c B) z (Fin.cons i (Fin.cons j v))) := by
    unfold roughLap
    rw [covTensorPair_sum_right]
    simp_rw [covTensorPair_sum_right, covTensorPair_mul_right]
    rfl
  unfold chartRealLaplacian
  simp_rw [chartTensorPair_covHessian k hk c A B hA hB hz]
  simp only [mul_add, Finset.sum_add_distrib]
  change _ + _ + _ + _ = _
  rw [← covTensorPair_succ, hcross, ← hroughA, ← hroughB]
  ring

end Yau.Proofs.C05Aux
