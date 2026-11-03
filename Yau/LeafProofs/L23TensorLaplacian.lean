import Yau.LeafProofs.L23TensorKato

/-! The rough-Laplacian identity for the original tensor norm. -/

noncomputable section
open Filter
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
open L18Aux L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ} {M : ComplexManifold n}

theorem covTensorPair_sum_right {κ : Type*} [Fintype κ]
    (G : Matrix (RIdx n) (RIdx n) ℝ) (A : CovTensor n r) (B : κ → CovTensor n r) :
    covTensorPair G A (fun v => ∑ k, B k v) = ∑ k, covTensorPair G A (B k) := by
  unfold covTensorPair
  simp only [Finset.mul_sum,Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext v
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem chartTensorPair_contDiffOn (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A B : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c)) :
    ContDiffOn ℝ ∞ (fun z => covTensorPair (realMetricFn h c z) (A z) (B z)) (chartTarget c) := by
  apply ContDiffOn.sum
  intro v _
  apply ContDiffOn.sum
  intro w _
  apply ((hA v).mul (hB w)).mul
  apply contDiffOn_prod
  intro j _
  exact realMetricFn_inverse_contDiffOn h hh c (v j) (w j)

theorem chartTensorNormSq_covHessian (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j : RIdx n) :
    chartCovHessian h c (fun w => covTensorNormSq (realMetricFn h c w) (A w)) z i j =
      2*covTensorPair (realMetricFn h c z)
        (fun v => covariantD h c A z (Fin.cons i v))
        (fun v => covariantD h c A z (Fin.cons j v))+
      2*covTensorPair (realMetricFn h c z) (A z)
        (fun v => covariantD h c (covariantD h c A) z (Fin.cons i (Fin.cons j v))) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  let B := fun w v => covariantD h c A w (Fin.cons j v)
  have hB (v : Fin r → RIdx n) := covariantD_contDiffOn h hh c A hA (Fin.cons j v)
  have heq : (fun w => rDeriv
      (fun u => covTensorNormSq (realMetricFn h c u) (A u)) w j) =ᶠ[𝓝 z]
      (fun w => 2*covTensorPair (realMetricFn h c w) (A w) (B w)) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact rDeriv_covTensorNormSq h hh c A hA hw j
  have hp := ((chartTensorPair_contDiffOn h hh c A B hA hB).contDiffAt
    (hO.mem_nhds hz)).differentiableAt (by simp)
  have hsecond := congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec i)) heq.fderiv_eq
  change rDeriv (fun w => rDeriv
      (fun u => covTensorNormSq (realMetricFn h c u) (A u)) w j) z i =
    rDeriv (fun w => 2*covTensorPair (realMetricFn h c w) (A w) (B w)) z i at hsecond
  rw [rDeriv_const_mul hp 2 i,rDeriv_covTensorPair h hh c A B hA hB hz i] at hsecond
  have hsplit : (fun v => covariantD h c (covariantD h c A) z (Fin.cons i (Fin.cons j v))) =
      (fun v => covariantD h c B z (Fin.cons i v)-
        ∑ b, christoffel h c z b i j*covariantD h c A z (Fin.cons b v)) := by
    funext v
    exact covariantD_twice_cons_split h c A z i j v
  have hsplitPair : covTensorPair (realMetricFn h c z) (A z)
      (fun v => covariantD h c (covariantD h c A) z (Fin.cons i (Fin.cons j v))) =
      covTensorPair (realMetricFn h c z) (A z) (fun v => covariantD h c B z (Fin.cons i v))-
        ∑ b, christoffel h c z b i j*covTensorPair (realMetricFn h c z) (A z)
          (fun v => covariantD h c A z (Fin.cons b v)) := by
    rw [hsplit,covTensorPair_sub_right,covTensorPair_sum_right]
    simp_rw [covTensorPair_mul_right]
  have hscale : (∑ b, christoffel h c z b i j*
      (2*covTensorPair (realMetricFn h c z) (A z)
        (fun v => covariantD h c A z (Fin.cons b v)))) =
      2*(∑ b, christoffel h c z b i j*covTensorPair (realMetricFn h c z) (A z)
        (fun v => covariantD h c A z (Fin.cons b v))) := by
    simp only [Finset.mul_sum,mul_left_comm,mul_assoc]
  unfold chartCovHessian
  rw [hsecond]
  simp_rw [rDeriv_covTensorNormSq h hh c A hA hz]
  rw [hsplitPair,hscale]
  change _ = 2*covTensorPair (realMetricFn h c z)
    (fun v => covariantD h c A z (Fin.cons i v)) (B z)+_
  ring

theorem chartTensorNormSq_laplacian (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    chartRealLaplacian h c (fun w => covTensorNormSq (realMetricFn h c w) (A w)) z =
      2*covTensorPair (realMetricFn h c z) (A z) (roughLap h c A z)+
        2*covTensorNormSq (realMetricFn h c z) (covariantD h c A z) := by
  have hgrad : (∑ i, ∑ j, (realMetricFn h c z)⁻¹ i j*
      covTensorPair (realMetricFn h c z) (fun v => covariantD h c A z (Fin.cons i v))
        (fun v => covariantD h c A z (Fin.cons j v))) =
        covTensorNormSq (realMetricFn h c z) (covariantD h c A z) := by
    rw [←covTensorPair_succ,covTensorPair_self]
  have hrough : covTensorPair (realMetricFn h c z) (A z) (roughLap h c A z) =
      ∑ i, ∑ j, (realMetricFn h c z)⁻¹ i j*covTensorPair (realMetricFn h c z) (A z)
        (fun v => covariantD h c (covariantD h c A) z (Fin.cons i (Fin.cons j v))) := by
    unfold roughLap
    rw [covTensorPair_sum_right]
    simp_rw [covTensorPair_sum_right,covTensorPair_mul_right]
  unfold chartRealLaplacian
  simp_rw [chartTensorNormSq_covHessian h hh c A hA hz]
  simp only [mul_add,Finset.sum_add_distrib,mul_left_comm,mul_assoc,←Finset.mul_sum]
  rw [hgrad,←hrough]
  ring

theorem chartJetSq_laplacian (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (k : ℕ) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    chartRealLaplacian h c
      (fun w => covTensorNormSq (realMetricFn h c w) (rmJet h c k w)) z =
      2*covTensorPair (realMetricFn h c z) (rmJet h c k z) (roughLap h c (rmJet h c k) z)+
        2*covTensorNormSq (realMetricFn h c z) (rmJet h c (k+1) z) :=
  chartTensorNormSq_laplacian h hh c (rmJet h c k) (rmJet_contDiffOn h hh c k) hz

end Yau.LeafProofs.L23Aux
