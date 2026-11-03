import Yau.LeafProofs.L23JetNaturality
import Yau.LeafProofs.L23TensorLaplacian

/-! The original scalar jet norm has the computed fixed-chart derivatives. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
open L18Aux L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem jetSq_inChart_eventuallyEq (h : HermitianField M) (hh : MetricSmooth h)
    (k : ℕ) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    inChart c (jetSq h k)=ᶠ[𝓝 z]
      (fun w => covTensorNormSq (realMetricFn h c w) (rmJet h c k w)) := by
  filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
  exact jetSq_inChart h hh k c hw

theorem jetSq_contDiffAt (h : HermitianField M) (hh : MetricSmooth h)
    (k : ℕ) (x : M.Carrier) :
    ContDiffAt ℝ ∞ (inChart x (jetSq h k)) (chartPt x x) := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hs := (chartJetSq_contDiffOn h hh x k).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)
  exact hs.congr_of_eventuallyEq (jetSq_inChart_eventuallyEq h hh k x hz)

theorem chartRealLaplacian_eventuallyEq (h : HermitianField M) (c : M.Carrier)
    (f g : ComplexVector n → ℝ) (z : ComplexVector n) (hfg : f=ᶠ[𝓝 z] g) :
    chartRealLaplacian h c f z=chartRealLaplacian h c g z := by
  have h1 (i : RIdx n) : rDeriv f z i=rDeriv g z i := by
    unfold rDeriv
    rw [hfg.fderiv_eq]
  have h2 (i j : RIdx n) : rDeriv (fun w => rDeriv f w j) z i=
      rDeriv (fun w => rDeriv g w j) z i := by
    have hh : (fun w => rDeriv f w j)=ᶠ[𝓝 z] (fun w => rDeriv g w j) :=
      (hfg.fderiv (𝕜 := ℝ)).mono
        (fun _ hw => congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec j)) hw)
    exact congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec i)) (hh.fderiv_eq (𝕜 := ℝ))
  simp only [chartRealLaplacian,chartCovHessian,h1,h2]

theorem realLap_jetSq (h : HermitianField M) (hh : MetricSmooth h)
    (k : ℕ) (x : M.Carrier) :
    realLap h (jetSq h k) x=
      2*covTensorPair (realMetricFn h x (chartPt x x))
        (rmJet h x k (chartPt x x)) (roughLap h x (rmJet h x k) (chartPt x x))+
          2*jetSq h (k+1) x := by
  unfold realLap
  have heq := jetSq_inChart_eventuallyEq h hh k x (z := chartPt x x) (mem_extChartAt_target x)
  rw [chartRealLaplacian_eventuallyEq h x _ _ (chartPt x x) heq,
      chartJetSq_laplacian h hh x k (z := chartPt x x) (mem_extChartAt_target x)]
  rfl

theorem realGradPair_jetSq_self_le (h : HermitianField M) (hh : MetricSmooth h)
    (k : ℕ) (x : M.Carrier) :
    realGradPair h (jetSq h k) (jetSq h k) x ≤ 4*jetSq h k x*jetSq h (k+1) x := by
  have heq := jetSq_inChart_eventuallyEq h hh k x (z := chartPt x x) (mem_extChartAt_target x)
  have hder : ∀ i : RIdx n, rDeriv (inChart x (jetSq h k)) (chartPt x x) i=
      rDeriv (fun w => covTensorNormSq (realMetricFn h x w) (rmJet h x k w)) (chartPt x x) i := by
    intro i
    unfold rDeriv
    rw [heq.fderiv_eq]
  unfold realGradPair
  rw [chartGradientPair_eq_sum]
  simp only [hder]
  have hb := chartJetSq_gradient_le h hh x k (mem_extChartAt_target x)
  rw [chartGradientPair_eq_sum] at hb
  exact hb

end Yau.LeafProofs.L23Aux
