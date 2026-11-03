import Yau.LeafProofs.L23FixedChartFlow
import Yau.LeafProofs.L23TensorFamilySmooth

/-! Actual mixed derivatives of the metric along the original local flow. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem realRicciCoeff_contDiffOn (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (i j : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => realRicciCoeff h c z i j) (chartTarget c) := by
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  apply (realMetricFn_inverse_contDiffOn h hh c a b).mul
  apply ContDiffOn.sum
  intro l _
  exact (hh c l b).mul (riemannCoeff_contDiffOn h hh c a i j l)

theorem localRealRicciFlow_rDeriv_metric_hasDerivAt_inChart
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hx : chartInv c z ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b) (i p q : RIdx n) :
    HasDerivAt (fun s => rDeriv (fun w => realMetricFn (h s) c w p q) z i)
      (-σ*rDeriv (fun w => realRicciCoeff (h t) c w p q) z i) t := by
  let F : ComplexVector n × ℝ → ℝ := fun u => realMetricFn (h u.2) c u.1 p q
  have hF : ContDiffAt ℝ 2 F (z,t) :=
    ((metricFamilySmooth_joint h a b hflow.1 c p q).contDiffAt
      ((isOpen_flowChartDomain c a b).mem_nhds ⟨hz,ht⟩)).of_le (by simp)
  have hd := joint_spatial_time_hasDerivAt F z t hF i
  have heq : (fun w => deriv (fun s => realMetricFn (h s) c w p q) t)=ᶠ[𝓝 z]
      (fun w => -σ*realRicciCoeff (h t) c w p q) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz,
      (continuousAt_extChartAt_symm'' hz).preimage_mem_nhds (hO.mem_nhds hx)] with w hw hwo
    exact (localRealRicciFlow_metric_hasDerivAt_inChart h O a b σ hflow c hw hwo t ht p q).deriv
  have hh := metricFamilySmooth_slice h hflow.1 ⟨ht.1.le,ht.2.le⟩
  have hRdiff := ((realRicciCoeff_contDiffOn (h t) hh c p q).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hval : rDeriv (fun w => deriv (fun s => realMetricFn (h s) c w p q) t) z i=
      -σ*rDeriv (fun w => realRicciCoeff (h t) c w p q) z i := by
    unfold rDeriv
    rw [heq.fderiv_eq,fderiv_const_mul hRdiff]
    simp only [smul_apply,smul_eq_mul]
  change HasDerivAt (fun s => rDeriv (fun w => realMetricFn (h s) c w p q) z i)
    (rDeriv (fun w => deriv (fun s => realMetricFn (h s) c w p q) t) z i) t at hd
  rwa [hval] at hd

end Yau.LeafProofs.L23Aux
