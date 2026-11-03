import Yau.LeafProofs.L23DistanceEnergyCovariant
import Yau.LeafProofs.L23FieldMetricParallelCalculus

/-! Metric compatibility for the actual pullback connection and scalar densities. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {M : ComplexManifold n}

theorem mapDirection_contDiffAt (Z : E → ComplexVector n) {p : E} (k : ℕ)
    (hZ : ContDiffAt ℝ (k+1) Z p) (a : E) : ContDiffAt ℝ k (mapDirection Z a) p := by
  change ContDiffAt ℝ k (fun q => fderiv ℝ Z q a) p
  exact (hZ.fderiv_right (m := k) (by simp)).clm_apply contDiffAt_const

theorem mapCovariantD_contDiffAt (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (Z W : E → ComplexVector n) {p : E} (hz : Z p∈chartTarget c)
    (k : ℕ) (hZ : ContDiffAt ℝ (k+1) Z p) (hW : ContDiffAt ℝ (k+1) W p) (a : E) :
    ContDiffAt ℝ k (mapCovariantD (chartChristoffelBilin h c) Z a W) p := by
  change ContDiffAt ℝ k (fun q => mapDirection W a q+
    chartChristoffelBilin h c (Z q) (mapDirection Z a q) (W q)) p
  have hΓ : ContDiffAt ℝ k (fun q => chartChristoffelBilin h c (Z q)) p :=
    ((((chartChristoffelBilin_contDiffOn h hh c).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).of_le (by simp)).comp p
        (hZ.of_le (by simp)))
  exact (mapDirection_contDiffAt W k hW a).add
    ((hΓ.clm_apply (mapDirection_contDiffAt Z k hZ a)).clm_apply (hW.of_le (by simp)))

theorem mapMetricPair_hasFDerivAt (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (Z W Q : E → ComplexVector n) {p : E} (hz : Z p∈chartTarget c)
    (hZ : DifferentiableAt ℝ Z p) (hW : DifferentiableAt ℝ W p) (hQ : DifferentiableAt ℝ Q p) :
    HasFDerivAt (fun q => realMetricInChart h c (Z q) (W q) (Q q))
      (fderiv ℝ (fun q => realMetricInChart h c (Z q) (W q) (Q q)) p) p := by
  have hG := ((realMetricInChart_smooth h hh c).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  exact (((hG.comp p hZ).clm_apply hW).clm_apply hQ).hasFDerivAt

theorem mapDirection_metricPair (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (Z W Q : E → ComplexVector n) {p : E} (hz : Z p∈chartTarget c)
    (hZ : DifferentiableAt ℝ Z p) (hW : DifferentiableAt ℝ W p) (hQ : DifferentiableAt ℝ Q p) (a : E) :
    mapDirection (fun q => realMetricInChart h c (Z q) (W q) (Q q)) a p=
      realMetricInChart h c (Z p) (mapCovariantD (chartChristoffelBilin h c) Z a W p) (Q p)+
      realMetricInChart h c (Z p) (W p) (mapCovariantD (chartChristoffelBilin h c) Z a Q p) := by
  have hG := ((realMetricInChart_smooth h hh c).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have H := (((hG.hasFDerivAt.comp p hZ.hasFDerivAt).clm_apply hW.hasFDerivAt).clm_apply hQ.hasFDerivAt).fderiv
  have he := congrArg (fun L : E →L[ℝ] ℝ => L a) H
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at he
  rw [realMetricInChart_connection_compatibility h hh c (Z p) hz (fderiv ℝ Z p a) (W p) (Q p)] at he
  simpa only [mapDirection,mapCovariantD,Function.comp_def,map_add,ContinuousLinearMap.add_apply,
    add_assoc,add_comm,add_left_comm] using he

theorem mapDirection_metricSelf (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (Z W : E → ComplexVector n) {p : E} (hz : Z p∈chartTarget c)
    (hZ : DifferentiableAt ℝ Z p) (hW : DifferentiableAt ℝ W p) (a : E) :
    mapDirection (fun q => realMetricInChart h c (Z q) (W q) (W q)) a p=
      2*realMetricInChart h c (Z p) (W p) (mapCovariantD (chartChristoffelBilin h c) Z a W p) := by
  rw [mapDirection_metricPair h hh c Z W W hz hZ hW hW a,
    realMetricInChart_symm h c (Z p) (mapCovariantD (chartChristoffelBilin h c) Z a W p) (W p)]
  ring

end Yau.LeafProofs.L23Aux
