import Yau.LeafProofs.L17BootstrapRelativeLogarithm
import Yau.LeafProofs.L17BootstrapMetricPositive

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux
local instance metricDomainMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T gamma : ℝ)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def metricDomain (s V0 : Set E)
    (K Hstar : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma) (lambda : ℝ)
    (Htheta Hzero : E → LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma) : Set E :=
  s ∩ {a | ‖Htheta a-Hstar‖<relativeMetricRadius P T gamma K lambda} ∩
    {a | ‖Hzero a-Hstar‖<relativeMetricRadius P T gamma K lambda} ∩ V0

theorem metricDomain_isOpen {s V0 : Set E} (hs : IsOpen s) (hV0 : IsOpen V0)
    (K Hstar : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma) (lambda : ℝ)
    {Htheta Hzero : E → LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma}
    (hHt : ContDiffOn ℝ ∞ Htheta s) (hH0 : ContDiffOn ℝ ∞ Hzero s) :
    IsOpen (metricDomain P T gamma s V0 K Hstar lambda Htheta Hzero) := by
  have hFirst : IsOpen (s ∩ {a | ‖Htheta a-Hstar‖<relativeMetricRadius P T gamma K lambda}) :=
    (hHt.continuousOn.sub continuousOn_const).norm.isOpen_inter_preimage hs isOpen_Iio
  have hSecond : IsOpen ((s ∩ {a | ‖Htheta a-Hstar‖<relativeMetricRadius P T gamma K lambda}) ∩
      {a | ‖Hzero a-Hstar‖<relativeMetricRadius P T gamma K lambda}) :=
    ((hH0.continuousOn.sub continuousOn_const).norm.mono inter_subset_left).isOpen_inter_preimage
      hFirst isOpen_Iio
  exact hSecond.inter hV0

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem mem_metricDomain_base {s V0 : Set E}
    (K Hstar : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    {lambda : ℝ} (hlambda : 0<lambda)
    {Htheta Hzero : E → LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma}
    {a : E} (ha : a∈s) (ha0 : a∈V0) (hHt : Htheta a=Hstar) (hH0 : Hzero a=Hstar) :
    a∈metricDomain P T gamma s V0 K Hstar lambda Htheta Hzero := by
  exact ⟨⟨⟨ha,by simpa only [mem_ofPred_eq,hHt,sub_self,norm_zero] using relativeMetricRadius_pos P T gamma K hlambda⟩,
    by simpa only [mem_ofPred_eq,hH0,sub_self,norm_zero] using relativeMetricRadius_pos P T gamma K hlambda⟩,ha0⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem metricDomain_relative_norms {s V0 : Set E}
    (K Hstar : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma) (lambda : ℝ)
    {Htheta Hzero : E → LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma}
    {a : E} (ha : a∈metricDomain P T gamma s V0 K Hstar lambda Htheta Hzero) :
    ‖relativeMetricPerturbation P T gamma K Hstar (Htheta a)‖<1/8 ∧
      ‖relativeMetricPerturbation P T gamma K Hstar (Hzero a)‖<1/8 :=
  ⟨relativeMetricPerturbation_norm_lt P T gamma K Hstar _ lambda ha.1.1.2,
    relativeMetricPerturbation_norm_lt P T gamma K Hstar _ lambda ha.1.2⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem metricDomain_posDef {s V0 : Set E}
    (K Hstar : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    {lambda : ℝ} (hlambda : 0<lambda)
    {Htheta Hzero : E → LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma}
    (hLower : ∀ q : LocalCylinder P T,
      (Hstar q-(lambda : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef)
    (hHermt : ∀a∈s,∀q : LocalCylinder P T, (Htheta a q).IsHermitian)
    (hHerm0 : ∀a∈s,∀q : LocalCylinder P T, (Hzero a q).IsHermitian)
    {a : E} (ha : a∈metricDomain P T gamma s V0 K Hstar lambda Htheta Hzero)
    (q : LocalCylinder P T) : (Htheta a q).PosDef ∧ (Hzero a q).PosDef := by
  exact ⟨local_metric_posDef_of_norm_close P T gamma Hstar (Htheta a) hlambda hLower
      (hHermt a ha.1.1.1) (ha.1.1.2.le.trans (min_le_left _ _)) q,
    local_metric_posDef_of_norm_close P T gamma Hstar (Hzero a) hlambda hLower
      (hHerm0 a ha.1.1.1) (ha.1.2.le.trans (min_le_left _ _)) q⟩

end Yau.LeafProofs.L17BootstrapMetricAux
