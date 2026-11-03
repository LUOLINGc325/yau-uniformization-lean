import Yau.Proofs.F03ScalarHeatInitialJetBounds
import Yau.Proofs.F03HeatCorrectionSpatialSmooth

/-! The actual chart differential is integrable through heat-time zero and commutes with the actual time integral. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem boundedScalarHeat_spatialDerivative_integrableOn
    (g : HermitianField M) (f : M.Carrier → ℝ) (u : ℝ → M.Carrier → ℝ)
    (hf : SmoothFn f) (hu : IsBoundedScalarHeat g f u)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a) (R : ℝ) :
    IntegrableOn (fun b => fderiv ℝ (inChart a (u b)) z) (Ioc 0 R) volume := by
  have hCont : ContinuousOn (fun b => fderiv ℝ (inChart a (u b)) z) (Ioc 0 R) := by
    intro b hb
    have hAt := (hu.1 a).contDiffAt
      (((isOpen_extChartAt_target (I := ComplexModel n) a).prod isOpen_Ioi).mem_nhds
        (show (z,b) ∈ chartTarget a ×ˢ Ioi 0 from ⟨hz,hb.1⟩))
    have hd := joint_spatial_fderiv_contDiffAt (m := ∞) hAt
    exact (hd.continuousAt.comp (f := fun t : ℝ => (z,t))
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  obtain ⟨C,hBound⟩ := boundedScalarHeat_compact_spatial_tensor_bound g f u hf hu a {z}
    isCompact_singleton (singleton_subset_iff.mpr hz) R 1
  have hFin : (volume : Measure ℝ) (Ioc 0 R) ≠ ⊤ :=
    ((measure_mono Ioc_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne
  have hConst : IntegrableOn (fun _ : ℝ => C) (Ioc 0 R) volume := integrableOn_const hFin
  apply hConst.mono' (hCont.aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with b hb
  simpa only [norm_iteratedFDeriv_one] using hBound b ⟨hb.1.le,hb.2⟩ z (mem_singleton _)

theorem boundedScalarHeat_timeIntegral_chart_derivative
    (g : HermitianField M) (f : M.Carrier → ℝ) (u : ℝ → M.Carrier → ℝ)
    (hf : SmoothFn f) (hu : IsBoundedScalarHeat g f u)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a) {R : ℝ} (hR : 0 ≤ R) :
    fderiv ℝ (inChart a (fun y => ∫ b in (0:ℝ)..R,u b y)) z=
      ∫ b in (0:ℝ)..R,fderiv ℝ (inChart a (u b)) z := by
  have hPackage := initial_spatial_integral_package
    (fun p : ComplexVector n × ℝ => u p.2 (chartInv a p.1)) (inChart a f)
    (isOpen_extChartAt_target (I := ComplexModel n) a) (hu.1 a) (hf a)
    (fun z => congrFun hu.2.1.1 (chartInv a z))
    (fun K hK hKt m ε hε => hu.2.1.2 a K hK hKt m ε hε) hR
  obtain ⟨D,hD,hEval⟩ := hPackage.2 z hz
  change fderiv ℝ (fun w => ∫ b in (0:ℝ)..R,u b (chartInv a w)) z=_
  rw [hD.fderiv]
  ext v
  rw [intervalIntegral.integral_of_le hR,ContinuousLinearMap.integral_apply
    (boundedScalarHeat_spatialDerivative_integrableOn g f u hf hu a hz R)]
  calc
    D v=∫ b in Ioc (0:ℝ) R,(fderiv ℝ (fun w => u b (chartInv a w)) z) v := by
      simpa only [intervalIntegral.integral_of_le hR] using hEval v
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun b => rfl)

end Yau.Proofs.F03Aux
