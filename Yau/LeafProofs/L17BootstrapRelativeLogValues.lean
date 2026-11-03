import Yau.LeafProofs.L17BootstrapConjugatedResidual

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux
local instance relativeLogValuesMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T gamma : ℝ)

theorem relativeLogDifference_zero_at
    (K Hstar Htheta Hzero : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (dLog : LocalHolderSpace ℝ P T gamma)
    (hSmallt : ‖relativeMetricPerturbation P T gamma K Hstar Htheta‖<1)
    (hSmall0 : ‖relativeMetricPerturbation P T gamma K Hstar Hzero‖<1)
    (q : LocalCylinder P T) (hH : Htheta q=Hzero q) (hd : localFun ℝ dLog q=0) :
    localFun ℝ (relativeLogDifference P T gamma K Hstar Htheta Hzero dLog) q=0 := by
  change relativeTraceLog P T gamma K Hstar Htheta q-
    relativeTraceLog P T gamma K Hstar Hzero q-localFun ℝ dLog q=0
  rw [relativeTraceLog,relativeTraceLog,
    matrixTraceLogIncrement_value P T gamma _ hSmallt,
    matrixTraceLogIncrement_value P T gamma _ hSmall0]
  change (Matrix.trace (L17BanachLogarithmAux.logIncrement _ (K q*(Htheta q-Hstar q)))).re-
    (Matrix.trace (L17BanachLogarithmAux.logIncrement _ (K q*(Hzero q-Hstar q)))).re-
      localFun ℝ dLog q=0
  rw [hH,hd,sub_self,sub_zero]

theorem relativeLogDifference_logratio
    (K Hstar Htheta Hzero : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (dLog : LocalHolderSpace ℝ P T gamma)
    (hK : ∀ q : LocalCylinder P T, K q=(Hstar q)⁻¹)
    (hBase : ∀ q : LocalCylinder P T, (Hstar q).PosDef)
    (hHt : ∀ q : LocalCylinder P T, (Htheta q).PosDef)
    (hH0 : ∀ q : LocalCylinder P T, (Hzero q).PosDef)
    (hSmallt : ‖relativeMetricPerturbation P T gamma K Hstar Htheta‖<1)
    (hSmall0 : ‖relativeMetricPerturbation P T gamma K Hstar Hzero‖<1)
    (q : LocalCylinder P T) :
    localFun ℝ (relativeLogDifference P T gamma K Hstar Htheta Hzero dLog) q=
      Real.log ((Htheta q).det.re/(Hzero q).det.re)-localFun ℝ dLog q := by
  change relativeTraceLog P T gamma K Hstar Htheta q-
    relativeTraceLog P T gamma K Hstar Hzero q-localFun ℝ dLog q=_
  rw [relativeTraceLog_value P T gamma K Hstar Htheta hK hBase hHt hSmallt,
    relativeTraceLog_value P T gamma K Hstar Hzero hK hBase hH0 hSmall0]
  have hb : (Hstar q).det.re≠0 := (Complex.pos_iff.mp (hBase q).det_pos).1.ne'
  have ht : (Htheta q).det.re≠0 := (Complex.pos_iff.mp (hHt q).det_pos).1.ne'
  have h0 : (Hzero q).det.re≠0 := (Complex.pos_iff.mp (hH0 q).det_pos).1.ne'
  rw [Real.log_div ht hb,Real.log_div h0 hb,Real.log_div ht h0]
  ring

end Yau.LeafProofs.L17BootstrapMetricAux
