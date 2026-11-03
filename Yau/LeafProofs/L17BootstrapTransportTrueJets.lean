import Yau.LeafProofs.L17BootstrapTransportJets
import Yau.LeafProofs.L17BootstrapTransportContinuity
import Yau.LeafProofs.L17LocalizedSchauderLocalData

open Set Metric
open scoped ContDiff Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17LocalizedSchauderAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0 < T}

 theorem correctionFamily_localTrueJets (D : BootstrapPatch P x)
    {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)
    (u : SchauderSpace P T gamma hT) :
    LocalTrueJets P T hT.le (correctionFamily D theta u) (correctionGradientFamily D theta u)
      (correctionHessianFamily D theta u) (correctionTimeFamily D theta u) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro p
    by_cases hp : p=D.center
    · subst p
      simpa only [correctionFamily,correctionGradientFamily,correctionHessianFamily,
        correctionTimeFamily,ite_eq_left rfl,ite_true] using
        And.intro (correctionValue_continuous D htheta u).continuousOn
          (And.intro (correctionGradient_continuous D htheta u).continuousOn
            (And.intro (correctionHessian_continuous D htheta u).continuousOn
              (correctionTime_continuous D htheta u).continuousOn))
    · simp only [correctionFamily,correctionGradientFamily,correctionHessianFamily,
        correctionTimeFamily,ite_eq_right hp]
      exact ⟨continuousOn_const,continuousOn_const,continuousOn_const,continuousOn_const⟩
  · intro p z hz t
    by_cases hp : p=D.center
    · subst p
      simpa only [correctionFamily,correctionGradientFamily,correctionHessianFamily,ite_eq_left rfl,ite_true] using
        And.intro (correctionValue_hasFDerivAt D htheta u z t) (correctionGradient_hasFDerivAt D htheta u z t)
    · simp only [correctionFamily,correctionGradientFamily,correctionHessianFamily,ite_eq_right hp]
      exact ⟨hasFDerivAt_const (0 : ℝ) z,hasFDerivAt_const (0 : D1 n) z⟩
  · intro p z hz t
    by_cases hp : p=D.center
    · subst p
      simpa only [correctionFamily,correctionTimeFamily,ite_eq_left rfl,ite_true] using
        correctionValue_hasDerivWithinAt D theta u z t
    · simp only [correctionFamily,correctionTimeFamily,ite_eq_right hp]
      exact hasDerivWithinAt_const (c := (0 : ℝ)) (s := Icc (0 : ℝ) T) (x := (t : ℝ))
  · intro p z hz
    by_cases hp : p=D.center
    · subst p
      simpa only [correctionFamily,ite_eq_left rfl,ite_true] using correctionValue_initial D theta u z
    · simp only [correctionFamily,ite_eq_right hp,Pi.zero_apply]

end Yau.LeafProofs.L17BootstrapTransportAux
