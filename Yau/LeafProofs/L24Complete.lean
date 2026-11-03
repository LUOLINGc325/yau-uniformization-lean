import Yau.LeafProofs.L24LocalGradient
import Yau.LeafProofs.L24GaussianCylinder

/-! The exact original heat-kernel gradient leaf, with all local analytic
inputs discharged internally from Bochner and the proved Gaussian bound. -/
namespace Yau.LeafProofs

theorem L24 : Yau.LeafObligations.L24 := by
  apply L24Aux.heatKernelGradient_of_sqrt_scale_local_gradient
    L24Aux.localGradientConstant L24Aux.localGradientConstant_pos
  intro n M g hK hRic u hu x t A ht hA hbound
  exact L24Aux.positiveHeatSolution_gradient_at_sqrt_scale g hK hRic hu x ht hA hbound

end Yau.LeafProofs
