import Yau.LeafProofs.L19KernelCoreAction

/-! The complete unchanged Gaussian estimate for every original scalar heat kernel. -/
noncomputable section
open scoped ComplexOrder
namespace Yau.LeafProofs.L19Aux

/-- All bridges for the original arbitrary kernel are now internal. The
positive constants are selected from the dimension before the geometry. -/
theorem liYauGaussian : LeafCandidates.LiYauGaussian := by
  intro n hn
  obtain ⟨C, c, hC, hc, hbound⟩ := exists_uniform_gaussian_of_ball_pairingIdentity n
  refine ⟨C, c, hC, hc, ?_⟩
  intro M g hcomplete hK hRic μ hμ H hH
  exact hbound M g hcomplete hK hRic μ hμ H hH
    (scalarHeatKernel_ball_pairing hn g hcomplete hK hRic μ hμ hH)

end Yau.LeafProofs.L19Aux
