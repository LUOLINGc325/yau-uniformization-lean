import Yau.LeafProofs.L10DiscEnergyHessian
import Yau.LeafProofs.L10DiscMiranda
import Yau.LeafProofs.L10DiscBoundaryBootstrap

/-! The frozen original disc Dirichlet leaf, with its constant fixed before
all density data and with genuine closed-disc smoothness. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace Yau.LeafProofs

theorem discDirichletEstimate : LeafCandidates.DiscDirichletEstimate := by
  refine ⟨2, by norm_num, ?_⟩
  intro f hf
  obtain ⟨u, hu, hzero, hPDE⟩ := discGreen_smoothDirichlet hf
  refine ⟨u, hu, hzero, hPDE, ?_⟩
  have hur : ContDiffOn ℝ ∞ (fun w => (u w).re) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.reCLM.contDiff.comp_contDiffOn hu
  have hui : ContDiffOn ℝ ∞ (fun w => (u w).im) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.imCLM.contDiff.comp_contDiffOn hu
  have hr : (∫ z in Metric.ball (0 : ℂ) 1,
      discEnergyRealHessianSq (fun w => (u w).re) z) ≤
      ∫ z in Metric.ball (0 : ℂ) 1,
        (discEnergyRealLaplacian (fun w => (u w).re) z)^2 := by
    simpa only [discEnergyRealHessianSq, discEnergyRealLaplacian] using
      discMirandaTalenti hur (fun z hz => by rw [hzero z hz]; rfl)
  have hi : (∫ z in Metric.ball (0 : ℂ) 1,
      discEnergyRealHessianSq (fun w => (u w).im) z) ≤
      ∫ z in Metric.ball (0 : ℂ) 1,
        (discEnergyRealLaplacian (fun w => (u w).im) z)^2 := by
    simpa only [discEnergyRealHessianSq, discEnergyRealLaplacian] using
      discMirandaTalenti hui (fun z hz => by rw [hzero z hz]; rfl)
  have hH := discEnergy_complex_hessian_estimate hu hr hi
  have hE := discEnergy_original_estimate hu hzero hH
  have heq : (∫ z in Metric.ball (0 : ℂ) 1, ‖discEnergyLaplacian u z‖^2) =
      ∫ z in Metric.ball (0 : ℂ) 1, ‖f z‖^2 := by
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro z hz
    dsimp only
    rw [discEnergyLaplacian_eq_planar hz, hPDE z hz]
  simpa only [heq] using hE

end Yau.LeafProofs
