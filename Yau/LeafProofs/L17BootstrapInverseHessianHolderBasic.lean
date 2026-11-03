import Yau.LeafProofs.L17BootstrapInverseHessianCoefficients
import Yau.LeafProofs.L17BootstrapCompactCoefficients

/-! Actual inverse-Hessian coefficients lifted into the complete local Hölder spaces. -/
noncomputable section
open Set Metric
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

namespace Yau.LeafProofs.L17BootstrapInverseHessianHolderAux
open L17Aux L17SchauderAux L17BootstrapPatchAux L17BootstrapInverseHessianCoefficientsAux
open L17BootstrapCompactCoefficientsAux L17LocalHolderBanachAlgebraAux

local instance inverseHessianHolderBasicMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

/-- These coefficient targets are Banach spaces, with the actual Frobenius matrix norm. -/
abbrev FirstCoefficient (n : ℕ) := D1 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ
abbrev SecondCoefficient (n : ℕ) := D2 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)
variable {T beta : ℝ} (hT0 : 0 < T) (hTime : T ≤ P.radius^2)
  (hb0 : 0 < beta) (hb : beta < 1)

include hT0 hTime hb0 hb

/-- The actual first coefficient has a smooth local Hölder lift, without shrinking time. -/
theorem exists_first_banach_lift :
    ∃ C1 : ComplexVector n → LocalHolderBanach (FirstCoefficient n) P T beta,
      ContDiffOn ℝ ∞ C1 (ball 0 (D.smallRadius/2)) ∧
      ∀ theta ∈ ball 0 (D.smallRadius/2), ∀ q : LocalCylinder P T,
        localFun (FirstCoefficient n) (C1 theta).value q =
          c1Family D theta q.1 q.2.1 q.2.2 := by
  classical
  have hSpecial : ContDiffOn ℝ ∞
      (fun a : ComplexVector n × (ComplexVector n × ℝ) => c1 D a.1 a.2.1)
      (ball 0 D.smallRadius ×ˢ (ball 0 (2*P.radius) ×ˢ Set.univ)) := by
    simpa [c1Family] using c1Family_contDiffOn D D.center
  obtain ⟨C1,hSmooth,hValues⟩ := exists_banach_spike_lift P D.center
    (half_pos D.smallRadius_pos) (half_lt_self D.smallRadius_pos) hT0 hTime hb0 hb
    (fun theta z (_ : ℝ) => c1 D theta z)
    (fun _ _ _ => (0 : FirstCoefficient n)) hSpecial (fun _ => contDiffOn_const)
    (le_rfl : (0 : ℝ) ≤ 0) (le_rfl : (0 : ℝ) ≤ 0) (le_rfl : (0 : ℝ) ≤ 0)
    (fun _ z _ t _ => c1_background_mixed_bounds z t)
  exact ⟨C1,hSmooth,by simpa only [c1Family] using hValues⟩

/-- The second coefficient has the same radius and original time, with its genuine Levi baseline. -/
theorem exists_second_banach_lift :
    ∃ C2 : ComplexVector n → LocalHolderBanach (SecondCoefficient n) P T beta,
      ContDiffOn ℝ ∞ C2 (ball 0 (D.smallRadius/2)) ∧
      ∀ theta ∈ ball 0 (D.smallRadius/2), ∀ q : LocalCylinder P T,
        localFun (SecondCoefficient n) (C2 theta).value q =
          c2Family D theta q.1 q.2.1 q.2.2 := by
  classical
  have hSpecial : ContDiffOn ℝ ∞
      (fun a : ComplexVector n × (ComplexVector n × ℝ) => c2 D a.1 a.2.1)
      (ball 0 D.smallRadius ×ˢ (ball 0 (2*P.radius) ×ˢ Set.univ)) := by
    simpa [c2Family] using c2Family_contDiffOn D D.center
  obtain ⟨C2,hSmooth,hValues⟩ := exists_banach_spike_lift P D.center
    (half_pos D.smallRadius_pos) (half_lt_self D.smallRadius_pos) hT0 hTime hb0 hb
    (fun theta z (_ : ℝ) => c2 D theta z)
    (fun _ _ _ => leviHessianCLM n) hSpecial (fun _ => contDiffOn_const)
    (norm_nonneg (leviHessianCLM n)) (le_rfl : (0 : ℝ) ≤ 0) (le_rfl : (0 : ℝ) ≤ 0)
    (fun _ z _ t _ => c2_background_mixed_bounds z t)
  exact ⟨C2,hSmooth,by simpa only [c2Family] using hValues⟩

end Yau.LeafProofs.L17BootstrapInverseHessianHolderAux
