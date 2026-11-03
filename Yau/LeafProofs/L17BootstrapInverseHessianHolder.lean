import Yau.LeafProofs.L17BootstrapInverseHessianHolderBasic
import Yau.LeafProofs.L17LocalHolderBanachAlgebraConstants

/-! Simultaneous Banach and raw local Hölder lifts, with actual baseline and collar identities. -/
noncomputable section
open Set Metric
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

namespace Yau.LeafProofs.L17BootstrapInverseHessianHolderAux
open L17Aux L17SchauderAux L17BootstrapPatchAux L17BootstrapInverseHessianCoefficientsAux
open L17LocalHolderBanachAlgebraAux

local instance inverseHessianHolderCanonicalMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)
variable {T beta : ℝ} (hT0 : 0 < T) (hTime : T ≤ P.radius^2)
  (hb0 : 0 < beta) (hb : beta < 1)

include hT0 hTime hb0 hb

/-- Both genuine inverse-Hessian coefficients are smooth in the same Banach parameter ball. -/
theorem exists_inverse_hessian_banach_lifts :
    ∃ C1 : ComplexVector n → LocalHolderBanach (FirstCoefficient n) P T beta,
      ∃ C2 : ComplexVector n → LocalHolderBanach (SecondCoefficient n) P T beta,
        ContDiffOn ℝ ∞ C1 (ball 0 (D.smallRadius/2)) ∧
        ContDiffOn ℝ ∞ C2 (ball 0 (D.smallRadius/2)) ∧
        (∀ theta ∈ ball 0 (D.smallRadius/2), ∀ q : LocalCylinder P T,
          localFun (FirstCoefficient n) (C1 theta).value q =
            c1Family D theta q.1 q.2.1 q.2.2) ∧
        (∀ theta ∈ ball 0 (D.smallRadius/2), ∀ q : LocalCylinder P T,
          localFun (SecondCoefficient n) (C2 theta).value q =
            c2Family D theta q.1 q.2.1 q.2.2) ∧
        C1 0 = 0 ∧
        C2 0 = const (SecondCoefficient n) P T beta (leviHessianCLM n) ∧
        (∀ theta ∈ ball 0 (D.smallRadius/2), ∀ q : LocalCylinder P T,
          (q.1 ≠ D.center ∨ (q.2.1 : ComplexVector n) ∉ tsupport D.bump) →
            localFun (FirstCoefficient n) (C1 theta).value q = 0 ∧
            localFun (SecondCoefficient n) (C2 theta).value q = leviHessianCLM n) := by
  classical
  obtain ⟨C1,hSmooth1,hValues1⟩ := exists_first_banach_lift D hT0 hTime hb0 hb
  obtain ⟨C2,hSmooth2,hValues2⟩ := exists_second_banach_lift D hT0 hTime hb0 hb
  have hZero : (0 : ComplexVector n) ∈ ball 0 (D.smallRadius/2) :=
    by simpa only [mem_ball,dist_self] using half_pos D.smallRadius_pos
  have hBase1 : C1 0 = 0 := by
    apply L17LocalHolderBanachAlgebraAux.ext
    intro q
    change localFun (FirstCoefficient n) (C1 0).value q = 0
    rw [hValues1 0 hZero q]
    simp only [c1Family,c1_zero,ite_self]
  have hBase2 : C2 0 = const (SecondCoefficient n) P T beta (leviHessianCLM n) := by
    apply L17LocalHolderBanachAlgebraAux.ext
    intro q
    change localFun (SecondCoefficient n) (C2 0).value q = leviHessianCLM n
    rw [hValues2 0 hZero q]
    simp only [c2Family,c2_zero,ite_self]
  refine ⟨C1,C2,hSmooth1,hSmooth2,hValues1,hValues2,hBase1,hBase2,?_⟩
  intro theta htheta q hCollar
  rw [hValues1 theta htheta q,hValues2 theta htheta q]
  by_cases hq : q.1 = D.center
  · have hz : (q.2.1 : ComplexVector n) ∉ tsupport D.bump :=
      hCollar.resolve_left (not_not.mpr hq)
    have hthetaHalf : ‖theta‖ < D.smallRadius/2 :=
      by simpa only [mem_ball,dist_zero_right] using htheta
    have hthetaSmall : ‖theta‖ < D.smallRadius :=
      hthetaHalf.trans (half_lt_self D.smallRadius_pos)
    simpa only [c1Family,c2Family,ite_eq_left hq] using
      And.intro (c1_of_not_mem_tsupport D theta hz) (c2_of_not_mem_tsupport D hthetaSmall hz)
  · simp only [c1Family,c2Family,ite_eq_right hq,and_self]

/-- The same actual coefficients are infinitely smooth in the original, unscaled Hölder graph. -/
theorem exists_inverse_hessian_local_holder_lifts :
    ∃ C1 : ComplexVector n → LocalHolderSpace (FirstCoefficient n) P T beta,
      ∃ C2 : ComplexVector n → LocalHolderSpace (SecondCoefficient n) P T beta,
        ContDiffOn ℝ ∞ C1 (ball 0 (D.smallRadius/2)) ∧
        ContDiffOn ℝ ∞ C2 (ball 0 (D.smallRadius/2)) ∧
        (∀ theta ∈ ball 0 (D.smallRadius/2), ∀ q : LocalCylinder P T,
          localFun (FirstCoefficient n) (C1 theta) q = c1Family D theta q.1 q.2.1 q.2.2) ∧
        (∀ theta ∈ ball 0 (D.smallRadius/2), ∀ q : LocalCylinder P T,
          localFun (SecondCoefficient n) (C2 theta) q = c2Family D theta q.1 q.2.1 q.2.2) := by
  obtain ⟨C1,hSmooth1,hValues1⟩ := exists_first_banach_lift D hT0 hTime hb0 hb
  obtain ⟨C2,hSmooth2,hValues2⟩ := exists_second_banach_lift D hT0 hTime hb0 hb
  refine ⟨fun theta => (C1 theta).value,fun theta => (C2 theta).value,?_,?_,hValues1,hValues2⟩
  · exact (valueContinuousLinearEquiv (FirstCoefficient n) P T beta).contDiff.comp_contDiffOn hSmooth1
  · exact (valueContinuousLinearEquiv (SecondCoefficient n) P T beta).contDiff.comp_contDiffOn hSmooth2

end Yau.LeafProofs.L17BootstrapInverseHessianHolderAux
