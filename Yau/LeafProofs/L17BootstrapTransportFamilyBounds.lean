import Yau.LeafProofs.L17BootstrapTransportScaledBounds

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17LocalizedSchauderAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T alpha beta : ℝ} {hT : 0 < T}

theorem correctionFamily_bounds_of_actual_holders (D : BootstrapPatch P x)
    (theta : ComplexVector n) (u : SchauderSpace P T alpha hT) {A : ℝ}
    (hA : 0 ≤ A) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (R0 : LocalHolderSpace ℝ P T beta) (R1 : LocalHolderSpace (D1 n) P T beta)
    (R2 : LocalHolderSpace (D2 n) P T beta) (R3 : LocalHolderSpace ℝ P T beta)
    (hNorm : ‖R0‖ ≤ A ∧ ‖R1‖ ≤ A ∧ ‖R2‖ ≤ A ∧ ‖R3‖ ≤ A)
    (hRep0 : ∀ q : ComplexVector n × Time T, ∀ hq : q.1 ∈ ball (0 : ComplexVector n) P.radius,
      correctionValue D theta u q=P.radius^2 • localFun ℝ R0 ⟨D.center,(⟨q.1,hq⟩,q.2)⟩)
    (hRep1 : ∀ q : ComplexVector n × Time T, ∀ hq : q.1 ∈ ball (0 : ComplexVector n) P.radius,
      correctionGradient D theta u q=P.radius • localFun (D1 n) R1 ⟨D.center,(⟨q.1,hq⟩,q.2)⟩)
    (hRep2 : ∀ q : ComplexVector n × Time T, ∀ hq : q.1 ∈ ball (0 : ComplexVector n) P.radius,
      correctionHessian D theta u q=localFun (D2 n) R2 ⟨D.center,(⟨q.1,hq⟩,q.2)⟩)
    (hRep3 : ∀ q : ComplexVector n × Time T, ∀ hq : q.1 ∈ ball (0 : ComplexVector n) P.radius,
      correctionTime D theta u q=localFun ℝ R3 ⟨D.center,(⟨q.1,hq⟩,q.2)⟩) :
    LocalScaledJetBounds P T beta (2*A) (correctionFamily D theta u)
      (correctionGradientFamily D theta u) (correctionHessianFamily D theta u)
      (correctionTimeFamily D theta u) := by
  have hZero (q : ComplexVector n × Time T) (hq : q.1 ∉ ball (0 : ComplexVector n) (P.radius/4)) :
      q.1 ∉ tsupport D.bump := fun h => hq (D.bump_support_ball_quarter h)
  have hV := scaled_zero_collar_holder_bounds hA (sq_nonneg P.radius) hbeta0 hbeta1
    D.center R0 hNorm.1 (correctionValue D theta u)
    (fun q hq => correctionValue_zero_of_not_mem_support D theta u (hZero q hq)) hRep0
  have hD := scaled_zero_collar_holder_bounds hA P.radius_pos.le hbeta0 hbeta1
    D.center R1 hNorm.2.1 (correctionGradient D theta u)
    (fun q hq => correctionGradient_zero_of_not_mem_support D theta u (hZero q hq)) hRep1
  have hH := scaled_zero_collar_holder_bounds hA zero_le_one hbeta0 hbeta1
    D.center R2 hNorm.2.2.1 (correctionHessian D theta u)
    (fun q hq => correctionHessian_zero_of_not_mem_support D theta u (hZero q hq))
    (fun q hq => by simpa only [one_smul] using hRep2 q hq)
  have hB := scaled_zero_collar_holder_bounds hA zero_le_one hbeta0 hbeta1
    D.center R3 hNorm.2.2.2 (correctionTime D theta u)
    (fun q hq => correctionTime_zero_of_not_mem_support D theta u (hZero q hq))
    (fun q hq => by simpa only [one_smul] using hRep3 q hq)
  have hPow (q r : ComplexVector n × Time T) :
      0 ≤ (localScaledDistance P.radius q r)^beta := Real.rpow_nonneg
    (div_nonneg (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) P.radius_pos.le) _
  have hrho := P.radius_pos
  constructor
  · intro p q _hq
    by_cases hp : p=D.center
    · subst p
      simpa only [correctionFamily,correctionGradientFamily,correctionHessianFamily,correctionTimeFamily,
        ite_eq_left rfl,ite_true,one_mul,Real.norm_eq_abs] using
        And.intro (hV.1 q) (And.intro (hD.1 q) (And.intro (hH.1 q) (hB.1 q)))
    · simp only [correctionFamily,correctionGradientFamily,correctionHessianFamily,correctionTimeFamily,
        ite_eq_right hp,Pi.zero_apply,abs_zero,norm_zero]
      refine ⟨?_,?_,?_,?_⟩ <;> positivity
  · intro p q r _hq _hr
    by_cases hp : p=D.center
    · subst p
      simpa only [correctionFamily,correctionGradientFamily,correctionHessianFamily,correctionTimeFamily,
        ite_eq_left rfl,ite_true,one_mul,Real.norm_eq_abs] using
        And.intro (hV.2 q r) (And.intro (hD.2 q r) (And.intro (hH.2 q r) (hB.2 q r)))
    · have hd := hPow q r
      simp only [correctionFamily,correctionGradientFamily,correctionHessianFamily,correctionTimeFamily,
        ite_eq_right hp,Pi.zero_apply,sub_self,abs_zero,norm_zero]
      refine ⟨?_,?_,?_,?_⟩ <;> positivity

end Yau.LeafProofs.L17BootstrapTransportAux
