import Mathlib

/-! Integration along an actual continuous path is a bounded linear map on
bounded continuous functions. This supplies the closed FTC graph constraints. -/

open MeasureTheory
noncomputable section

namespace Yau.Proofs.F05Aux

variable {Z V : Type*} [TopologicalSpace Z] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V]

def F05PathIntegral (γ : ℝ → Z) (hγ : Continuous γ) (a b : ℝ) :
    BoundedContinuousFunction Z V →L[ℝ] V :=
  ({ toFun := fun f : BoundedContinuousFunction Z V => ∫ r in a..b, f (γ r)
     map_add' := by
       intro f g
       change (∫ r in a..b, f (γ r)+g (γ r)) = _
       exact intervalIntegral.integral_add ((f.continuous.comp hγ).intervalIntegrable a b)
         ((g.continuous.comp hγ).intervalIntegrable a b)
     map_smul' := by
       intro c f
       change (∫ r in a..b, c • f (γ r)) = _
       exact intervalIntegral.integral_smul c (fun r => f (γ r)) } :
    BoundedContinuousFunction Z V →ₗ[ℝ] V).mkContinuous |b-a| (by
      intro f
      exact (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun r hr => f.norm_coe_le_norm (γ r))).trans_eq (mul_comm _ _))

theorem F05PathIntegral_apply (γ : ℝ → Z) (hγ : Continuous γ) (a b : ℝ)
    (f : BoundedContinuousFunction Z V) :
    F05PathIntegral γ hγ a b f = ∫ r in a..b, f (γ r) := rfl

theorem F05PathIntegral_norm_le (γ : ℝ → Z) (hγ : Continuous γ) (a b : ℝ) :
    ‖F05PathIntegral (V := V) γ hγ a b‖ ≤ |b-a| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
  intro f
  exact (intervalIntegral.norm_integral_le_of_norm_le_const
    (fun r hr => f.norm_coe_le_norm (γ r))).trans_eq (mul_comm _ _)

end Yau.Proofs.F05Aux
