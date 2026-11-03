import Yau.LeafProofs.L19HeatDualBoundary

/-! The compact-slab boundary error is controlled by actual local energies. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- The localized duality error on a genuine finite heat slab. -/
theorem scalarHeat_localized_pairing_interval_bound (hI : IsOpen I)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u v : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u I) (hv : SmoothSpaceTime v I)
    (hforward : ∀ x t, t ∈ I → HasDerivAt (u x)
      (laplacian g.form (fun y => u y t) x) t)
    (hbackward : ∀ x t, t ∈ I → HasDerivAt (v x)
      (-laplacian g.form (fun y => v y t) x) t)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    {K : Set M.Carrier} (hcompact : IsCompact K)
    (hzero : ∀ t ∈ I, ∀ x, x ∉ K →
      scalarGradientPair g.form η (fun y => u y t) x = 0 ∧
      scalarGradientPair g.form η (fun y => v y t) x = 0)
    {B δ s T : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hbound : ∀ x, scalarGradientPair g.form η η x ≤ B)
    (hslab : Icc s T ⊆ I) (hsT : s ≤ T) :
    |(∫ x, η x * u x T * v x T ∂μ) - (∫ x, η x * u x s * v x s ∂μ)| ≤
      (1 / 2 : ℝ) *
        (δ * (∫ t in s..T, ∫ x in K, u x t ^ 2 ∂μ) +
          δ⁻¹ * (∫ t in s..T, ∫ x in K, v x t ^ 2 ∂μ) +
          (δ * B / 4) * (∫ t in s..T, ∫ x in K,
            scalarGradientPair g.form (fun y => u y t) (fun y => u y t) x ∂μ) +
          (B / (4 * δ)) * (∫ t in s..T, ∫ x in K,
            scalarGradientPair g.form (fun y => v y t) (fun y => v y t) x ∂μ)) := by
  let U : ℝ → ℝ := fun t => ∫ x in K, u x t ^ 2 ∂μ
  let V : ℝ → ℝ := fun t => ∫ x in K, v x t ^ 2 ∂μ
  let A : ℝ → ℝ := fun t => ∫ x in K,
    scalarGradientPair g.form (fun y => u y t) (fun y => u y t) x ∂μ
  let D : ℝ → ℝ := fun t => ∫ x in K,
    scalarGradientPair g.form (fun y => v y t) (fun y => v y t) x ∂μ
  have hU : IntervalIntegrable U volume s T :=
    LocalTime.smoothSpaceTime_integralOn_compact_intervalIntegrable hI g μ hμ
      (fun a => (hu a).pow 2) hcompact hslab hsT
  have hV : IntervalIntegrable V volume s T :=
    LocalTime.smoothSpaceTime_integralOn_compact_intervalIntegrable hI g μ hμ
      (fun a => (hv a).pow 2) hcompact hslab hsT
  have hA : IntervalIntegrable A volume s T :=
    LocalTime.smoothSpaceTime_integralOn_compact_intervalIntegrable hI g μ hμ
      (LocalTime.smoothSpaceTime_scalarGradientPair hI g hu hu) hcompact hslab hsT
  have hD : IntervalIntegrable D volume s T :=
    LocalTime.smoothSpaceTime_integralOn_compact_intervalIntegrable hI g μ hμ
      (LocalTime.smoothSpaceTime_scalarGradientPair hI g hv hv) hcompact hslab hsT
  have hR := (((hU.const_mul δ).add (hV.const_mul δ⁻¹)).add
    (hA.const_mul (δ * B / 4))).add (hD.const_mul (B / (4 * δ)))
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hsT
    (f := fun t => ∫ x, u x t * scalarGradientPair g.form η (fun y => v y t) x -
      v x t * scalarGradientPair g.form η (fun y => u y t) x ∂μ)
    (g := fun t => δ * U t + δ⁻¹ * V t + (δ * B / 4) * A t + (B / (4 * δ)) * D t)
    (ae_of_all _ (fun t ht => by
      have htI := hslab ⟨ht.1.le, ht.2⟩
      simpa only [Real.norm_eq_abs] using scalarHeat_commutator_integral_bound g hK μ hμ
        (smoothSpaceTime_slice hu htI) (smoothSpaceTime_slice hv htI) hη hcη hcompact
        (hzero t htI) hB hδ hbound)) hR
  have h₁ := intervalIntegral.integral_add
    (((hU.const_mul δ).add (hV.const_mul δ⁻¹)).add (hA.const_mul (δ * B / 4)))
    (hD.const_mul (B / (4 * δ)))
  have h₂ := intervalIntegral.integral_add ((hU.const_mul δ).add (hV.const_mul δ⁻¹))
    (hA.const_mul (δ * B / 4))
  have h₃ := intervalIntegral.integral_add (hU.const_mul δ) (hV.const_mul δ⁻¹)
  rw [h₁, h₂, h₃] at hnorm
  simp only [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at hnorm
  rw [LocalTime.scalarHeat_localized_pairing_interval_identity hI g hK μ hμ hu hv
    hforward hbackward hη hcη hslab hsT, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact mul_le_mul_of_nonneg_left hnorm (by norm_num)

end Yau.LeafProofs.L19Aux
