import Yau.LeafProofs.L23FieldMetric
import Yau.LeafProofs.L23LocalDistanceSupportContracts

/-! A globally smooth actual constant-speed path is an admissible length
curve, with exactly the same genuine length used in the frozen distance. -/

noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem integrableCurve_length_of_constant_speed (h : HermitianField M) (hh : MetricSmooth h)
    (γ : ℝ → M.Carrier) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ)
    (D : ℝ) (hD : 0 ≤ D)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, actualSpeedSq h γ t = D ^ 2) :
    curveLength h (L23Aux.integrableCurve_of_contMDiff h hh hγ).1 = D := by
  let δ := L23Aux.integrableCurve_of_contMDiff h hh hγ
  have hvel (t : ℝ) : realTangentEquiv (γ t) (realCurveVelocity γ t) =
      realTangentDerivative δ.1 t := by
    exact (realCurveVelocity_chart hγ.continuous.continuousAt
      ((contDiffAt_chart_of_contMDiff hγ t).differentiableAt (by norm_num))).trans
        (realTangentDerivative_eq_chart δ.1 t).symm
  have hs (t : ℝ) : curveSpeed h δ.1 t = Real.sqrt (actualSpeedSq h γ t) := by
    unfold actualSpeedSq
    rw [underlyingRealRiemannianMetric_inner, hvel t]
    rfl
  change (∫ t in Icc (0 : ℝ) 1, curveSpeed h δ.1 t) = D
  calc
    _ = ∫ _t in Icc (0 : ℝ) 1, D := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [hs t, hspeed t ht, Real.sqrt_sq hD]
    _ = D := by simp

end Yau.Proofs.C03Aux
