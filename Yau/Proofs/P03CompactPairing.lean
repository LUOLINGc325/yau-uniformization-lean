import Yau.Geometry.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

open scoped Topology ENNReal
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {A K : Type*} [TopologicalSpace A] [TopologicalSpace K]
  [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
  (μ : Measure K) [IsFiniteMeasure μ]

/-- Integration against a fixed continuous weight on a genuine compact
parameter set, after continuous restriction from the original domain. -/
def compactPairingCLM (j : C(K, A)) (w : C(K, ℂ)) : C(A, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp ((ContinuousMap.toLp 1 μ ℂ).comp
    ((ContinuousLinearMap.mul ℂ C(K, ℂ) w).comp
      (ContinuousMap.compCLM (R := ℂ) ℂ j)))

theorem compactPairingCLM_apply (j : C(K, A)) (w : C(K, ℂ)) (f : C(A, ℂ)) :
    compactPairingCLM μ j w f = ∫ z, w z * f (j z) ∂μ := by
  change L1.integralCLM' ℂ (ContinuousMap.toLp 1 μ ℂ (w * f.comp j)) = _
  rw [← L1.integral_eq' ℂ, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (μ := μ) (𝕜 := ℂ)
    (w * f.comp j))

theorem continuous_compactPairing (j : C(K, A)) (w : C(K, ℂ)) :
    Continuous (fun f : C(A, ℂ) => ∫ z, f (j z) * w z ∂μ) := by
  exact (compactPairingCLM μ j w).continuous.congr (fun f => by
    rw [compactPairingCLM_apply]
    simp only [mul_comm])

theorem isClosed_compactPairing_zero (j : C(K, A)) (w : C(K, ℂ)) :
    IsClosed {f : C(A, ℂ) | (∫ z, f (j z) * w z ∂μ) = 0} :=
  isClosed_eq (continuous_compactPairing μ j w) continuous_const

end Yau.NodeProofs.P03Aux
