import Yau.Proofs.P06WeakDDbarCurrentGreen

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem ddRealForm_constant (c : ℝ) : G04Aux.ddRealForm (fun _ : M.Carrier => c) = 0 := by
  have hs : SmoothFn (fun _ : M.Carrier => c) := fun _ => contDiffOn_const
  apply realForm_eq_of_center_components
  intro x I
  rw [G04Aux.dd_coefficients _ hs x (z := chartPt x x) (mem_extChartAt_target x) I]
  simp [formComponents, leviC, leviMatrix, wirt, wirtBar, inChart, rDeriv, G04Aux.matrixPairing]

/-- The genuine compact dd-adjoint test annihilates constants. -/
theorem integral_ddAdjointScalar_eq_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (B : RealForm M 2)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ x, WeakCurrent.ddAdjointScalar g.form B x ∂μ) = 0 := by
  have hs : SmoothFn (fun _ : M.Carrier => (1 : ℝ)) := fun _ => contDiffOn_const
  have he := WeakCurrent.integral_dd_eq_adjoint g μ hμ (fun _ => 1) hs B hB hcB
  simpa only [ddRealForm_constant, formInner_zero_left, Pi.zero_apply, integral_zero, one_mul] using he.symm

/-- Passing to the compact difference from the value at infinity leaves
the original global current pairing unchanged. -/
theorem current_pairing_sub_constant (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ) (hf : Continuous f)
    (c : ℝ) (B : RealForm M 2) (hB : SmoothRealForm B)
    (hcB : CompactlySupportedRealForm B) :
    (∫ x, (f x - c) * WeakCurrent.ddAdjointScalar g.form B x ∂μ) =
      ∫ x, f x * WeakCurrent.ddAdjointScalar g.form B x ∂μ := by
  letI : IsLocallyFiniteMeasure μ := Yau.LeafProofs.L18Aux.riemannianVolume_locallyFinite g μ hμ
  have hQ := Yau.LeafProofs.L18Aux.continuous_of_smoothFn (WeakCurrent.ddAdjointScalar_smooth g μ hμ B hB)
  have hcQ := WeakCurrent.ddAdjointScalar_compact g μ hμ B hB hcB
  have hfQ : Integrable (fun x => f x * WeakCurrent.ddAdjointScalar g.form B x) μ :=
    (hf.mul hQ).integrable_of_hasCompactSupport hcQ.mul_left
  have hcI : Integrable (fun x => c * WeakCurrent.ddAdjointScalar g.form B x) μ :=
    (hQ.const_mul c).integrable_of_hasCompactSupport hcQ.mul_left
  calc
    _ = ∫ x, (f x * WeakCurrent.ddAdjointScalar g.form B x -
        c * WeakCurrent.ddAdjointScalar g.form B x) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)
    _ = _ := by rw [integral_sub hfQ hcI, integral_const_mul,
      integral_ddAdjointScalar_eq_zero g μ hμ B hB hcB, mul_zero, sub_zero]

end Yau.NodeProofs.P06Aux
