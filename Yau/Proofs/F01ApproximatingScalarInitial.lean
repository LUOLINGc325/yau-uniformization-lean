import Yau.Proofs.F01InitialScalarNonneg
import Yau.Proofs.F01ConformalScalarCurvature
import Yau.Proofs.F01ApproximatingRicci
import Yau.Proofs.F01AmbientBisectionalNonneg

/-! One constant before every approximation level bounds the actual
initial negative scalar curvature by C/L², using the original controlled
exhaustion and the ambient curvature. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem controlled_approximating_negative_scalar_initial
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (ho : u o < L),
      ∀ x : (sublevelManifold X.manifold u hu.1 o L ho).Carrier,
        -scalarCurvature (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) x ≤ C / L ^ 2 := by
  obtain ⟨A, hA, B, hB, hb⟩ := controlled_conformal_gradient_levi X o u hu
  refine ⟨((n : ℝ) + 1) ^ 2 * B, by positivity, ?_⟩
  intro L ho x
  have hL : 0 < L := (zero_lt_one.trans_le (hu.2.2.1 o)).trans ho
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let g0 : HermitianField N := approximatingBaseMetric X.manifold X.metric.form u hu.1 o L ho
  let f : N.Carrier → ℝ := approximatingScalar X.manifold u hu.1 o L ho
  have hg0 : MetricSmooth g0 := openRestrictedField_metricSmooth X.manifold
    (sublevelOpens X.manifold u hu.1 o L) (sublevelComponent_isConnected ho)
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)
  have hf : SmoothFn f := approximatingScalar_smoothFn u hu.1 o hL ho
  have hscalar : 0 ≤ scalarCurvature g0 x := by
    unfold scalarCurvature
    dsimp only [g0, approximatingBaseMetric]
    erw [openRestrictedField_gMat X.manifold (sublevelOpens X.manifold u hu.1 o L)
      (sublevelComponent_isConnected ho) X.metric.form x,
      openRestrictedField_ricci (sublevelOpens X.manifold u hu.1 o L)
        (sublevelComponent_isConnected ho) X.metric.form x]
    exact scalarCurvature_nonneg_of_nonnegBisectional X.metric (kahlerManifold_nonnegBisectional X) x.val
  have hupper := conformalField_negative_scalar_upper g0 hg0 f hf x hscalar (hb L ho x).2.2
  change -scalarCurvature (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) x ≤
    (n : ℝ) ^ 2 * (B / L ^ 2) at hupper
  have hcoef : (n : ℝ) ^ 2 * B ≤ ((n : ℝ) + 1) ^ 2 * B :=
    mul_le_mul_of_nonneg_right (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hB.le
  calc
    _ ≤ (n : ℝ) ^ 2 * (B / L ^ 2) := hupper
    _ = ((n : ℝ) ^ 2 * B) / L ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hcoef (sq_nonneg L)

end Yau.NodeProofs.F01Aux
