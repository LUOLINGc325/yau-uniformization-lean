import Yau.Proofs.P08ScalarAverageIntegral
import Yau.Proofs.P08ScalarAverageLimit
import Yau.Proofs.P08ExhaustionCutoffs
import Yau.Proofs.P08CanonicalZeroSet
import Yau.LeafProofs.L12MinimizingJacobi

/-! The scalar-curvature half of the original canonical averages follows
from the natural uniform regularized logarithmic estimates and the frozen
controlled exhaustion. Constants are fixed before the volume and the radius. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Matrix ComplexOrder ENNReal
namespace Yau.NodeProofs.P08Aux.ScalarAverage
open Yau Yau.Blueprint Yau.LeafProofs
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem cutoff_scale_identity (A B ρ L : ℝ) (hL : L ≠ 0) :
    (A / L ^ 2) * (B * (ρ * L)) * ρ ^ (2 * n) =
      (A * B * ρ ^ (2 * n + 1)) / L := by
  rw [pow_succ]
  field_simp [hL]
  ring

/-- This helper consumes only estimates for the actual regularized canonical
norm. The P08 producer supplies that natural internal premise. -/
theorem scalar_average_of_regularized_bounds (X : KahlerManifold n) (o : Pt X)
    {u : Pt X → ℝ} (hu : ControlledExhaustion X o u)
    (S : CanonicalSection X.manifold) (hS : IsHolomorphicCanonical S)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ μ, IsRiemannianVolume X.metric.form μ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ L : ℝ, 1 ≤ L →
        BallIntegralLE X.metric.form μ o
          (fun x => |Real.log (canonicalNormSq X.metric.form S x + ε)|) L (B * L)) :
    ∃ C : ℝ, ∀ μ, IsRiemannianVolume X.metric.form μ → ∀ L : ℝ, 1 ≤ L →
      BallIntegralLE X.metric.form μ o (scalarCurvature X.metric.form) L (C / L) := by
  obtain ⟨ρ, A, hρ, hA, hcut⟩ := exists_exhaustion_laplacian_cutoffs X o hu
  refine ⟨A * B * ρ ^ (2 * n + 1), ?_⟩
  intro μ hμ L hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hρL : 1 ≤ ρ * L := hL.trans (by nlinarith [mul_le_mul_of_nonneg_right hρ hLpos.le])
  have hρLpos : 0 < ρ * L := mul_pos hρpos hLpos
  obtain ⟨χ, hχ, hcχ, hχ01, hχone, hχs, hχlap⟩ := hcut L hL
  have hvol : μ (distBall X.metric.form o (ρ * L)) ≤
      ENNReal.ofReal (ρ ^ (2 * n)) * μ (distBall X.metric.form o L) := by
    have h := L12Aux.bishopGromov n X.manifold X.metric X.complete_metric X.kahler_metric
      (P06Aux.kahlerManifold_ricci_posSemidef X) μ hμ o L (ρ * L) hLpos (by nlinarith)
    simpa only [mul_div_cancel_right₀ ρ hLpos.ne'] using h
  have hzero := canonical_zero_set_null_of_regularized_ball_bounds X.metric S hS μ hμ o B
    (hbound μ hμ)
  have hreg (j : ℕ) :
      (∫⁻ x, ENNReal.ofReal (χ x *
        (canonicalNormSq X.metric.form S x /
          (canonicalNormSq X.metric.form S x + logRegularizationParameter j) *
            scalarCurvature X.metric.form x)) ∂μ) ≤
        ENNReal.ofReal ((A * B * ρ ^ (2 * n + 1)) / L) * μ (distBall X.metric.form o L) := by
    have hk : 0 ≤ A / L ^ 2 := div_nonneg hA.le (sq_nonneg L)
    calc
      _ ≤ ENNReal.ofReal (A / L ^ 2) *
          ∫⁻ x in distBall X.metric.form o (ρ * L),
            ENNReal.ofReal |Real.log (canonicalNormSq X.metric.form S x + logRegularizationParameter j)| ∂μ :=
        regularized_cutoff_lintegral_bound X o S hS μ hμ
          (logRegularizationParameter_pos j) hρLpos hk hχ hcχ (fun x => (hχ01 x).1) hχs hχlap
      _ ≤ ENNReal.ofReal (A / L ^ 2) *
          (ENNReal.ofReal (B * (ρ * L)) * μ (distBall X.metric.form o (ρ * L))) :=
        mul_le_mul_right (hbound μ hμ _ (logRegularizationParameter_pos j)
          (logRegularizationParameter_le_one j) _ hρL) _
      _ ≤ ENNReal.ofReal (A / L ^ 2) * (ENNReal.ofReal (B * (ρ * L)) *
          (ENNReal.ofReal (ρ ^ (2 * n)) * μ (distBall X.metric.form o L))) :=
        mul_le_mul_right (mul_le_mul_right hvol _) _
      _ = ENNReal.ofReal ((A / L ^ 2) * (B * (ρ * L)) * ρ ^ (2 * n)) *
          μ (distBall X.metric.form o L) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hk (mul_nonneg hB hρLpos.le)), ENNReal.ofReal_mul hk]
        ac_rfl
      _ = _ := by rw [cutoff_scale_identity A B ρ L hLpos.ne']
  have hlim := regularized_weight_lintegral_limit μ
    (canonicalNormSq X.metric.form S) (scalarCurvature X.metric.form) χ
    (L18Aux.continuous_of_smoothFn (Yau.Proofs.P04Aux.canonicalNormSq_smooth X.metric S hS)).measurable
    (L18Aux.continuous_of_smoothFn (scalarCurvature_smooth X)).measurable
    (L18Aux.continuous_of_smoothFn hχ).measurable hzero _ hreg
  change (∫⁻ x in distBall X.metric.form o L, ENNReal.ofReal (scalarCurvature X.metric.form x) ∂μ) ≤ _
  calc
    _ = ∫⁻ x in distBall X.metric.form o L,
        ENNReal.ofReal (χ x * scalarCurvature X.metric.form x) ∂μ := by
      apply setLIntegral_congr_fun (L12Aux.isOpen_distBall X.metric o L).measurableSet
      intro x hx
      change ENNReal.ofReal (scalarCurvature X.metric.form x) =
        ENNReal.ofReal (χ x * scalarCurvature X.metric.form x)
      rw [hχone x ((L12Aux.mem_distBall_iff X.metric o x hLpos).mp hx).le, one_mul]
    _ ≤ ∫⁻ x, ENNReal.ofReal (χ x * scalarCurvature X.metric.form x) ∂μ :=
      setLIntegral_le_lintegral _ _
    _ ≤ _ := hlim

end Yau.NodeProofs.P08Aux.ScalarAverage
