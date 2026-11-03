import Yau.Proofs.V04FejerConvolution
import Yau.Proofs.V04MatrixFejerError
import Yau.Proofs.V04DiscMatrixMaximum

/-! The actual positive-kernel bound controls every frozen polynomial
column on the closed disc. The bound is independent of the frequency
and keeps the given disc and frame throughout. -/

open MeasureTheory AddCircle
open scoped Topology Matrix ComplexOrder ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n q : ℕ} {X : KahlerManifold n}

theorem matrix_entry_norm_le_rectOpNorm (A : CotangentMatrix n) (i j : CotangentIndex n) :
    ‖A i j‖ ≤ rectOpNorm A := by
  let L := (Matrix.toEuclideanLin A).toContinuousLinearMap
  let v : EuclideanSpace ℂ (CotangentIndex n) := PiLp.single 2 j (1 : ℂ)
  have hv : ‖v‖ = 1 := by simp [v, PiLp.norm_single]
  have hentry : ‖A i j‖ ≤ ‖L v‖ := by
    have hh := PiLp.norm_apply_le (L v) i
    change ‖(A *ᵥ Pi.single j (1 : ℂ)) i‖ ≤ ‖L v‖ at hh
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hh
  have hop := L.le_opNorm v
  rw [hv, mul_one] at hop
  exact hentry.trans hop

theorem fejerMean_entry_norm_le (A : ℝ → CotangentMatrix n)
    (hA : ∀ i k, Continuous (fun θ => A θ i k))
    (hp : ∀ i k, Function.Periodic (fun θ => A θ i k) (2 * Real.pi))
    {M : ℝ} (hM : ∀ θ i k, ‖A θ i k‖ ≤ M) (P : ℕ) (θ : ℝ) (i k : CotangentIndex n) :
    ‖fejerMean A P θ i k‖ ≤ M := by
  rw [fejerMean_entry_eq_scalarFejer A hp]
  apply scalarFejer_norm_le (periodic_lift_continuous (hp i k) (hA i k))
  intro y
  induction y using Quotient.inductionOn' with
  | h t => exact hM t i k

theorem closedDisc_holomorphic_norm_le {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) {M : ℝ}
    (hboundary : ∀ θ, ‖f (circlePoint θ)‖ ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) : ‖f z‖ ≤ M := by
  have hd : DiffContOnCl ℂ f (Metric.ball 0 1) :=
    ((hf.differentiableOn (by simp)).mono Metric.closure_ball_subset_closedBall).diffContOnCl
  apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd ?_ ?_
  · intro w hw
    have hwn : ‖w‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using Metric.frontier_ball_subset_sphere hw
    have hc : circlePoint (Complex.arg w) = w := by
      simpa only [circlePoint, hwn, Complex.ofReal_one, one_mul] using
        Complex.norm_mul_exp_arg_mul_I w
    rw [← hc]
    exact hboundary _
  · simpa only [closure_ball _ one_ne_zero] using hz

theorem fejerTestColumn_closedDisc_bound {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} (ha : 4 ≤ a) {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {E : ℂ → CotangentMatrix n} (hE : NormalizedDiscFrame d.G F.f E) {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ θ, (boundarySymbol d j a F E (circlePoint θ)).IsHermitian ∧
      rectOpNorm (boundarySymbol d j a F E (circlePoint θ)) ≤ M)
    (P : ℕ) (i : CotangentIndex n) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ∑ r, ‖fejerTestColumn d j a F E P i z r‖ ^ 2 ≤ (2 * n : ℕ) * M ^ 2 := by
  let A := fun θ => matrixNegative (boundarySymbol d j a F E (circlePoint θ))
  have hA : ∀ r k, Continuous (fun θ => A θ r k) := matrixNegative_entry_continuous
    (fun r k => (boundarySymbol_trace_contDiff hd j a ha F hF E hE r k).continuous)
    (fun θ => (hT θ).1)
  have hp : ∀ r k, Function.Periodic (fun θ => A θ r k) (2 * Real.pi) :=
    fun r k => circleTrace_periodic (fun z => matrixNegative (boundarySymbol d j a F E z) r k)
  have hentry : ∀ θ r k, ‖A θ r k‖ ≤ M := fun θ r k =>
    (matrix_entry_norm_le_rectOpNorm _ r k).trans
      ((rectOpNorm_negative_le _ (hT θ).1).trans (hT θ).2)
  have hcol : ∀ r z, z ∈ Metric.closedBall (0 : ℂ) 1 →
      ‖fejerTestColumn d j a F E P i z r‖ ≤ M := by
    intro r z hz
    apply closedDisc_holomorphic_norm_le (fejerTestColumn_holomorphic d j a F E P i r) ?_ hz
    intro θ
    rw [fejerTestColumn_boundary, norm_mul, norm_pow]
    have hcircle : ‖circlePoint θ‖ = 1 := by simp [circlePoint, Complex.norm_exp]
    rw [hcircle, one_pow, one_mul]
    exact fejerMean_entry_norm_le A hA hp hentry P θ r i
  intro z hz
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun r _ =>
    (sq_le_sq₀ (norm_nonneg _) hM).mpr (hcol r z hz))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, two_mul] using hh

end Yau.Blueprint.V04Proof
