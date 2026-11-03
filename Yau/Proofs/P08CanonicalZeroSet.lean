import Yau.Proofs.P08LogFatou

/-! The uniformly bounded regularized logarithms force nullity of the actual
canonical zero set on the whole manifold, by a countable ball exhaustion. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace Yau.NodeProofs.P08Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem canonical_zero_set_null_of_regularized_ball_bounds (g : SmoothMetric M)
    (S : CanonicalSection M) (hS : IsHolomorphicCanonical S)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) (C : ℝ)
    (hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ L : ℝ, 1 ≤ L →
      BallIntegralLE g.form μ o (fun x => |Real.log (canonicalNormSq g.form S x + ε)|) L (C * L)) :
    μ {x | canonicalNormSq g.form S x = 0} = 0 := by
  let q := canonicalNormSq g.form S
  have hq : Measurable q :=
    (L18Aux.continuous_of_smoothFn (Yau.Proofs.P04Aux.canonicalNormSq_smooth g S hS)).measurable
  have hnull (j : ℕ) : μ ({x | q x = 0} ∩ distBall g.form o ((j : ℝ) + 1)) = 0 := by
    have hL : 1 ≤ (j : ℝ) + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg j)
    have hvol := L18Aux.riemannianVolume_distBall_lt_top g μ hμ o
      (lt_of_lt_of_le zero_lt_one hL)
    have hfin : ENNReal.ofReal (C * ((j : ℝ) + 1)) * μ (distBall g.form o ((j : ℝ) + 1)) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol
    have hz := zero_set_null_of_regularized_bound
      (μ.restrict (distBall g.form o ((j : ℝ) + 1))) q hq _ hfin
      (fun k => hbound _ (logRegularizationParameter_pos k) (logRegularizationParameter_le_one k) _ hL)
    rwa [Measure.restrict_apply (measurableSet_eq_fun hq measurable_const)] at hz
  apply measure_mono_null ?_ (measure_iUnion_null hnull)
  intro x hx
  obtain ⟨j, hj⟩ := exists_nat_gt (distFrom g.form o x)
  apply Set.mem_iUnion.mpr
  refine ⟨j, hx, ?_⟩
  apply (L12Aux.mem_distBall_iff g o x (by positivity : 0 < (j : ℝ) + 1)).mpr
  change distFrom g.form o x < (j : ℝ) + 1
  linarith

end Yau.NodeProofs.P08Aux
