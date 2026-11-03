import Yau.Proofs.P08CanonicalAverage
import Yau.Proofs.P08CanonicalZeroSet

/-! Nullity of the genuine canonical zero set is a proved consequence of
its original growth and nonzero-at-basepoint conditions. -/
noncomputable section
open MeasureTheory
namespace Yau.NodeProofs.P08Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem canonical_zero_set_null (X : KahlerManifold n) (o : Pt X)
    (S : CanonicalSection X.manifold) (hS : IsHolomorphicCanonical S) (ho : S o ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ x, Real.log (canonicalNormSq X.metric.form S x) ≤
      C * (1 + distFrom X.metric.form o x)) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) :
    μ {x | canonicalNormSq X.metric.form S x = 0} = 0 := by
  obtain ⟨C, _, hC⟩ := canonical_regularized_averages X o S hS ho hgrowth
  exact canonical_zero_set_null_of_regularized_ball_bounds X.metric S hS μ hμ o C (hC μ hμ)

end Yau.NodeProofs.P08Aux
