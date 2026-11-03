import Yau.Proofs.P06ExteriorHeatLimit
import Yau.Proofs.P06ScalarUniquenessRicciPositive

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexOrder Matrix

namespace Yau.NodeProofs.P06Aux.ExteriorHeat
open Yau Yau.Blueprint Yau.LeafProofs L03
variable {n : ℕ}

/-- The constructed smooth limit of the original cutoff heat preserves closedness.
The manifold's original geometry supplies the Ricci and Kähler hypotheses. -/
theorem canonical_cutoff_localSmoothLimit_closed
    (X : KahlerManifold n) (μ : Measure X.manifold.Carrier)
    (hμ : IsRiemannianVolume X.metric.form μ)
    (A : RealForm X.manifold 2) (hA : BoundedOneOneData X.metric.form A)
    (hclosed : ClosedRealForm A) (o : X.manifold.Carrier)
    (χ : ℕ → X.manifold.Carrier → ℝ) (hχ : MetricCutoffFamily X.metric.form o χ)
    (Us : ℕ → ℝ → RealForm X.manifold 2) (U : ℝ → RealForm X.manifold 2)
    (hUsL2 : ∀ j, 1 ≤ j → ∀ t, 0 < t → L2RealForm X.metric.form μ (Us j t))
    (hrep : ∀ j (hj : 1 ≤ j) t (ht : 0 < t),
      realizeActualForm X.metric μ (Us j t) (hUsL2 j hj t ht) =
        hodgeHeatHilbert X.metric μ hμ 2 t (cutoffVector X.metric μ hμ o χ hχ A hA.1 j hj))
    (hU : ∀ t, 0 < t → SmoothRealForm (U t)) (hlimit : FormHeatLocalSmoothLimit Us U) :
    ∀ t, 0 < t → ClosedRealForm (U t) := by
  obtain ⟨C,hC,horder⟩ := hA.2.2
  have hb (x : X.manifold.Carrier) : formNormSq X.metric.form A x ≤ (((n:ℝ)+1)*C)^2 := by
    have hn : (n:ℝ) ≤ ((n:ℝ)+1)^2 := by nlinarith [sq_nonneg (n:ℝ)]
    calc
      _ ≤ (n:ℝ)*C^2 := G04Aux.norm_of_order X.metric.form A hA.2.1 hC horder x
      _ ≤ ((n:ℝ)+1)^2*C^2 := mul_le_mul_of_nonneg_right hn (sq_nonneg C)
      _ = _ := by ring
  exact canonical_cutoff_localSmoothLimit_closed_general X.metric X.kahler_metric
    (kahlerManifold_ricci_posSemidef X) μ hμ A hA.1 hclosed (((n:ℝ)+1)*C) hb o χ hχ Us U hUsL2 hrep hU hlimit

end Yau.NodeProofs.P06Aux.ExteriorHeat
