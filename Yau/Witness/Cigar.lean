import Yau.Witness.CigarCurvature
import Yau.Witness.CigarComplete

noncomputable section
namespace Yau
namespace Witness.Cigar

/-- The genuine complete cigar metric, with real metric `(dx² + dy²)/(1 + |z|²)`. -/
def cigarMetric : SmoothMetric cigarPlane :=
  Yau.Proofs.C04ChartsAux.smoothMetric_of_complete_field
    cigarField cigar_metricSmooth cigar_kahlerClosed cigar_completeDistance

@[simp] theorem cigarMetric_form : cigarMetric.form = cigarField := rfl

/-- The complete positively curved cigar on the standard complex line. -/
def cigarKahlerManifold : KahlerManifold 1 where
  manifold := cigarPlane
  metric := cigarMetric
  smooth_metric := cigarMetric.coordinate_smooth
  complete_metric := cigarMetric.complete_distance
  kahler_metric := cigarMetric.kahler_equations
  positive_bisectional_curvature := by
    change PaperPositiveBisectional cigarField
    exact cigar_paperPositive

end Witness.Cigar

/-- The complete cigar metric on the complex line supplies a genuine
inhabited instance of the hypotheses of Theorem 1.1. -/
theorem kahlerManifold_one_nonempty : Nonempty (KahlerManifold 1) :=
  ⟨Witness.Cigar.cigarKahlerManifold⟩

end Yau
