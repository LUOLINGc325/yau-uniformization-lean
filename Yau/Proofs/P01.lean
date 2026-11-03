import Yau.Proofs.P01RayCompact
import Yau.Proofs.P01BusemannTail

noncomputable section
open scoped NNReal

namespace Yau.NodeProofs.P01Aux
open Yau Yau.Blueprint

theorem exists_project_ray {n : ℕ} (X : KahlerManifold n) (o : Pt X) :
    ∃ ray : ℝ≥0 → Pt X, ray 0 = o ∧
      ∀ s t, distFrom X.metric.form (ray s) (ray t) =
        |(t : ℝ) - (s : ℝ)| := by
  letI := Yau.LeafProofs.L12Aux.inducedMetricSpace X.metric
  letI := Yau.LeafProofs.L12Aux.inducedMetricSpace_proper X.metric
  letI : NoncompactSpace (Pt X) := X.manifold.noncompact
  have hrad : ∀ (x y : Pt X) {r : ℝ}, 0 ≤ r → r ≤ dist x y →
      ∃ z : Pt X, dist x z = r ∧ dist z y = dist x y - r := by
    intro x y r hr0 hr
    exact Yau.LeafProofs.L12Aux.exists_exact_radial X.metric x y hr0 hr
  change ∃ ray : ℝ≥0 → Pt X, ray 0 = o ∧
    ∀ s t, dist (ray s) (ray t) = |(t : ℝ) - (s : ℝ)|
  exact @exists_isometric_ray_of_exact_radial (Pt X)
    (Yau.LeafProofs.L12Aux.inducedMetricSpace X.metric)
    (Yau.LeafProofs.L12Aux.inducedMetricSpace_proper X.metric)
    X.manifold.noncompact hrad o

end Yau.NodeProofs.P01Aux

namespace Yau.NodeProofs

theorem P01_proved : Yau.Blueprint.P01 := by
  intro n X o
  obtain ⟨ray, hzero, hray⟩ := P01Aux.exists_project_ray X o
  exact P01Aux.busemannConclusion_of_isometric_ray X o ray hzero hray

theorem P01_contract_proved : Yau.BlueprintContracts.P01_contract := P01_proved

end Yau.NodeProofs
