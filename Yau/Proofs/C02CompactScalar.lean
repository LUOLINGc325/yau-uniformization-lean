import Yau.Proofs.C02ScalarHarnack
import Yau.Proofs.C02MetricSlice
import Yau.Proofs.C02DistanceOrder

/-! One scalar-curvature bound for all late times and all moving balls whose
centres range over an arbitrary compact subset of the original manifold. -/

noncomputable section
open Set
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
variable {n : ℕ} {X : KahlerManifold n}

theorem scalarCurvature_bound_on_compact_centered_balls
    (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hC01 : HarnackCompleteness X o h)
    (K : Set (Pt X)) (hK : IsCompact K) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 1 ≤ t → ∀ p ∈ K, ∀ x : Pt X,
      distFrom (h t) p x ≤ R → scalarCurvature (h t) x ≤ B := by
  have hg : MetricSmooth X.metric.form := L12Aux.metricSmooth_of_smoothMetric X.metric
  obtain ⟨D, hD⟩ := hK.bddAbove_image
    (L23Aux.continuous_distFrom X.metric.form hg o).continuousOn
  obtain ⟨B, hBpos, hB⟩ := scalarCurvature_bound_on_harnack_radius o h hC01
    (R + max D 0) (add_nonneg hR (le_max_right D 0))
  refine ⟨B, hBpos, ?_⟩
  intro t ht p hp x hx
  have ht0 : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ 1).trans ht
  have hSmooth : MetricSmooth (h t) := metricFamilySmooth_slice hloc.1.2.1 ht0
  have hInitial : inducedDistance (h t) p o ≤ inducedDistance X.metric.form p o :=
    inducedDistance_le_of_gMat_order (h t) X.metric.form hSmooth hg
      (hloc.2.2.2.2.1 t ht0) p o
  have hBase : inducedDistance X.metric.form p o ≤ max D 0 := by
    rw [L23Aux.inducedDistance_symm X.metric.form hg p o]
    exact (hD (mem_image_of_mem (inducedDistance X.metric.form o) hp)).trans (le_max_left D 0)
  have hTriangle := L23Aux.inducedDistance_triangle (h t) hSmooth x p o
  rw [L23Aux.inducedDistance_symm (h t) hSmooth x p] at hTriangle
  have hRadius : inducedDistance (h t) x o ≤ R + max D 0 := by
    change inducedDistance (h t) p x ≤ R at hx
    linarith
  apply hB t ht x
  change |inducedDistance (h t) x o| ≤ R + max D 0
  rw [abs_of_nonneg (L23Aux.inducedDistance_nonneg (h t) hSmooth x o)]
  exact hRadius

end Yau.Blueprint.C02Proof
