import Yau.Proofs.C01RealTangentRicciJets
import Yau.Proofs.C01ScalarDistanceGrowth

/-! The genuine real Ricci trace has the same quadratic distance
bound as the scalar curvature, relative to the actual tangent speed. -/

noncomputable section
open scoped Topology Manifold ContDiff

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint Yau.LeafProofs.L12Aux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_realRicci_quadratic_distance_bound
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ t, 0 < t → t ≤ T → ∀ (x : Pt X)
      (v : TangentSpace 𝓘(ℝ, ComplexVector n) x),
      0 ≤ actualRealRicciQuadratic (h t) x v ∧
        actualRealRicciQuadratic (h t) x v ≤
          (C * (1 + inducedDistance (h t) x o ^ 2) / t) * realTangentSpeedSq (h t) x v := by
  obtain ⟨C, hC, hb⟩ := localizedFlow_scalar_quadratic_distance_bound hflow hjoint T hT
  refine ⟨C, hC, ?_⟩
  intro t ht htT x v
  have hR := localizedFlow_realRicciQuadratic_bounds hflow hjoint t ht.le x v
  have hv : 0 ≤ realTangentSpeedSq (h t) x v :=
    mul_nonneg (by norm_num) (hermitianNormSq_nonneg _ _)
  exact ⟨hR.1, hR.2.trans (mul_le_mul_of_nonneg_right (hb t ht htT x) hv)⟩

theorem localizedFlow_realTangentSpeedSq_contDiffOn
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    ContDiffOn ℝ ∞ (fun t => realTangentSpeedSq (h t) x v) (Set.Ici 0) := by
  have heq : (fun t => realTangentSpeedSq (h t) x v) =
      (fun t => 2 * matrixQuadraticReal (gMat (h t) x)
        (tangentCoords x x (realTangentEquiv x v))) := by
    funext t
    exact realTangentSpeedSq_eq_matrix (h t) x v
  rw [heq]
  exact contDiffOn_const.mul (localizedFlow_metric_quadratic_contDiffOn hflow x
    (WithLp.ofLp (tangentCoords x x (realTangentEquiv x v))))

end Yau.NodeProofs.C01Aux
