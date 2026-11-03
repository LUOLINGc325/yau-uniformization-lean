import Yau.Proofs.C02CurvatureScalarBound
import Yau.Proofs.C02CompactScalar
import Yau.Proofs.C02CompleteMetric

/-! A single original curvature bound holds on every late moving ball
with centre in a fixed compact set. Completeness is taken from C01 and
used to construct the same-field metric record, rather than assumed. -/

noncomputable section
open Set
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {X : KahlerManifold n}

theorem curvatureJetNorm_zero_bound_on_compact_centered_balls
    (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hC01 : HarnackCompleteness X o h)
    (K : Set (Pt X)) (hK : IsCompact K) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 1 ≤ t → ∀ p ∈ K, ∀ x : Pt X,
      distFrom (h t) p x ≤ R → curvatureJetNorm (h t) 0 x ≤ B := by
  obtain ⟨D, hD, hGeometry⟩ := exists_curvatureJetNorm_zero_scalar_bound n
  obtain ⟨B, hB, hScalar⟩ := scalarCurvature_bound_on_compact_centered_balls o h U P ρ hloc hC01 K hK R hR
  refine ⟨D * B, mul_pos hD hB, ?_⟩
  intro t ht p hp x hx
  have ht0 : 0 < t := (by norm_num : (0 : ℝ) < 1).trans_le ht
  let g := completeFlowSlice X o h hloc.1 hC01 t ht0
  have hBisec : NonnegBisectional g.form := hC01.1 t ht0.le
  exact (hGeometry X.manifold g hBisec x).trans
    (mul_le_mul_of_nonneg_left (hScalar t ht p hp x hx) hD.le)

end Yau.Blueprint.C02Proof
