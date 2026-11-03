import Yau.Proofs.E02InfConvolution
import Mathlib.Topology.MetricSpace.Thickening

open Set Metric
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.E02Aux

/-- One uniform scale puts EVERY actual minimizing source over the fixed
compact evaluation region inside the source compactum's interior. -/
theorem compactInfConvolution_uniform_source_interior {E : Type*} [NormedAddCommGroup E]
    (K S : Set E) (hS : IsCompact S) (hSK : S ⊆ interior K)
    (v : E → ℝ) (hv0 : ∀ a ∈ K, 0 ≤ v a) (M : ℝ) (hM : 0 ≤ M)
    (hSM : ∀ q ∈ S, v q ≤ M) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ < κ₀ →
      ∀ q ∈ S, ∀ a ∈ K,
        compactInfConvolution K v κ q = v a+‖q-a‖^2/(2*κ) → a ∈ interior K := by
  obtain ⟨δ,hδ,hThick⟩ := hS.exists_thickening_subset_open isOpen_interior hSK
  have hDen : 0 < 2*(M+1) := by positivity
  refine ⟨δ^2/(2*(M+1)),div_pos (sq_pos_of_pos hδ) hDen,?_⟩
  intro κ hκ hSmall q hq a ha hMin
  have hDisplace := (compactInfConvolution_source_displacement K v hv0 hκ hM q a
    (interior_subset (hSK hq)) ha (hSM q hq) hMin).1
  have hScale : κ*(2*(M+1)) < δ^2 := (lt_div_iff₀ hDen).mp hSmall
  have hNorm : ‖q-a‖ < δ := by
    nlinarith [norm_nonneg (q-a)]
  apply hThick
  exact mem_thickening_iff.mpr ⟨q,hq,by simpa only [dist_eq_norm,norm_sub_rev] using hNorm⟩

end Yau.NodeProofs.E02Aux
