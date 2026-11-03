import Yau.Proofs.F05AtlasHomeomorph
import Yau.LeafProofs.L18

/-! A smooth finite partition on a neighborhood of the actual compact closure.
Every support lies strictly inside its own radius-one-quarter chart. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.HeatConcreteBindings Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_finite_atlas_partition {O : Set M.Carrier} (hO : SmoothPrecompactDomain O)
    (A : AtlasData M) (hA : GenuineAtlas O A)
    (hSmall : closure O ⊆ ⋃ i, lift A i '' region (A.normal i) (1/8)) :
    ∃ χ : Fin A.count → M.Carrier → ℝ, F05Partition O A χ := by
  classical
  letI := Yau.LeafProofs.L12Aux.manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := Yau.LeafProofs.L12Aux.manifold_locallyCompact M
  let U : Fin A.count → Set M.Carrier := fun i => lift A i '' Metric.ball 0 (1/4)
  have hU (i : Fin A.count) : IsOpen (U i) := F05_lift_ball_isOpen hA i (by norm_num)
  have hCover : closure O ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp (hSmall hx)
    apply mem_iUnion.mpr
    refine ⟨i,z,?_,rfl⟩
    rw [Metric.mem_ball,dist_zero_right]
    exact hz.1.trans_lt (by norm_num)
  obtain ⟨V,hV,hKV,hVW⟩ := normal_exists_closure_subset
    hO.2.2.2.1.isClosed (isOpen_iUnion hU) hCover
  obtain ⟨p,hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ,Space n)) isClosed_closure U hU hVW
  refine ⟨fun i => p i,?_,p.nonneg,?_,V,hV,hKV,?_⟩
  · intro i
    exact Yau.LeafProofs.L18Aux.smoothFn_of_contMDiff_real (p i).contMDiff
  · intro i x hx
    obtain ⟨z,hz,rfl⟩ := hp i hx
    exact ⟨z,Metric.ball_subset_closedBall hz,rfl⟩
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one (subset_closure hx)

end Yau.Proofs.F05Aux
