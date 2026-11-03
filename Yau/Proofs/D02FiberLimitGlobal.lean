import Yau.Proofs.D02FiberLimitLocal

open scoped Manifold Topology ContDiff
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02FiberLimitAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.NodeProofs.D02Aux Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

/-- Intrinsic uniqueness glues the local reconstructed covectors. The total
function is zero outside Δ, and each local formula uses the required fixed
chart centered at f(z₀). -/
theorem global_fiber_limit {n m : ℕ} {M : ComplexManifold n} (g : SmoothMetric M)
    (V : Fin m → VectorField M) (hV : ∀ a, IsHolomorphicField (V a))
    (hspan : ∀ x, Submodule.span ℂ (Set.range fun i ↦ V i x) = ⊤)
    (fs : ℕ → ℂ → M.Carrier) (ξs : ℕ → ℂ → Covector n)
    (hfs : ∀ j, IsCotangentDisc (fs j) (ξs j))
    (f : ℂ → M.Carrier) (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f (ball 0 1))
    (hconv : letI := L12Aux.inducedMetricSpace g;
      TendstoLocallyUniformlyOn fs f atTop (ball 0 1))
    (e : ℂ → (Fin m → ℂ)) (he : DifferentiableOn ℂ e (ball 0 1))
    (heconv : TendstoLocallyUniformlyOn
      (fun j z ↦ evaluationVector V (fs j z, ξs j z)) e atTop (ball 0 1)) :
    ∃ ξ : ℂ → Covector n, ∀ z₀ ∈ ball (0 : ℂ) 1, ∃ W ∈ 𝓝 z₀,
      DifferentiableOn ℂ (fun z ↦ covectorCoords (f z₀) (f z) (ξ z)) W ∧
      TendstoUniformlyOn (fun j z ↦ covectorCoords (f z₀) (fs j z) (ξs j z))
        (fun z ↦ covectorCoords (f z₀) (f z) (ξ z)) atTop W := by
  classical
  have hpoint : ∀ z ∈ ball (0 : ℂ) 1, ∃ ξ : Covector n,
      ∀ i, fieldEvaluation (V i) (f z, ξ) = e z i := by
    intro z hz
    obtain ⟨R, η, hR, hRD, hmap, hη, hηconv, heq⟩ :=
      local_fiber_limit g V hV hspan fs ξs hfs f hf hconv e he heconv hz
    exact ⟨covectorOfCoords (f z) (f z) (η z), heq z (mem_closedBall_self hR.le)⟩
  choose ξpoint hξpoint using hpoint
  let ξ : ℂ → Covector n := fun z ↦ if hz : z ∈ ball (0 : ℂ) 1 then ξpoint z hz else 0
  have hξ : ∀ z ∈ ball (0 : ℂ) 1, ∀ i, fieldEvaluation (V i) (f z, ξ z) = e z i := by
    intro z hz
    simpa only [ξ, dif_pos hz] using hξpoint z hz
  refine ⟨ξ, ?_⟩
  intro z₀ hz₀
  obtain ⟨R, η, hR, hRD, hmap, hη, hηconv, heq⟩ :=
    local_fiber_limit g V hV hspan fs ξs hfs f hf hconv e he heconv hz₀
  have hcoords : ∀ z ∈ closedBall z₀ R, covectorCoords (f z₀) (f z) (ξ z) = η z := by
    intro z hz
    have hident : ξ z = covectorOfCoords (f z₀) (f z) (η z) :=
      field_evaluation_injective V hspan (f z) (fun i ↦ (hξ z (hRD hz) i).trans (heq z hz i).symm)
    rw [hident, covectorCoords_ofCoords (f z₀) (f z) (hmap hz) (η z)]
  refine ⟨ball z₀ R, ball_mem_nhds z₀ hR, ?_, ?_⟩
  · exact hη.congr (fun z hz ↦ hcoords z (ball_subset_closedBall hz))
  · exact (hηconv.mono ball_subset_closedBall).congr_right
      (fun z hz ↦ (hcoords z (ball_subset_closedBall hz)).symm)

end Yau.NodeProofs.D02FiberLimitAux
