import Yau.Proofs.F04ChartContinuity

open Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic

/-- A genuine physical cutoff with support INSIDE an open region turns
 actual regional closed-time smoothness into global closed-time smoothness.
 At the exterior spatial boundary the product has a TRUE zero germ; no
 regularity of the finite-domain function there is assumed. -/
theorem physical_spatial_cutoff_smooth
    {n : ℕ} {M : ComplexManifold n} {Ω : Set M.Carrier} (hΩ : IsOpen Ω)
    {I : Set ℝ} {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ) (hψΩ : tsupport ψ ⊆ Ω)
    {v : M.Carrier → ℝ → ℝ}
    (hv : ∀ c, ContDiffOn ℝ ∞ (fun p : Point n => v (chartInv c p.1) p.2)
      ((chartTarget c ∩ chartInv c ⁻¹' Ω) ×ˢ I)) :
    SmoothSpaceTime (fun x t => ψ x * v x t) I := by
  intro c p hp
  have hPsi : ContDiffOn ℝ ∞ (fun q : Point n => ψ (chartInv c q.1)) (chartTarget c ×ˢ I) :=
    (hψ c).comp contDiffOn_fst (fun q hq => hq.1)
  have hInv : ContinuousAt (fun q : Point n => chartInv c q.1) p :=
    ((continuousOn_extChartAt_symm (I := ComplexModel n) c).continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hp.1)).comp continuousAt_fst
  by_cases hy : chartInv c p.1 ∈ Ω
  · have hNear := hInv.tendsto.eventually (hΩ.mem_nhds hy)
    have hD : (chartTarget c ∩ chartInv c ⁻¹' Ω) ×ˢ I ∈ 𝓝[chartTarget c ×ˢ I] p := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hNear,self_mem_nhdsWithin] with q hq hqQ
      exact ⟨⟨hqQ.1,hq⟩,hqQ.2⟩
    exact (hPsi p hp).mul ((hv c p ⟨⟨hp.1,hy⟩,hp.2⟩).mono_of_mem_nhdsWithin hD)
  · have hyS : chartInv c p.1 ∉ tsupport ψ := fun h => hy (hψΩ h)
    have hNear := hInv.tendsto.eventually ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hyS)
    have he : (fun q : Point n => ψ (chartInv c q.1) * v (chartInv c q.1) q.2) =ᶠ[𝓝 p]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hNear] with q hq
      rw [image_eq_zero_of_notMem_tsupport hq,zero_mul]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

end Yau.F04Proof
