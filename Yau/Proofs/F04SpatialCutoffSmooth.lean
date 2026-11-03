import Yau.LeafProofs.L18

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof

/-- Spatial compact support permits actual smooth multiplication on a
 CLOSED time slab. Inside the support the open spatial set is a genuine
 relative neighborhood; outside it the product has the actual zero germ.
 The original coefficient is never required to be smooth off its chart. -/
theorem spatialCutoff_smul_contDiffOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set E} (hO : IsOpen O) {I : Set ℝ}
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχO : tsupport χ ⊆ O)
    {A : E × ℝ → F} (hA : ContDiffOn ℝ ∞ A (O ×ˢ I)) :
    ContDiffOn ℝ ∞ (fun p => χ p.1 • A p) (univ ×ˢ I) := by
  have hχJ : ContDiff ℝ ∞ (fun p : E × ℝ => χ p.1) := hχ.comp contDiff_fst
  intro p hp
  by_cases hsupp : p.1 ∈ tsupport χ
  · have hN : O ×ˢ I ∈ 𝓝[univ ×ˢ I] p := by
      have hNO : ∀ᶠ q : E × ℝ in 𝓝 p, q.1 ∈ O :=
        continuousAt_fst.eventually (hO.mem_nhds (hχO hsupp))
      filter_upwards [hNO.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hqi
      exact ⟨hq, hqi.2⟩
    exact hχJ.contDiffAt.contDiffWithinAt.smul
      ((hA p ⟨hχO hsupp, hp.2⟩).mono_of_mem_nhdsWithin hN)
  · have he : (fun q : E × ℝ => χ q.1 • A q) =ᶠ[𝓝 p] (fun _ => (0 : F)) := by
      have hZ := notMem_tsupport_iff_eventuallyEq.mp hsupp
      filter_upwards [continuousAt_fst.eventually hZ] with q hq
      change χ q.1 = 0 at hq
      rw [hq, zero_smul]
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

end Yau.F04Proof
