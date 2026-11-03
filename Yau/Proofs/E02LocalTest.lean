import Yau.Blueprint.Nodes

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.NodeProofs.E02Aux

/-- Only one finite-order neighbourhood is extracted from the original
smooth germ. This does not assert a common C-infinity neighbourhood. -/
theorem smooth_germ_open_C2
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) :
    ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ ContDiffOn ℝ 2 f O := by
  obtain ⟨s,hs,hf2⟩ := hf.contDiffOn (m := 2) (by simp) (by simp)
  exact ⟨interior s,isOpen_interior,mem_interior_iff_mem_nhds.mpr hs,hf2.mono interior_subset⟩

end Yau.NodeProofs.E02Aux
