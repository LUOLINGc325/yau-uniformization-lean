import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

noncomputable section
open Filter Set
open scoped Topology ContDiff
set_option maxHeartbeats 1600000

namespace Yau.LeafProofs.L17BanachImplicitFunctionAux

variable {E F : Type*}
    [instE : NormedAddCommGroup E] [instER : NormedSpace ℝ E]
    [instF : NormedAddCommGroup F] [instFR : NormedSpace ℝ F]
    [instCompleteE : CompleteSpace E]

/-- A single smooth inverse on a single open target.  The derivative is
invertible at every point of the restricted source, rather than only at the
base point. -/
theorem smooth_inverse_on_open {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f s) {a : E} (ha : a ∈ s)
    (A : E ≃L[ℝ] F) (hA : HasFDerivAt f (A : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F,
      (e : E → F)=f ∧ a ∈ e.source ∧ e.source ⊆ s ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hfa : ContDiffAt ℝ ∞ f a := hf.contDiffAt (hs.mem_nhds ha)
  let e0 : OpenPartialHomeomorph E F := hfa.toOpenPartialHomeomorph f hA hn
  have hInv : ∀ᶠ p in 𝓝 a,
      fderiv ℝ f p ∈ range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F) := by
    apply (hfa.continuousAt_fderiv hn).eventually
    change range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F) ∈ 𝓝 (fderiv ℝ f a)
    rw [hA.fderiv]
    exact A.nhds
  obtain ⟨u,hu,huOpen,hau⟩ := mem_nhds_iff.mp (inter_mem hInv (hs.mem_nhds ha))
  let e : OpenPartialHomeomorph E F := e0.restrOpen u huOpen
  have he : (e : E → F)=f := rfl
  have ha0 : a ∈ e0.source := hfa.mem_toOpenPartialHomeomorph_source hA hn
  refine ⟨e,he,⟨ha0,hau⟩,?_,?_⟩
  · intro p hp
    exact (hu hp.2).2
  · intro y hy
    have hp := e.map_target hy
    obtain ⟨B,hB⟩ := (hu hp.2).1
    have hfAt : ContDiffAt ℝ ∞ f (e.symm y) :=
      hf.contDiffAt (hs.mem_nhds (hu hp.2).2)
    have hfp : HasFDerivAt f (B : E →L[ℝ] F) (e.symm y) := by
      rw [hB]
      exact (hfAt.differentiableAt hn).hasFDerivAt
    have hInvAt : ContDiffAt ℝ ∞ e.symm y :=
      e.contDiffAt_symm (f₀' := B) hy (by simpa only [he] using hfp)
        (by simpa only [he] using hfAt)
    exact hInvAt.contDiffWithinAt

end Yau.LeafProofs.L17BanachImplicitFunctionAux
