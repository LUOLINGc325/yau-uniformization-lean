import Yau.Proofs.V02FlowNativeBranches
import Yau.Proofs.V02FlowNativeUniqueness

/-! Explicit total gluing of compatible actual native local flows. -/

open scoped Manifold Topology ContDiff
open Filter Metric Set

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open Yau Yau.Blueprint V03Proof

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*}

def nativeFlowGlue (U : ι → Set (NativeCotangentPoint M))
    (F : ι → ℂ × NativeCotangentPoint M → NativeCotangentPoint M) (R : ℝ)
    (p : ℂ × NativeCotangentPoint M) : NativeCotangentPoint M := by
  classical
  exact if h : p.1 ∈ ball (0 : ℂ) R ∧ p.2 ∈ ⋃ i, U i then
    F (Classical.choose (mem_iUnion.mp h.2)) p else p.2

theorem nativeFlowGlue_eq_branch
    {U : ι → Set (NativeCotangentPoint M)}
    {F : ι → ℂ × NativeCotangentPoint M → NativeCotangentPoint M} {R : ℝ}
    (hcompat : ∀ i j t, t ∈ ball (0 : ℂ) R → ∀ y, y ∈ U i → y ∈ U j →
      F i (t, y) = F j (t, y))
    (i : ι) {t : ℂ} (ht : t ∈ ball (0 : ℂ) R)
    {y : NativeCotangentPoint M} (hy : y ∈ U i) :
    nativeFlowGlue U F R (t, y) = F i (t, y) := by
  classical
  have h : t ∈ ball (0 : ℂ) R ∧ y ∈ ⋃ j, U j := ⟨ht, mem_iUnion.mpr ⟨i, hy⟩⟩
  simp only [nativeFlowGlue, dite_eq_left h]
  exact hcompat _ i t ht y (Classical.choose_spec (mem_iUnion.mp h.2)) hy

theorem nativeFlowGlue_zero
    {U : ι → Set (NativeCotangentPoint M)}
    {F : ι → ℂ × NativeCotangentPoint M → NativeCotangentPoint M} {R : ℝ}
    (hzero : ∀ i y, y ∈ U i → F i (0, y) = y) (y : NativeCotangentPoint M) :
    nativeFlowGlue U F R (0, y) = y := by
  classical
  unfold nativeFlowGlue
  split_ifs with h
  · exact hzero _ y (Classical.choose_spec (mem_iUnion.mp h.2))
  · rfl

theorem nativeFlowGlue_contMDiffOn
    {U : ι → Set (NativeCotangentPoint M)}
    {F : ι → ℂ × NativeCotangentPoint M → NativeCotangentPoint M} {R : ℝ}
    (hU : ∀ i, IsOpen (U i))
    (hF : ∀ i, ContMDiffOn ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, CotangentCoord n))
      𝓘(ℂ, CotangentCoord n) ∞ (F i) (ball (0 : ℂ) R ×ˢ U i))
    (hcompat : ∀ i j t, t ∈ ball (0 : ℂ) R → ∀ y, y ∈ U i → y ∈ U j →
      F i (t, y) = F j (t, y)) :
    ContMDiffOn ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, CotangentCoord n)) 𝓘(ℂ, CotangentCoord n) ∞
      (nativeFlowGlue U F R) (ball (0 : ℂ) R ×ˢ ⋃ i, U i) := by
  intro p hp
  obtain ⟨i, hy⟩ := mem_iUnion.mp hp.2
  have hpatch : IsOpen (ball (0 : ℂ) R ×ˢ U i) := isOpen_ball.prod (hU i)
  have hlocal := (hF i p ⟨hp.1, hy⟩).contMDiffAt (hpatch.mem_nhds ⟨hp.1, hy⟩)
  apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hpatch.mem_nhds ⟨hp.1, hy⟩] with q hq
  exact nativeFlowGlue_eq_branch hcompat i hq.1 hq.2

end Yau.Blueprint.V02FlowProof
