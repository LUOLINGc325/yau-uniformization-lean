import Yau.LeafProofs.L22Patching
import Yau.LeafProofs.L18

noncomputable section

open scoped Topology ContDiff Manifold
open Set Filter

namespace Yau.LeafProofs.L22Aux

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*} [DecidableEq ι]

/-- Local smoothness of the branches and the proved fixed finite expression
give genuine global smoothness of the patched function. -/
theorem patchedRegularizedMax_contMDiff
    (χ : ι → M.Carrier → ℝ) (hχ : LocallyFinite (fun i => tsupport (χ i)))
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) (g : ι → M.Carrier → ℝ) (u : M.Carrier → ℝ)
    (W : ι → Set M.Carrier) (hW : ∀ i, IsOpen (W i))
    (hsupp : ∀ i, tsupport (χ i) ⊆ W i)
    (hcover : ∀ x, ∃ j, χ j =ᶠ[𝓝 x] (fun _ => 1))
    (hcore : ∀ i y, y ∈ W i → χ i y = 1 → u y + 6 * δ i < g i y)
    (hzero : ∀ i y, y ∈ W i → χ i y = 0 → g i y < u y - 6 * δ i)
    (hg : ∀ i x, x ∈ W i →
      ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (g i) x) :
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞
      (patchedRegularizedMax χ hχ δ g) := by
  letI := L12Aux.manifold_realSmooth M
  intro x
  let s := activeIndices χ hχ x
  have hgs : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, s → ℝ) ∞
      (fun y (i : s) => g i y) x := by
    apply contMDiffAt_pi_module_iff.mpr
    intro i
    exact hg i x (hsupp i ((mem_activeIndices χ hχ x i).mp i.property))
  have hfinite := (regularizedMaxCoords_smooth (fun i : s => δ i)).comp_contMDiffAt hgs
  apply hfinite.congr_of_eventuallyEq
  exact patchedRegularizedMax_eventuallyEq χ hχ δ hδ g u W hW hsupp hcover hcore hzero x

theorem patchedRegularizedMax_smoothFn
    (χ : ι → M.Carrier → ℝ) (hχ : LocallyFinite (fun i => tsupport (χ i)))
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) (g : ι → M.Carrier → ℝ) (u : M.Carrier → ℝ)
    (W : ι → Set M.Carrier) (hW : ∀ i, IsOpen (W i))
    (hsupp : ∀ i, tsupport (χ i) ⊆ W i)
    (hcover : ∀ x, ∃ j, χ j =ᶠ[𝓝 x] (fun _ => 1))
    (hcore : ∀ i y, y ∈ W i → χ i y = 1 → u y + 6 * δ i < g i y)
    (hzero : ∀ i y, y ∈ W i → χ i y = 0 → g i y < u y - 6 * δ i)
    (hg : ∀ i x, x ∈ W i →
      ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (g i) x) :
    SmoothFn (patchedRegularizedMax χ hχ δ g) :=
  L18Aux.smoothFn_of_contMDiff_real
    (patchedRegularizedMax_contMDiff χ hχ δ hδ g u W hW hsupp hcover hcore hzero hg)

end Yau.LeafProofs.L22Aux
