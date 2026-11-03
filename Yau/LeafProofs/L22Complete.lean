import Yau.LeafProofs.L22Branches
import Yau.LeafProofs.L22LeviAggregate
import Yau.LeafProofs.L22Locality

noncomputable section

open scoped Topology ContDiff Manifold Matrix ComplexOrder
open Set Filter

namespace Yau.LeafProofs.L22Aux

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*} [DecidableEq ι]

theorem patchedRegularizedMax_levi_posDef
    (χ : ι → M.Carrier → ℝ) (hχ : LocallyFinite (fun i => tsupport (χ i)))
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) (g : ι → M.Carrier → ℝ) (u : M.Carrier → ℝ)
    (W : ι → Set M.Carrier) (hW : ∀ i, IsOpen (W i))
    (hsupp : ∀ i, tsupport (χ i) ⊆ W i)
    (hcover : ∀ x, ∃ j, χ j =ᶠ[𝓝 x] (fun _ => 1))
    (hcore : ∀ i y, y ∈ W i → χ i y = 1 → u y + 6 * δ i < g i y)
    (hzero : ∀ i y, y ∈ W i → χ i y = 0 → g i y < u y - 6 * δ i)
    (hg : ∀ i x, x ∈ W i →
      ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (g i) x)
    (hpos : ∀ i x, x ∈ W i → (levi (g i) x).PosDef)
    (x : M.Carrier) : (levi (patchedRegularizedMax χ hχ δ g) x).PosDef := by
  letI := L12Aux.manifold_realSmooth M
  let s := activeIndices χ hχ x
  letI : Nonempty s := (activeIndices_nonempty χ hχ hcover x).to_subtype
  have hchart (i : s) : ContDiffAt ℝ ∞ (inChart x (g i)) (chartPt x x) := by
    have hgi := hg i x (hsupp i ((mem_activeIndices χ hχ x i).mp i.property))
    rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ,
      contMDiffWithinAt_univ] at hgi
    simpa only [inChart, chartInv, chartPt, L12Aux.real_extChartAt_eq] using! hgi.contDiffAt
  have hfinite : (levi
      (fun y => regularizedMax (activeIndices χ hχ x) δ (fun i => g i y)) x).PosDef := by
    change (leviC
      (fun z => regularizedMaxCoords (fun i : s => δ i) (fun i : s => inChart x (g i) z))
      (chartPt x x)).PosDef
    apply leviC_posDef_regularizedMaxCoords
      (fun i : s => δ i) (fun i => (hchart i).of_le (by simp))
    intro i
    exact hpos i x (hsupp i ((mem_activeIndices χ hχ x i).mp i.property))
  rw [levi_congr_of_eventuallyEq
    (patchedRegularizedMax_eventuallyEq χ hχ δ hδ g u W hW hsupp hcover hcore hzero x)]
  exact hfinite

end Yau.LeafProofs.L22Aux

namespace Yau.LeafProofs

/-- The complete frozen classical Richberg approximation leaf. All local
convolutions, strict branches, finite regularized maxima and their gluing
are constructed internally from the original premises. -/
theorem L22 : LeafObligations.L22 := by
  intro n M u ε hu hε hεpos
  obtain ⟨ι, χ, δ, g, W, hχ, hδ, hW, hsupp, hcover, hgs, hgpos, hcore, hzero, hupper⟩ :=
    L22Aux.exists_strict_branch_cover u ε hu hε hεpos
  classical
  let ψ := L22Aux.patchedRegularizedMax χ hχ δ g
  have hψs : SmoothFn ψ :=
    L22Aux.patchedRegularizedMax_smoothFn χ hχ δ hδ g u W hW hsupp hcover hcore hzero hgs
  have hψpos : ∀ x, (levi ψ x).PosDef :=
    L22Aux.patchedRegularizedMax_levi_posDef χ hχ δ hδ g u W hW hsupp hcover hcore hzero hgs hgpos
  refine ⟨ψ, hψs, L22Aux.classicalStrictPsh_of_smooth_positive hψs
    (L18Aux.continuous_of_smoothFn hψs) hψpos, ?_⟩
  intro x
  have hb := L22Aux.patchedRegularizedMax_error χ hχ δ hδ g u ε W hsupp hcover hcore hupper x
  rw [abs_of_pos (sub_pos.mpr hb.1)]
  linarith [hb.2]

end Yau.LeafProofs
