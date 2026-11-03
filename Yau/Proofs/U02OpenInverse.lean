import Yau.Blueprint.Nodes

open scoped Manifold Topology ContDiff
open Set Filter Topology

noncomputable section

namespace Yau.NodeProofs.U02OpenInverseAux

variable {n : ℕ} {M : ComplexManifold n}

/-- An invertible coordinate derivative gives a smooth local right inverse. -/
theorem exists_local_inverse (ψ : M.Carrier → ComplexVector n)
    (hψ : ContMDiff (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ ψ)
    (hD : ∀ x, Function.Bijective
      (fderiv ℂ (fun z => ψ (chartInv x z)) (chartPt x x)))
    (x : M.Carrier) :
    ∃ g : ComplexVector n → M.Carrier,
      ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ g (ψ x) ∧
      g (ψ x) = x ∧ ∀ᶠ y in 𝓝 (ψ x), ψ (g y) = y := by
  let f : ComplexVector n → ComplexVector n := fun z => ψ (chartInv x z)
  let a : ComplexVector n := chartPt x x
  have hf : ContDiffAt ℂ ∞ f a := by
    have ht := contMDiffAt_iff_source.mp (hψ.contMDiffAt (x := x))
    simpa [ComplexModel, chartInv, chartPt, f, a,
      contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt, Function.comp_def] using ht
  let e : ComplexVector n ≃L[ℂ] ComplexVector n :=
    ContinuousLinearEquiv.ofBijective (fderiv ℂ f a)
      (LinearMap.ker_eq_bot.mpr (hD x).1) (LinearMap.range_eq_top.mpr (hD x).2)
  have hder : HasFDerivAt f (e : ComplexVector n →L[ℂ] ComplexVector n) a := by
    simpa only [e, ContinuousLinearEquiv.coe_ofBijective] using
      (hf.differentiableAt (by simp)).hasFDerivAt
  have hfa : f a = ψ x := by
    simp [f, a, chartInv, chartPt]
  let k : ComplexVector n → ComplexVector n := hf.localInverse hder (by simp)
  have hk : ContDiffAt ℂ ∞ k (ψ x) := by
    simpa only [← hfa] using hf.to_localInverse hder (by simp)
  have hka : k (ψ x) = a := by
    simpa only [← hfa] using hf.localInverse_apply_image hder (by simp)
  have hchart : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞
      (chartInv x) a := by
    exact (contMDiffWithinAt_extChartAt_symm_range_self (I := ComplexModel n)
      (n := (∞ : ℕ∞ω)) x).contMDiffAt (by simp [ComplexModel])
  refine ⟨fun y => chartInv x (k y), ?_, ?_, ?_⟩
  · exact (hka ▸ hchart).comp (ψ x) hk.contMDiffAt
  · simp only [hka, a, chartInv, chartPt, extChartAt_to_inv]
  · have ht := (hf.hasStrictFDerivAt' hder (by simp)).eventually_right_inverse
    change ∀ᶠ y in 𝓝 (ψ x), f (k y) = y
    simpa only [hfa, k, ContDiffAt.localInverse] using ht

/-- A map with an invertible coordinate derivative everywhere is open. -/
theorem isOpenMap (ψ : M.Carrier → ComplexVector n)
    (hψ : ContMDiff (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ ψ)
    (hD : ∀ x, Function.Bijective
      (fderiv ℂ (fun z => ψ (chartInv x z)) (chartPt x x))) : IsOpenMap ψ := by
  apply IsOpenMap.of_nhds_le
  intro x
  obtain ⟨g, hg, hgx, hright⟩ := exists_local_inverse ψ hψ hD x
  have hmap : Filter.map (ψ ∘ g) (𝓝 (ψ x)) = 𝓝 (ψ x) := by
    simpa only [Filter.map_id', Function.comp_def] using Filter.map_congr hright
  rw [← hmap, ← Filter.map_map]
  have hcont := hg.continuousAt
  change Filter.map g (𝓝 (ψ x)) ≤ 𝓝 (g (ψ x)) at hcont
  exact Filter.map_mono (by simpa only [hgx] using hcont)

/-- A smooth injective local diffeomorphism is an open embedding. -/
theorem isOpenEmbedding (ψ : M.Carrier → ComplexVector n)
    (hψ : ContMDiff (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ ψ)
    (hInj : Function.Injective ψ)
    (hD : ∀ x, Function.Bijective
      (fderiv ℂ (fun z => ψ (chartInv x z)) (chartPt x x))) :
    IsOpenEmbedding ψ :=
  .of_continuous_injective_isOpenMap hψ.continuous hInj (isOpenMap ψ hψ hD)

/-- The ordinary global inverse is smooth at every point of the image. -/
theorem contMDiffOn_invFun (ψ : M.Carrier → ComplexVector n)
    (hψ : ContMDiff (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ ψ)
    (hInj : Function.Injective ψ)
    (hD : ∀ x, Function.Bijective
      (fderiv ℂ (fun z => ψ (chartInv x z)) (chartPt x x))) :
    ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞
      (Function.invFun ψ) (range ψ) := by
  rintro y ⟨x, rfl⟩
  obtain ⟨g, hg, hgx, hright⟩ := exists_local_inverse ψ hψ hD x
  apply ContMDiffAt.contMDiffWithinAt
  apply hg.congr_of_eventuallyEq
  filter_upwards [hright] with z hz
  calc
    Function.invFun ψ z = Function.invFun ψ (ψ (g z)) := congrArg (Function.invFun ψ) hz.symm
    _ = g z := Function.leftInverse_invFun hInj (g z)

/-- A global inverse, open image, and smoothness on that image, with no extra premise. -/
theorem exists_global_inverse (ψ : M.Carrier → ComplexVector n)
    (hψ : ContMDiff (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ ψ)
    (hInj : Function.Injective ψ)
    (hD : ∀ x, Function.Bijective
      (fderiv ℂ (fun z => ψ (chartInv x z)) (chartPt x x))) :
    ∃ ψinv : ComplexVector n → M.Carrier,
      IsOpen (range ψ) ∧
      ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψinv (range ψ) ∧
      ∀ x, ψinv (ψ x) = x := by
  refine ⟨Function.invFun ψ, ?_, contMDiffOn_invFun ψ hψ hInj hD,
    Function.leftInverse_invFun hInj⟩
  simpa only [image_univ] using (isOpenMap ψ hψ hD) univ isOpen_univ

/-- Compact subsets of the open image have compact inverse images under the inverse. -/
theorem isCompact_invFun_image (ψ : M.Carrier → ComplexVector n)
    (hψ : ContMDiff (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ ψ)
    (hInj : Function.Injective ψ)
    (hD : ∀ x, Function.Bijective
      (fderiv ℂ (fun z => ψ (chartInv x z)) (chartPt x x)))
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKr : K ⊆ range ψ) :
    IsCompact (Function.invFun ψ '' K) :=
  hK.image_of_continuousOn ((contMDiffOn_invFun ψ hψ hInj hD).continuousOn.mono hKr)

end Yau.NodeProofs.U02OpenInverseAux
