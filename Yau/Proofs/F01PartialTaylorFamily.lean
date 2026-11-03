import spec.CHAIN.CONTRACTS

/-! Parameter Taylor jets are restrictions of the actual joint Taylor jets
along the fixed affine slice x ↦ (x,t). No regularity of those partial jets is
postulated independently of the original smooth joint map. -/
open Set
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def parameterInclusion (t : ℝ) : E →ᴬ[ℝ] E × ℝ :=
  (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E t)

theorem parameterInclusion_apply (t : ℝ) (x : E) : parameterInclusion t x = (x, t) := rfl

theorem parameterInclusion_contLinear (t : ℝ) :
    (parameterInclusion (E := E) t).contLinear = ContinuousLinearMap.inl ℝ E ℝ := by
  ext x <;> rfl

def partialTaylorFamily (f : E × ℝ → F) (W : Set (E × ℝ))
    (x : E) (t : ℝ) : FormalMultilinearSeries ℝ E F :=
  fun m => (iteratedFDerivWithin ℝ m f W (x, t)).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.inl ℝ E ℝ)

theorem partialTaylorFamily_isTaylor {W : Set (E × ℝ)} (hW : IsOpen W)
    {U : Set E} {f : E × ℝ → F} (hf : ContDiffOn ℝ ∞ f W)
    (hUW : U ×ˢ Icc (0 : ℝ) 1 ⊆ W) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasFTaylorSeriesUpToOn ∞ (fun x => f (x, t)) (fun x => partialTaylorFamily f W x t) U := by
  have h := ((hf.ftaylorSeriesWithin hW.uniqueDiffOn).comp_continuousAffineMap
    (parameterInclusion (E := E) t)).mono (fun x hx => hUW ⟨hx, ht⟩)
  unfold partialTaylorFamily
  simpa only [Function.comp_def, parameterInclusion_apply, parameterInclusion_contLinear,
    ftaylorSeriesWithin] using h

theorem partialTaylorFamily_continuous {W : Set (E × ℝ)} (hW : IsOpen W)
    {U : Set E} {f : E × ℝ → F} (hf : ContDiffOn ℝ ∞ f W)
    (hUW : U ×ˢ Icc (0 : ℝ) 1 ⊆ W) (m : ℕ) :
    ContinuousOn (fun w : E × ℝ => partialTaylorFamily f W w.1 w.2 m) (U ×ˢ Icc 0 1) := by
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (F := F) (fun _ : Fin m => ContinuousLinearMap.inl ℝ E ℝ)).continuous.comp_continuousOn
    ((hf.continuousOn_iteratedFDerivWithin
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) hW.uniqueDiffOn).mono hUW)

end Yau.NodeProofs.F01Aux
