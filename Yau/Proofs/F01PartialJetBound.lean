import spec.CHAIN.CONTRACTS

/-! Actual derivatives in the variable coordinate are restrictions of the
joint derivatives along an affine isometric slice. Compact joint budgets
therefore bound every order of the chart-coordinate derivatives. -/
open Set
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def fixedFirstInclusion (a : A) : E →ᴬ[ℝ] A × E :=
  (ContinuousAffineMap.const ℝ E a).prod (ContinuousAffineMap.id ℝ E)

theorem fixedFirstInclusion_apply (a : A) (z : E) :
    fixedFirstInclusion a z = (a, z) := rfl

theorem fixedFirstInclusion_contLinear (a : A) :
    (fixedFirstInclusion (E := E) a).contLinear = ContinuousLinearMap.inr ℝ A E := by
  ext z <;> rfl

theorem iteratedFDeriv_fixedFirst {W : Set (A × E)} (hW : IsOpen W)
    {f : A × E → F} (hf : ContDiffOn ℝ ∞ f W) (a : A) {z : E}
    (hz : (a, z) ∈ W) (k : ℕ) :
    iteratedFDeriv ℝ k (fun w => f (a, w)) z =
      (iteratedFDeriv ℝ k f (a, z)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ A E) := by
  let V := (fixedFirstInclusion (E := E) a) ⁻¹' W
  have hV : IsOpen V := hW.preimage (fixedFirstInclusion a).continuous
  have ht := (hf.ftaylorSeriesWithin hW.uniqueDiffOn).comp_continuousAffineMap
    (fixedFirstInclusion (E := E) a)
  have heq := ht.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k) hV.uniqueDiffOn hz
  simp only [Function.comp_def, fixedFirstInclusion_apply,
    fixedFirstInclusion_contLinear, ftaylorSeriesWithin] at heq
  rw [iteratedFDerivWithin_of_isOpen k hW hz,
    iteratedFDerivWithin_of_isOpen k hV hz] at heq
  exact heq.symm

theorem norm_iteratedFDeriv_fixedFirst_le {W : Set (A × E)} (hW : IsOpen W)
    {f : A × E → F} (hf : ContDiffOn ℝ ∞ f W) (a : A) {z : E}
    (hz : (a, z) ∈ W) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w => f (a, w)) z‖ ≤ ‖iteratedFDeriv ℝ k f (a, z)‖ := by
  rw [iteratedFDeriv_fixedFirst hW hf a hz k]
  have h := (iteratedFDeriv ℝ k f (a, z)).norm_compContinuousLinearMap_le
    (fun _ : Fin k => ContinuousLinearMap.inr ℝ A E)
  apply h.trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ A E)

end Yau.NodeProofs.F01Aux
