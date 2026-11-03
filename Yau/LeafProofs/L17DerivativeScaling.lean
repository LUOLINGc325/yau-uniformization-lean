import Yau.LeafProofs.L17ScaledBumps

/-! Local derivative scaling, without extending a local chart map globally. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L17Aux

theorem norm_iteratedFDeriv_comp_smul_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (a : ℝ) {x : E} (hx : a • x ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z => f (a • z)) x‖ ≤
      ‖iteratedFDeriv ℝ k f (a • x)‖ * ‖a‖ ^ k := by
  let L : E →L[ℝ] E := a • ContinuousLinearMap.id ℝ E
  have hL : ‖L‖ ≤ ‖a‖ := by
    rw [show L = a • ContinuousLinearMap.id ℝ E from rfl, norm_smul]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg a)).trans_eq
      (mul_one _)
  have hW : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hxL : L x ∈ U := hx
  have hder := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hW.uniqueDiffOn hxL
    (by simp : (k : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_of_isOpen k hW hxL,
    iteratedFDerivWithin_of_isOpen k hU hxL] at hder
  change ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ * ‖a‖ ^ k
  rw [hder]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ * ‖L‖ ^ k := by
      simpa using (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
    _ ≤ _ := by gcongr

end Yau.LeafProofs.L17Aux
