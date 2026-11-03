import Yau.LeafProofs.L17LocalizedSchauderTimeTransport
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux

theorem contDiffOn_two_of_true_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) (v : E → F)
    (D : E → E →L[ℝ] F) (H : E → E →L[ℝ] E →L[ℝ] F)
    (hv : ∀ z ∈ U, HasFDerivAt v (D z) z)
    (hD : ∀ z ∈ U, HasFDerivAt D (H z) z) (hH : ContinuousOn H U) :
    ContDiffOn ℝ 2 v U := by
  have hD1 : ContDiffOn ℝ 1 D U := by
    change ContDiffOn ℝ ((0 : ℕ∞ω)+1) D U
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
    refine ⟨by simp,H,?_,fun z hz => (hD z hz).hasFDerivWithinAt⟩
    exact contDiffOn_zero.mpr hH
  change ContDiffOn ℝ ((1 : ℕ∞ω)+1) v U
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
  exact ⟨by simp,D,hD1,fun z hz => (hv z hz).hasFDerivWithinAt⟩

end Yau.LeafProofs.L17LocalizedSchauderAux
