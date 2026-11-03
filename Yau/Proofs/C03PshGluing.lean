import Yau.Proofs.C03TwoMaximum
import Yau.Proofs.C03LeviGerms

/-! A smooth maximum on the source ball glues to a global barrier.
Separation on the boundary proves actual smoothness across that boundary. -/

noncomputable section
open Filter
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs.L22Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def gluedMaximum (R δ : ℝ) (f b : ComplexVector n → ℝ) (z : ComplexVector n) : ℝ :=
  if ‖z‖ < R then twoMaximum δ f b z else b z

theorem gluedMaximum_eq_maximum_germ (R δ : ℝ) (f b : ComplexVector n → ℝ)
    (z : ComplexVector n) (hz : ‖z‖ < R) :
    gluedMaximum R δ f b =ᶠ[𝓝 z] twoMaximum δ f b := by
  filter_upwards [continuous_norm.continuousAt.eventually_lt_const hz] with w hw
  exact if_pos hw

theorem gluedMaximum_eq_barrier_germ (R δ : ℝ) (hδ : 0 < δ)
    (f b : ComplexVector n → ℝ) (hf : Continuous f) (hb : Continuous b)
    (hboundary : ∀ z, ‖z‖ = R → f z + 4 * δ ≤ b z)
    (z : ComplexVector n) (hz : ¬‖z‖ < R) :
    gluedMaximum R δ f b =ᶠ[𝓝 z] b := by
  by_cases hout : R < ‖z‖
  · filter_upwards [continuous_norm.continuousAt.eventually_const_lt hout] with w hw
    exact if_neg (not_lt.mpr hw.le)
  · have hnorm : ‖z‖ = R := le_antisymm (le_of_not_gt hout) (le_of_not_gt hz)
    have hgap : 2 * δ < b z - f z := by linarith [hboundary z hnorm]
    have hnear := (hb.continuousAt.sub hf.continuousAt).eventually_const_lt hgap
    filter_upwards [hnear] with w hw
    change 2 * δ < b w - f w at hw
    by_cases hwin : ‖w‖ < R
    · rw [gluedMaximum, if_pos hwin]
      exact twoMaximum_eq_right δ hδ f b w (by linarith)
    · exact if_neg hwin

theorem gluedMaximum_contDiff (R δ : ℝ) (hδ : 0 < δ)
    (f b : ComplexVector n → ℝ) (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (hboundary : ∀ z, ‖z‖ = R → f z + 4 * δ ≤ b z) :
    ContDiff ℝ ∞ (gluedMaximum R δ f b) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : ‖z‖ < R
  · exact (twoMaximum_contDiff δ f b hf hb).contDiffAt.congr_of_eventuallyEq
      (gluedMaximum_eq_maximum_germ R δ f b z hz)
  · exact hb.contDiffAt.congr_of_eventuallyEq
      (gluedMaximum_eq_barrier_germ R δ hδ f b hf.continuous hb.continuous hboundary z hz)

theorem gluedMaximum_leviC_posSemidef (R δ : ℝ) (hδ : 0 < δ)
    (f b : ComplexVector n → ℝ) (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (hboundary : ∀ z, ‖z‖ = R → f z + 4 * δ ≤ b z)
    (hfp : ∀ z, ‖z‖ < R → (leviC f z).PosSemidef)
    (hbp : ∀ z, (leviC b z).PosSemidef) (z : ComplexVector n) :
    (leviC (gluedMaximum R δ f b) z).PosSemidef := by
  by_cases hz : ‖z‖ < R
  · rw [leviC_congr_germ (gluedMaximum_eq_maximum_germ R δ f b z hz)]
    exact twoMaximum_leviC_posSemidef δ f b z
      (hf.contDiffAt.of_le (by simp)) (hb.contDiffAt.of_le (by simp)) (hfp z hz) (hbp z)
  · rw [leviC_congr_germ
      (gluedMaximum_eq_barrier_germ R δ hδ f b hf.continuous hb.continuous hboundary z hz)]
    exact hbp z

theorem gluedMaximum_eq_original_germ (R δ : ℝ) (hδ : 0 < δ)
    (f b : ComplexVector n → ℝ) (hf : Continuous f) (hb : Continuous b)
    (z : ComplexVector n) (hz : ‖z‖ < R) (hgap : b z + 4 * δ ≤ f z) :
    gluedMaximum R δ f b =ᶠ[𝓝 z] f := by
  have hstrict : 2 * δ < f z - b z := by linarith
  have hnear := (hf.continuousAt.sub hb.continuousAt).eventually_const_lt hstrict
  filter_upwards [hnear, continuous_norm.continuousAt.eventually_lt_const hz] with w hw hwin
  change 2 * δ < f w - b w at hw
  rw [gluedMaximum, if_pos hwin]
  exact twoMaximum_eq_left δ hδ f b w (by linarith)

end Yau.Proofs.C03Aux
