import Yau.Proofs.F05BootstrapLocalBounds
import Yau.Proofs.F05BootstrapGoodAlgebra

/-! Equality on the original positive physical patch preserves actual
computed good derivatives and good differentiability. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_good_line_mem_posPatch {ν : Option (RIdx n)} {k : RIdx n} {T : ℝ}
    (hd : F05GoodLetter ν (some k)) {z : Point n} (hz : z ∈ F05PosPatch ν T) :
    ∀ᶠ a : ℝ in 𝓝 0, (z.1+a • realVec k,z.2) ∈ F05PosPatch ν T := by
  have hn : ‖z.1‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hz.1.2
  let R := (‖z.1‖+2)/2
  have hR2 : R < 2 := by dsimp only [R]; linarith
  have hxR : ‖z.1‖ < R := by dsimp only [R]; linarith
  have hLine := F05_good_line_mem_region hd (F05_posSpace_mem_region hz.1 hxR.le) hxR
  filter_upwards [hLine] with a ha
  exact ⟨F05_region_subset_posSpace ν hR2 ha,hz.2⟩

theorem F05_good_partial_congr {ν d : Option (RIdx n)} {T : ℝ}
    (hd : F05GoodLetter ν d) {f g : Point n → V} (hEq : EqOn f g (F05PosPatch ν T)) :
    EqOn (F05GoodPartial T d f) (F05GoodPartial T d g) (F05PosPatch ν T) := by
  intro z hz
  cases d with
  | none =>
    exact derivWithin_congr (fun t ht => hEq ⟨hz.1,ht⟩) (hEq hz)
  | some k =>
    have hLine : (fun a : ℝ => f (z.1+a • realVec k,z.2)) =ᶠ[𝓝 0]
        (fun a => g (z.1+a • realVec k,z.2)) := by
      filter_upwards [F05_good_line_mem_posPatch hd hz] with a ha
      exact hEq ha
    exact hLine.deriv_eq

theorem F05_good_diff_congr {ν d : Option (RIdx n)} {T : ℝ}
    (hd : F05GoodLetter ν d) {f g : Point n → V} (hEq : EqOn f g (F05PosPatch ν T))
    (hg : F05GoodDiffOn T d g (F05PosPatch ν T)) : F05GoodDiffOn T d f (F05PosPatch ν T) := by
  intro z hz
  cases d with
  | none => exact (hg z hz).congr (fun t ht => hEq ⟨hz.1,ht⟩) (hEq hz)
  | some k =>
    have hLine : (fun a : ℝ => f (z.1+a • realVec k,z.2)) =ᶠ[𝓝 0]
        (fun a => g (z.1+a • realVec k,z.2)) := by
      filter_upwards [F05_good_line_mem_posPatch hd hz] with a ha
      exact hEq ha
    exact hLine.differentiableAt_iff.mpr (hg z hz)

end Yau.Proofs.F05Aux
