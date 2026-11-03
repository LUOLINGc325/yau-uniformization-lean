import Yau.LeafProofs.L16InitialTimeCutoff
import Yau.LeafProofs.L16HolderExtension

/-! One fixed initial cutoff has a common Hölder budget on every later
time slab. The cutoff and its derivative are actually constant after the
fixed cutoff interval, so the native clamping extension is exact. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_initialTimeCutoff_deriv_zero {b t : ℝ} (hb : 0 < b) (ht : b/2 < t) :
    deriv (initialTimeCutoff b) t = 0 := by
  have hGerm : initialTimeCutoff b =ᶠ[𝓝 t] (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact initialTimeCutoff_eq_one hb hr.le
  exact hGerm.deriv_eq.trans (deriv_const t 1)

theorem F05_nonnegative_time_clamp_eq {n : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (f : ℝ → ℝ) (hConst : ∀ t : ℝ, b ≤ t → f t = f b)
    (p : Point n) (hp : 0 ≤ p.2) :
    f (clampPointTime 0 b hb p).2 = f p.2 := by
  change f ((projIcc 0 b hb p.2 : Icc 0 b) : ℝ) = f p.2
  by_cases ht : p.2 ≤ b
  · rw [projIcc_of_mem hb ⟨hp,ht⟩]
  · rw [projIcc_of_right_le hb (not_le.mp ht).le]
    exact (hConst p.2 (not_le.mp ht).le).symm

theorem F05_fixed_time_cutoff_holder {n : ℕ} {α b : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ E : ℝ, 0 < E ∧ ∀ T : ℝ,
      HolderBound α (cylinder (n := n) univ 0 T) (fun p => initialTimeCutoff b p.2) E ∧
      HolderBound α (cylinder (n := n) univ 0 T) (fun p => deriv (initialTimeCutoff b) p.2) E := by
  obtain ⟨C,hC,hNative⟩ := initialTimeCutoff_uniform_holder_jets (n := n) hα hα1
  have hFixed := hNative b hb hb1
  have hConst0 (t : ℝ) (ht : b ≤ t) : initialTimeCutoff b t = initialTimeCutoff b b := by
    rw [initialTimeCutoff_eq_one hb (by linarith),initialTimeCutoff_eq_one hb (by linarith)]
  have hConst1 (t : ℝ) (ht : b ≤ t) :
      deriv (initialTimeCutoff b) t = deriv (initialTimeCutoff b) b := by
    rw [F05_initialTimeCutoff_deriv_zero hb (by linarith),
      F05_initialTimeCutoff_deriv_zero hb (by linarith)]
  have hExtended0 := holderBound_clampPointTime hα.le hb.le univ hFixed.1
  have hExtended1 := holderBound_clampPointTime hα.le hb.le univ hFixed.2
  refine ⟨C/b^2,by positivity,?_⟩
  intro T
  have hSub : cylinder (n := n) univ 0 T ⊆ univ ×ˢ univ := fun p hp => ⟨hp.1,mem_univ _⟩
  refine ⟨?_,?_⟩
  · exact holderBound_congr_on (holderBound_mono hExtended0 hSub)
      (fun p hp => F05_nonnegative_time_clamp_eq hb.le (initialTimeCutoff b) hConst0 p hp.2.1)
  · exact holderBound_congr_on (holderBound_mono hExtended1 hSub)
      (fun p hp => F05_nonnegative_time_clamp_eq hb.le (deriv (initialTimeCutoff b)) hConst1 p hp.2.1)

end Yau.Proofs.F05Aux
