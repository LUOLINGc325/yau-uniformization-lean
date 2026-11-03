import Yau.Proofs.F04ZeroPastLp

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic

theorem zeroPast_continuousOn_of_linear_growth {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) {s K : ℝ} (hK : 0 ≤ K) {u : Point n → ℝ}
    (hu : ContinuousOn u (O ×ˢ Ioo 0 s))
    (hGrowth : ∀ p ∈ O ×ˢ Ioo 0 s, |u p| ≤ K * p.2) :
    ContinuousOn (zeroPast u) (O ×ˢ Ioo (-s) s) := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  by_cases hpos : 0 < p.2
  · have he : zeroPast u =ᶠ[𝓝 p] u := by
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hpos] with q hq
      exact zeroPast_of_pos u hq
    have hc : ContinuousAt u p := hu.continuousAt
      ((hO.prod isOpen_Ioo).mem_nhds ⟨hp.1, hpos, hp.2.2⟩)
    change Tendsto (zeroPast u) (𝓝 p) (𝓝 (zeroPast u p))
    rw [zeroPast_of_pos u hpos]
    exact hc.congr' he.symm
  · by_cases hneg : p.2 < 0
    · have he : zeroPast u =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
        filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hneg] with q hq
        exact zeroPast_of_nonpos u hq.le
      change Tendsto (zeroPast u) (𝓝 p) (𝓝 (zeroPast u p))
      rw [zeroPast_of_nonpos u hneg.le]
      exact tendsto_const_nhds.congr' he.symm
    · have hzero : p.2 = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      have hb : ∀ᶠ q : Point n in 𝓝 p, ‖zeroPast u q‖ ≤ K * |q.2| := by
        filter_upwards [(hO.prod isOpen_Ioo).mem_nhds hp] with q hq
        by_cases hqpos : 0 < q.2
        · rw [zeroPast_of_pos u hqpos, Real.norm_eq_abs, abs_of_pos hqpos]
          exact hGrowth q ⟨hq.1, hqpos, hq.2.2⟩
        · rw [zeroPast_of_nonpos u (le_of_not_gt hqpos), norm_zero]
          exact mul_nonneg hK (abs_nonneg _)
      have hlim : Tendsto (fun q : Point n => K * |q.2|) (𝓝 p) (𝓝 0) := by
        simpa only [hzero, abs_zero, mul_zero] using
          ((continuous_snd.abs).tendsto p).const_mul K
      change Tendsto (zeroPast u) (𝓝 p) (𝓝 (zeroPast u p))
      rw [zeroPast_of_nonpos u hzero.le]
      exact tendsto_zero_iff_norm_tendsto_zero.mpr
        (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hb hlim)

end Yau.F04Proof
