import Yau.Proofs.F04SeeleySmooth
import Yau.Proofs.F04AuxiliaryEllipticity

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A single time radius controls a continuous coefficient on a compact spatial buffer. -/
theorem compact_time_norm_control {K W : Set E} {S η : ℝ} (hK : IsCompact K)
    (hKW : K ⊆ W) (hS : 0 < S) (hη : 0 < η) {f : E × ℝ → F}
    (hf : ContinuousOn f (W ×ˢ Iio S)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ t ∈ Ioo (-ε) 0, ‖f (x, t) - f (x, 0)‖ ≤ η := by
  have hC := hK.prod (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 0))
  have hfc : ContinuousOn f (K ×ˢ Icc (-1 : ℝ) 0) :=
    hf.mono (fun p hp => ⟨hKW hp.1, (show p.2 ≤ 0 from hp.2.2).trans_lt hS⟩)
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.mp
    (hC.uniformContinuousOn_of_continuous hfc) η hη
  refine ⟨min 1 d, lt_min (by norm_num) hd, ?_⟩
  intro x hx t ht
  have ht1 : -1 ≤ t := by have := min_le_left (1 : ℝ) d; linarith [ht.1]
  have htd : |t| < d := by
    rw [abs_of_neg ht.2]
    have := min_le_right (1 : ℝ) d
    linarith [ht.1]
  have hp : (x, t) ∈ K ×ˢ Icc (-1 : ℝ) 0 := ⟨hx, ht1, ht.2.le⟩
  have hq : (x, (0 : ℝ)) ∈ K ×ˢ Icc (-1 : ℝ) 0 := ⟨hx, by norm_num, le_rfl⟩
  have hpq : dist (x, t) (x, (0 : ℝ)) < d := by
    simpa only [Prod.dist_eq, dist_self, dist_zero_right, Real.norm_eq_abs,
      max_eq_right (abs_nonneg t)] using htd
  simpa only [dist_eq_norm] using (hdist (x, t) hp (x, 0) hq hpq).le

theorem auxiliary_time_cutoff {S : ℝ} (hS : 0 < S) :
    ∃ δ : ℝ, 0 < δ ∧ δ < S ∧ ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ s : ℝ, δ ≤ s → χ s = 0) ∧
        ∀ s : ℝ, |s| ≤ δ / 2 → χ s = 1 := by
  let δ := S / 2
  have hδ : 0 < δ := half_pos hS
  let χ : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  refine ⟨δ, hδ, half_lt_self hS, χ, χ.contDiff, ?_, ?_⟩
  · intro s hs
    apply χ.zero_of_le_dist
    change δ ≤ dist s 0
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (hδ.le.trans hs)] using hs
  · intro s hs
    apply χ.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hs

end Yau.F04Proof
