import Yau.Proofs.D02LocalMorrey
import Yau.Proofs.D02ConnectedRange

/-! Actual local Hölder estimates give equicontinuity on the regular
domain with its inherited topology and the original induced target metric. -/

open scoped Topology
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux

theorem equicontinuous_restrict_of_local_holder {Y : Type*} [PseudoMetricSpace Y]
    {O : Set ℂ} (fs : ℕ → ℂ → Y)
    (hHolder : ∀ x ∈ O, ∃ r H : ℝ, 0 < r ∧ 0 ≤ H ∧
      ∀ j z, z ∈ ball x r → ∀ w, w ∈ ball x r →
        dist (fs j z) (fs j w) ≤ H * ‖z - w‖ ^ (1 / 3 : ℝ)) :
    Equicontinuous (fun j (x : O) => fs j x) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨r, H, hr, _, hh⟩ := hHolder x x.2
  have hc : Continuous (fun z : ℂ => H * ‖z - (x : ℂ)‖ ^ (1 / 3 : ℝ)) := by
    apply continuous_const.mul
    exact (continuous_id.sub continuous_const).norm.rpow_const (fun _ => Or.inr (by norm_num))
  have ht : Tendsto (fun z : O => H * ‖(z : ℂ) - (x : ℂ)‖ ^ (1 / 3 : ℝ)) (𝓝 x) (𝓝 0) := by
    simpa [Function.comp_def] using (hc.comp continuous_subtype_val).continuousAt.tendsto (x := x)
  have hb : ∀ᶠ z : O in 𝓝 x, (z : ℂ) ∈ ball (x : ℂ) r :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
  filter_upwards [hb, ht.eventually (Iio_mem_nhds hε)] with z hz hsmall j
  exact ((hh j x (mem_ball_self hr) z hz).trans_eq (by rw [norm_sub_rev])).trans_lt hsmall

theorem bounded_point_range_of_eventually (a : ℕ → ℝ) (B : ℝ)
    (ha : ∀ᶠ j in atTop, a j ≤ B) : ∃ C : ℝ, ∀ j, a j ≤ C := by
  classical
  obtain ⟨J, hJ⟩ := ha.exists_forall_of_atTop
  let C : ℝ := max 0 B + ∑ i ∈ Finset.range J, max 0 (a i)
  refine ⟨C, fun j => ?_⟩
  have hsum : 0 ≤ ∑ i ∈ Finset.range J, max 0 (a i) :=
    Finset.sum_nonneg (fun i _ => le_max_left 0 (a i))
  by_cases hj : j < J
  · have hs : max 0 (a j) ≤ ∑ i ∈ Finset.range J, max 0 (a i) :=
      Finset.single_le_sum (fun i _ => le_max_left 0 (a i)) (Finset.mem_range.mpr hj)
    dsimp [C]
    linarith [le_max_right 0 (a j), le_max_left 0 B]
  · dsimp [C]
    linarith [hJ j (Nat.le_of_not_gt hj), le_max_right 0 B]

theorem moving_anchor_bounded_subsequence {D Y : Type*} [MetricSpace D] [MetricSpace Y]
    (fs : ℕ → D → Y) (zs : ℕ → D) {H : Set D} {K : Set Y}
    (hH : IsCompact H) (hzs : ∀ j, zs j ∈ H) (hK : IsCompact K)
    (hmap : ∀ j, fs j (zs j) ∈ K) (heq : ∀ x ∈ H, EquicontinuousAt fs x) (o : Y) :
    ∃ β : ℕ → ℕ, StrictMono β ∧ ∃ x ∈ H, ∃ B : ℝ, ∀ j, dist (fs (β j) x) o ≤ B := by
  obtain ⟨x, hx, β, hβ, ht⟩ := hH.tendsto_subseq hzs
  obtain ⟨R, hR⟩ := hK.bddAbove_image (continuous_id.dist continuous_const).continuousOn
  have hn := (Metric.equicontinuousAt_iff_right.mp (heq x hx)) 1 one_pos
  have hlate : ∀ᶠ j in atTop, dist (fs (β j) x) o ≤ 1 + R := by
    filter_upwards [ht.eventually hn] with j hj
    exact (dist_triangle (fs (β j) x) (fs (β j) (zs (β j))) o).trans
      (add_le_add (hj (β j)).le (hR (mem_image_of_mem (fun y => dist y o) (hmap (β j)))))
  obtain ⟨B, hB⟩ := bounded_point_range_of_eventually (fun j => dist (fs (β j) x) o) (1 + R) hlate
  exact ⟨β, hβ, x, hx, B, hB⟩

end Yau.NodeProofs.D02Aux
