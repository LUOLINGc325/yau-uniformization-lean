import Mathlib

/-! The moving-ball maximum is an actual attained supremum. Its upper
continuity uses a compact set of possible maximizing endpoints. -/

noncomputable section
open Set Metric
open scoped Topology

namespace Yau.Proofs.C03Aux

variable {E : Type*} [MetricSpace E] [ProperSpace E]

def metricBallMaximum (ψ : E → ℝ) (ρ : ℝ) (z : E) : ℝ :=
  sSup (ψ '' closedBall z ρ)

theorem metricBallMaximum_spec (ψ : E → ℝ) (hψ : Continuous ψ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (z : E) :
    ∃ y ∈ closedBall z ρ, ψ y = metricBallMaximum ψ ρ z ∧
      ∀ w ∈ closedBall z ρ, ψ w ≤ metricBallMaximum ψ ρ z := by
  obtain ⟨y, hy, hmax⟩ := (isCompact_closedBall z ρ).exists_isMaxOn
    ⟨z, by simpa only [mem_closedBall, dist_self] using hρ⟩ hψ.continuousOn
  have hg : IsGreatest (ψ '' closedBall z ρ) (ψ y) := by
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmax hw
  have heq : ψ y = metricBallMaximum ψ ρ z := hg.csSup_eq.symm
  refine ⟨y, hy, heq, ?_⟩
  intro w hw
  rw [← heq]
  exact hmax hw

theorem le_metricBallMaximum (ψ : E → ℝ) (hψ : Continuous ψ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (z y : E) (hy : y ∈ closedBall z ρ) :
    ψ y ≤ metricBallMaximum ψ ρ z := by
  obtain ⟨_, _, _, H⟩ := metricBallMaximum_spec ψ hψ ρ hρ z
  exact H y hy

theorem metricBallMaximum_le (ψ : E → ℝ) (hψ : Continuous ψ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (z : E) (B : ℝ) (hB : ∀ y, ψ y ≤ B) :
    metricBallMaximum ψ ρ z ≤ B := by
  obtain ⟨y, _, heq, _⟩ := metricBallMaximum_spec ψ hψ ρ hρ z
  rw [← heq]
  exact hB y

theorem metricBallMaximum_upper_neighborhood (ψ : E → ℝ) (hψ : Continuous ψ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (z : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w, dist w z < δ →
      metricBallMaximum ψ ρ w < metricBallMaximum ψ ρ z + ε := by
  let C := closedBall z (ρ + 1) ∩ {y | metricBallMaximum ψ ρ z + ε ≤ ψ y}
  have hC : IsCompact C :=
    (isCompact_closedBall z (ρ + 1)).inter_right (isClosed_Ici.preimage hψ)
  by_cases hne : C.Nonempty
  · obtain ⟨y₀, hy₀, hmin⟩ := hC.exists_isMinOn (f := fun y : E => dist y z) hne
      (continuous_id.dist (continuous_const (y := z))).continuousOn
    have hm : ρ < dist y₀ z := by
      by_contra hn
      have hyρ : y₀ ∈ closedBall z ρ := le_of_not_gt hn
      have H := le_metricBallMaximum ψ hψ ρ hρ z y₀ hyρ
      have H' := hy₀.2
      change metricBallMaximum ψ ρ z + ε ≤ ψ y₀ at H'
      linarith
    let δ := min (1 / 2 : ℝ) ((dist y₀ z - ρ) / 2)
    have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
    refine ⟨δ, hδ, ?_⟩
    intro w hw
    obtain ⟨y, hy, heq, _⟩ := metricBallMaximum_spec ψ hψ ρ hρ w
    by_contra hn
    have hlarge : metricBallMaximum ψ ρ z + ε ≤ ψ y := by
      rw [heq]
      exact le_of_not_gt hn
    have hy' : dist y w ≤ ρ := hy
    have hd : dist y z ≤ ρ + dist w z := by linarith [dist_triangle y w z]
    have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
    have hyC : y ∈ C := ⟨by change dist y z ≤ ρ + 1; linarith, hlarge⟩
    have hmin' : dist y₀ z ≤ dist y z := hmin hyC
    have hδm : δ ≤ (dist y₀ z - ρ) / 2 := min_le_right _ _
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro w hw
    obtain ⟨y, hy, heq, _⟩ := metricBallMaximum_spec ψ hψ ρ hρ w
    by_contra hn
    have hlarge : metricBallMaximum ψ ρ z + ε ≤ ψ y := by
      rw [heq]
      exact le_of_not_gt hn
    have hy' : dist y w ≤ ρ := hy
    have hd : dist y z ≤ ρ + dist w z := by linarith [dist_triangle y w z]
    exact hne ⟨y, ⟨by change dist y z ≤ ρ + 1; linarith, hlarge⟩⟩

theorem metricBallMaximum_lower_neighborhood (ψ : E → ℝ) (hψ : Continuous ψ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (z : E)
    (hclosure : closedBall z ρ ⊆ closure (ball z ρ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w, dist w z < δ →
      metricBallMaximum ψ ρ z - ε < metricBallMaximum ψ ρ w := by
  obtain ⟨y, hy, heq, _⟩ := metricBallMaximum_spec ψ hψ ρ hρ z
  have hlarge : metricBallMaximum ψ ρ z - ε < ψ y := by rw [heq]; linarith
  have hnear : ψ ⁻¹' Ioi (metricBallMaximum ψ ρ z - ε) ∈ 𝓝 y :=
    hψ.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hlarge)
  obtain ⟨y', hy'large, hy'ball⟩ := mem_closure_iff_nhds.mp (hclosure hy) _ hnear
  have hy'dist : dist y' z < ρ := hy'ball
  refine ⟨ρ - dist y' z, sub_pos.mpr hy'dist, ?_⟩
  intro w hw
  have hy'w : y' ∈ closedBall w ρ := by
    change dist y' w ≤ ρ
    have htri := dist_triangle y' z w
    rw [dist_comm z w] at htri
    linarith
  exact (show metricBallMaximum ψ ρ z - ε < ψ y' from hy'large).trans_le
    (le_metricBallMaximum ψ hψ ρ hρ w y' hy'w)

theorem metricBallMaximum_continuous (ψ : E → ℝ) (hψ : Continuous ψ)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hclosure : ∀ z : E, closedBall z ρ ⊆ closure (ball z ρ)) :
    Continuous (metricBallMaximum ψ ρ) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δu, hδu, hu⟩ := metricBallMaximum_upper_neighborhood ψ hψ ρ hρ z ε hε
  obtain ⟨δl, hδl, hl⟩ := metricBallMaximum_lower_neighborhood ψ hψ ρ hρ z (hclosure z) ε hε
  refine ⟨min δu δl, lt_min hδu hδl, ?_⟩
  intro w hw
  have Hu := hu w (hw.trans_le (min_le_left _ _))
  have Hl := hl w (hw.trans_le (min_le_right _ _))
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Yau.Proofs.C03Aux
