import Yau.Proofs.C03SourceMinimizingCurves
import Yau.Proofs.C03ShortLiftMapDistance
import Yau.Proofs.C03CompactTarget

/-! Short actual minimizing source curves give the genuine forward target
distance bound and the uniform compact-image fence for moving balls. -/

noncomputable section
open Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem chartExtendedField_forward_distance (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r c R : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hΦ : IsLocalBiholomorphism Φ r)
    (hlo : ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z))
    (hsmall : Real.sqrt ((min c 1)⁻¹) * R < r / 4)
    (z y : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (r / 2))
    (hzy : inducedDistance (chartExtendedField hn X Φ r hr hΦ) z y ≤ R) :
    inducedDistance X.metric.form (Φ z) (Φ y) ≤
      inducedDistance (chartExtendedField hn X Φ r hr hΦ) z y := by
  obtain ⟨γ, himage, hlength⟩ := exists_short_chart_minimizing_curve hn X Φ r c R
    hr hc hΦ hlo hsmall z y hz hzy
  have hsub : Metric.ball (0 : ComplexVector n) (3 * r / 4) ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (by linarith)
  exact ShortLift.forward_distance_of_minimizing_curve (hΦ.1.mono hsub) hn
    (chartExtendedField hn X Φ r hr hΦ) X.metric.form
    (fun w hw u v => chartExtendedField_pullback hn X Φ r hr hΦ w hw u v)
    γ himage hlength

theorem chart_moving_ball_target_fence (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r c ρ ε : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hΦ : IsLocalBiholomorphism Φ r)
    (hlo : ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z))
    (hsmall : Real.sqrt ((min c 1)⁻¹) * (2 * ρ) < r / 4) (hρε : 2 * ρ ≤ ε)
    (K K' : Set X.manifold.Carrier) (h0 : Φ 0 ∈ K)
    (hK' : ∀ o ∈ K, ∀ y : X.manifold.Carrier,
      inducedDistance X.metric.form o y ≤ ε → y ∈ K')
    (z y : ComplexVector n)
    (hz : inducedDistance (chartExtendedField hn X Φ r hr hΦ) (0 : ComplexVector n) z ≤ ρ)
    (hzy : inducedDistance (chartExtendedField hn X Φ r hr hΦ) z y ≤ ρ) : Φ y ∈ K' := by
  let k := chartExtendedField hn X Φ r hr hΦ
  have ks : MetricSmooth k := chartExtendedField_metricSmooth hn X Φ r hr hΦ
  have hy : inducedDistance k (0 : ComplexVector n) y ≤ 2 * ρ := by
    have H := inducedDistance_triangle k ks (0 : ComplexVector n) z y
    linarith
  apply hK' (Φ 0) h0 (Φ y)
  exact (chartExtendedField_forward_distance hn X Φ r c (2 * ρ) hr hc hΦ hlo hsmall
    (0 : ComplexVector n) y (Metric.mem_ball_self (by linarith)) hy).trans (hy.trans hρε)

theorem exists_chart_transport_radius (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (d : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ ≤ ε ∧ Real.sqrt (d⁻¹) * (2 * ρ) < r / 4 := by
  let a := 1 + Real.sqrt (d⁻¹)
  have ha : 0 < a := by dsimp only [a]; positivity
  let ρ := min (ε / 4) (r / (16 * a))
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  refine ⟨ρ, hρ, ?_, ?_⟩
  · have H : ρ ≤ ε / 4 := min_le_left _ _
    linarith
  · have H : ρ ≤ r / (16 * a) := min_le_right _ _
    have Hmul : ρ * (16 * a) ≤ r := (le_div_iff₀ (by positivity)).mp H
    dsimp only [a] at Hmul
    nlinarith [Real.sqrt_nonneg (d⁻¹)]

end Yau.Proofs.C03Aux
