import Yau.Proofs.P07SupportWeakMollifier

noncomputable section
open Filter Set Metric MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace Yau.NodeProofs.P07Aux.SupportWeak
open Yau Yau.Blueprint Yau.LeafProofs L18Aux L22Aux P06Aux
variable {n : ℕ}

/-- One compact buffer and one positive mollifier retain the original variable right side. -/
theorem exists_smooth_directionalUpper_approx_on_compact
    {O : Set (ComplexVector n)} {f h : ComplexVector n → ℝ} {v : ComplexVector n}
    (hO : IsOpen O) (hf : ContinuousOn f O) (hh : ContinuousOn h O)
    (hs : LocalDirectionalUpperSupportsOn O f h v)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKO : K ⊆ O)
    {η σ : ℝ} (hη : 0 < η) (hσ : 0 < σ) :
    ∃ u : ComplexVector n → ℝ, ContDiff ℝ ∞ u ∧
      (∀ z ∈ K, |u z - f z| ≤ σ) ∧
      (∀ z ∈ K, leviDirection (leviC u z) v ≤ h z + η) := by
  obtain ⟨ρ, hρ, hρO⟩ := hK.exists_cthickening_subset_open hO hKO
  let D : Set (ComplexVector n) := cthickening ρ K
  have hD : IsCompact D := hK.cthickening
  let fc : C(D, ℝ) := ⟨fun z => f z, (hf.mono hρO).restrict⟩
  obtain ⟨F, hF⟩ := fc.exists_restrict_eq hD.isClosed
  have hEq : EqOn F f D := by
    intro z hz
    exact congrArg (fun q : C(D, ℝ) => q ⟨z, hz⟩) hF
  have hUF := hD.uniformContinuousOn_of_continuous F.continuous.continuousOn
  have hUh := hD.uniformContinuousOn_of_continuous (hh.mono hρO)
  obtain ⟨df, hdf, hfdist⟩ := Metric.uniformContinuousOn_iff.mp hUF (σ / 2) (half_pos hσ)
  obtain ⟨dh, hdh, hhdist⟩ := Metric.uniformContinuousOn_iff.mp hUh η hη
  let δ : ℝ := min (ρ / 4) (min (df / 2) (dh / 4))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδρ : δ ≤ ρ / 4 := min_le_left _ _
  have hδdf : δ < df := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hδdh : 2 * δ < dh := by
    have hh : δ ≤ dh / 4 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  let β : ContDiffBump (0 : ComplexVector n) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let u : ComplexVector n → ℝ := β.normed volume ⋆[lsmul ℝ ℝ, volume] (fun z => F z)
  have hu : ContDiff ℝ ∞ u :=
    β.hasCompactSupport_normed.contDiff_convolution_left _ β.contDiff_normed
      F.continuous.locallyIntegrable
  have hKD : K ⊆ D := Metric.self_subset_cthickening K
  have hnearD {z w : ComplexVector n} (hz : z ∈ K) (hw : dist w z ≤ 2 * δ) : w ∈ D := by
    exact Metric.closedBall_subset_cthickening hz ρ
      (hw.trans (by linarith : 2 * δ ≤ ρ))
  refine ⟨u, hu, ?_, ?_⟩
  · intro z hz
    have hbound : ∀ x ∈ ball z β.rOut, dist (F x) (F z) ≤ σ / 2 := by
      intro x hx
      have hxδ : dist x z < δ := Metric.mem_ball.mp hx
      have hxD : x ∈ D := hnearD hz (by linarith)
      exact (hfdist x hxD z (hKD hz) (hxδ.trans hδdf)).le
    have hb := β.dist_normed_convolution_le (μ := volume)
      F.continuous.aestronglyMeasurable hbound
    change |u z - f z| ≤ σ
    rw [← hEq (hKD hz), ← Real.dist_eq]
    exact hb.trans (by linarith)
  · intro z hz
    apply leviDirection_le_of_local_supermean hu z v (h z + η)
    have hden : 0 < ‖v‖ + 1 := by positivity
    have hR : 0 < δ / (‖v‖ + 1) := div_pos hδ hden
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hR] with r hr
    have hr' : |r| < δ / (‖v‖ + 1) := by simpa only [mem_ball, Real.dist_eq, sub_zero] using hr
    have hrv : |r| * ‖v‖ < δ := by
      have hsmall := (mul_lt_mul_of_pos_right hr' hden).trans_eq (div_mul_cancel₀ δ hden.ne')
      nlinarith [abs_nonneg r]
    apply normalized_convolution_supermean F.continuous β z v r (h z + η)
    intro a ha
    have haδ : ‖a‖ ≤ δ := by simpa only [mem_closedBall, dist_zero_right] using ha
    have hdist (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) :
        dist (z - a + ζ • (r • v)) z < 2 * δ := by
      rw [dist_eq_norm]
      have heq : z - a + ζ • (r • v) - z = -a + ζ • (r • v) := by abel
      rw [heq]
      calc
        ‖-a + ζ • (r • v)‖ ≤ ‖-a‖ + ‖ζ • (r • v)‖ := norm_add_le _ _
        _ = ‖a‖ + ‖ζ‖ * (|r| * ‖v‖) := by rw [norm_neg, norm_smul, norm_smul, Real.norm_eq_abs]
        _ ≤ δ + |r| * ‖v‖ := add_le_add haδ (mul_le_of_le_one_left (by positivity) hζ)
        _ < 2 * δ := by linarith
    have hdiscD (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) : z - a + ζ • (r • v) ∈ D :=
      hnearD hz (hdist ζ hζ).le
    have hdiscO (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) : z - a + ζ • (r • v) ∈ O := hρO (hdiscD ζ hζ)
    have hright (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) : h (z - a + ζ • (r • v)) ≤ h z + η := by
      have H := hhdist _ (hdiscD ζ hζ) z (hKD hz) ((hdist ζ hζ).trans hδdh)
      rw [Real.dist_eq] at H
      linarith [(abs_lt.mp H).2]
    have hm := angularLineMean_le_of_localUpperSupports hf hs r (h z + η) hdiscO hright
    have hcenterD : z - a ∈ D := by simpa only [zero_smul, add_zero] using hdiscD 0 (by simp)
    rw [← hEq hcenterD] at hm
    convert hm using 1
    unfold angularLineMean
    congr 1
    funext θ
    apply hEq
    have hζ : ‖Complex.exp (θ * Complex.I)‖ ≤ 1 := by simp
    simpa only [smul_comm r] using hdiscD (Complex.exp (θ * Complex.I)) hζ

end Yau.NodeProofs.P07Aux.SupportWeak
