import Yau.LeafProofs.L22Basic

noncomputable section
open Filter
open scoped Topology

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L22Aux
variable {n : ℕ}

theorem circleAverage_tendsto_of_uniform (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ᶠ j in atTop, Continuous (f j)) (hg : Continuous g)
    (hunif : TendstoUniformly f g atTop) :
    Tendsto (fun j => circleAverage (f j)) atTop (𝓝 (circleAverage g)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have HE := (Metric.tendstoUniformly_iff.mp hunif) (ε/2) (by positivity)
  filter_upwards [HE,hf] with j hj hjc
  have hupper : circleAverage (f j) ≤ circleAverage g + ε/2 := by
    rw [← circleAverage_const (ε/2), ← circleAverage_add hg continuous_const]
    apply circleAverage_mono hjc (hg.add continuous_const)
    intro θ
    change f j θ ≤ g θ+ε/2
    have H := (abs_lt.mp (by simpa only [Real.dist_eq] using hj θ)).1
    linarith
  have hlower : circleAverage g - ε/2 ≤ circleAverage (f j) := by
    have H := circleAverage_mono hg (hjc.add (continuous_const (y := ε/2))) (fun θ => by
      change g θ ≤ f j θ+ε/2
      have HH := (abs_lt.mp (by simpa only [Real.dist_eq] using hj θ)).2
      linarith)
    change circleAverage g ≤ circleAverage (fun θ => f j θ+ε/2) at H
    rw [circleAverage_add hjc continuous_const, circleAverage_const] at H
    linarith
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

theorem complexLinePshOn_uniformLimit (O : Set (ComplexVector n))
    (f : ℕ → ComplexVector n → ℝ) (b : ComplexVector n → ℝ)
    (hb : ContinuousOn b O)
    (hf : ∀ᶠ j in atTop, LeafCandidates.ComplexLinePshOn O (f j))
    (hlim : ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ O →
      TendstoUniformlyOn f b atTop K) : LeafCandidates.ComplexLinePshOn O b := by
  refine ⟨hb,?_⟩
  intro z w hdisc
  let K : Set (ComplexVector n) := (fun ζ : ℂ => z+ζ • w) '' Metric.closedBall 0 1
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).image (by fun_prop)
  have hKO : K ⊆ O := by
    rintro _ ⟨ζ,hζ,rfl⟩
    apply hdisc ζ
    simpa only [Metric.mem_closedBall, dist_zero_right] using hζ
  have hθ (θ : ℝ) : z+Complex.exp (θ*Complex.I) • w ∈ K := by
    exact ⟨Complex.exp (θ*Complex.I), by simp, rfl⟩
  have hcirc : Continuous (fun θ : ℝ => z+Complex.exp (θ*Complex.I) • w) := by fun_prop
  have hbc : Continuous (fun θ : ℝ => b (z+Complex.exp (θ*Complex.I) • w)) :=
    hb.comp_continuous hcirc (fun θ => hKO (hθ θ))
  have hfc : ∀ᶠ j in atTop,
      Continuous (fun θ : ℝ => f j (z+Complex.exp (θ*Complex.I) • w)) := by
    filter_upwards [hf] with j hj
    exact hj.1.comp_continuous hcirc (fun θ => hKO (hθ θ))
  have huc : TendstoUniformly (fun (j : ℕ) (θ : ℝ) => f j (z+Complex.exp (θ*Complex.I) • w))
      (fun θ => b (z+Complex.exp (θ*Complex.I) • w)) atTop := by
    have H := (hlim K hK hKO).comp (fun θ : ℝ => z+Complex.exp (θ*Complex.I) • w)
    apply tendstoUniformlyOn_univ.mp
    exact H.mono (fun θ _ => hθ θ)
  have hmean := circleAverage_tendsto_of_uniform _ _ hfc hbc huc
  have hz : z ∈ K := ⟨0, by simp, by simp⟩
  have hcenter := (hlim K hK hKO).tendsto_at hz
  apply le_of_tendsto_of_tendsto hcenter hmean
  filter_upwards [hf] with j hj
  exact hj.2 z w hdisc

end Yau.NodeProofs.P02Aux
