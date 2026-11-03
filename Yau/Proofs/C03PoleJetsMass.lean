import Yau.Proofs.C03PoleJetsDensity
import Yau.Proofs.C03PoleJetsKernel
import Yau.Proofs.C03PoleIntegral

/-! Finite critical weighted mass gives an actual coefficient sequence
tending to zero, rather than only a bounded big-O coefficient. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff ENNReal

namespace Yau.Proofs.C03Aux.PoleJets

open Yau Yau.NodeProofs.P03Aux
variable {n : ℕ}

theorem approxRadius_antitone {ρ : ℝ} (hρ : 0 ≤ ρ) : Antitone (approxRadius ρ) := by
  intro i j hij
  unfold approxRadius
  apply div_le_div_of_nonneg_left hρ (by positivity)
  exact_mod_cast Nat.add_le_add_right hij 2

theorem real_jets_zero_of_finite_density
    (hn : 1 ≤ n) (f : ComplexVector n → ℂ) (hc : Continuous f) (hfc : HasCompactSupport f)
    (R : ℝ) (hR : 0 < R) (hH : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hW : IntegrableOn (weightedDensity (2 * (n + 1)) f) (Metric.ball 0 R) volume) :
    ∀ j ≤ 1, iteratedFDeriv ℝ j f 0 = 0 := by
  let ρ := R / 4
  let p := 2 * (n + 1)
  let J : ℕ → ℝ := fun i =>
    ∫ z in Metric.ball (0 : ComplexVector n) (2 * approxRadius ρ i) \ {0}, weightedDensity p f z
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρR : 3 * ρ < R := by dsimp [ρ]; linarith
  have hrR (i : ℕ) : 2 * approxRadius ρ i < R := by
    have h := approxRadius_le hρ i
    dsimp [ρ] at h
    linarith
  have hanti : Antitone (fun i => 2 * approxRadius ρ i) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (approxRadius_antitone hρ.le hij) (by norm_num)
  have hrad : Tendsto (fun i => 2 * approxRadius ρ i) atTop (𝓝 0) := by
    simpa only [mul_zero] using (approxRadius_tendsto ρ).const_mul 2
  have hJ0 : Tendsto J atTop (𝓝 0) := by
    apply Yau.Proofs.C03Aux.punctured_ball_integral_tendsto_zero volume
      (weightedDensity p f) 0 (fun i => 2 * approxRadius ρ i) hanti hrad
    exact hW.mono_set (fun z hz => Metric.ball_subset_ball (hrR 0).le hz.1)
  have hJ (i : ℕ) : 0 ≤ J i := integral_nonneg (weightedDensity_nonneg p f)
  let D : ℕ → ℝ := fun i => 2 ^ p * J i
  have hD (i : ℕ) : 0 ≤ D i := mul_nonneg (by positivity) (hJ i)
  have hD0 : Tendsto D atTop (𝓝 0) := by
    simpa only [mul_zero] using hJ0.const_mul ((2 : ℝ) ^ p)
  have hf2 : Integrable (fun z => ‖f z‖ ^ 2) volume :=
    (hc.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞)) hfc).integrable_norm_pow (by norm_num)
  have hL2 (i : ℕ) :
      (∫ z in Metric.closedBall (0 : ComplexVector n) (approxRadius ρ i), ‖f z‖ ^ 2) ≤
        D i * approxRadius ρ i ^ (2 * (n + 1)) := by
    calc
      _ ≤ (2 * approxRadius ρ i) ^ p * J i :=
        closedBall_L2_le_punctured_mass hn p f hf2 R hW (approxRadius_pos hρ i) (hrR i)
      _ = _ := by dsimp only [D, p]; rw [mul_pow]; ring
  exact real_jets_zero_of_critical_sequence f hc hfc R hH ρ hρ hρR D hD hD0 hL2

end Yau.Proofs.C03Aux.PoleJets
