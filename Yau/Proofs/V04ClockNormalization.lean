import Yau.Proofs.V04ClockLiftCandidate
import Yau.Proofs.V03Walls

/-! The original raw clock has a genuinely positive normalizer on every
admissible disc. Its normalized weight has mean one, and its actual
positive Fourier extension is a clock lift with a nonnegative interior
physical-time exponent. -/

open scoped Matrix Topology ComplexOrder ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem clockWeightRaw_pos {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (θ : ℝ) : 0 < clockWeightRaw d k j a F θ := by
  have hm := (admissible_wallPower_bounds hd hF a θ).1
  dsimp only [clockWeightRaw]
  exact mul_pos (mul_pos (pow_pos hm 4) (Real.exp_pos _)) (Real.exp_pos _)

theorem clockWeightRaw_periodic (d : VariationData X q) (k : ClockData X)
    (j a : ℕ) (F : VariationDisc X) : Function.Periodic (clockWeightRaw d k j a F) (2 * Real.pi) := by
  intro θ
  simp only [clockWeightRaw, circlePoint_periodic θ]

theorem clockWeightRaw_average_pos {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (hc : Continuous (clockWeightRaw d k j a F)) :
    0 < circleAverage (clockWeightRaw d k j a F) := by
  unfold circleAverage
  apply mul_pos (by positivity)
  apply intervalIntegral.integral_pos (by positivity) hc.continuousOn
  · intro θ _
    exact (clockWeightRaw_pos hd hF θ).le
  · exact ⟨0, ⟨le_rfl, by positivity⟩, clockWeightRaw_pos hd hF 0⟩

theorem clockWeight_normalization {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (hc : Continuous (clockWeightRaw d k j a F)) :
    (∀ θ, 0 < clockWeight d k j a F θ) ∧ circleAverage (clockWeight d k j a F) = 1 := by
  have hZ := clockWeightRaw_average_pos hd hF hc
  constructor
  · intro θ
    exact div_pos (clockWeightRaw_pos hd hF θ) hZ
  · have hh := circleAverage_const_add_div hc 0 (circleAverage (clockWeightRaw d k j a F))
    change circleAverage (fun θ => clockWeightRaw d k j a F θ /
      circleAverage (clockWeightRaw d k j a F)) = 1
    simpa only [zero_add, div_self hZ.ne'] using hh

theorem clockLift_of_raw_regular {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (hc : ContDiff ℝ ∞ (clockWeightRaw d k j a F)) :
    ∃ Γ : ℂ → ℂ, ClockLift d k j a F Γ ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ 1 + (Γ z).re := by
  let γ := clockWeight d k j a F
  have hγ : ContDiff ℝ ∞ γ := hc.div_const _
  have hp : Function.Periodic γ (2 * Real.pi) := by
    intro θ
    simp only [γ, clockWeight, clockWeightRaw_periodic d k j a F θ]
  have hn := clockWeight_normalization hd hF hc.continuous
  have hs := clockLiftCandidate_smooth hγ hp
  have hb := clockLiftCandidate_zero_real_boundary hγ hp hn.2
  refine ⟨clockLiftCandidate γ, ⟨hs, hb.1, hb.2⟩, ?_⟩
  apply closedDisc_real_part_lower hs
  intro θ
  rw [hb.2 θ]
  linarith only [(hn.1 θ).le]

end Yau.Blueprint.V04Proof
