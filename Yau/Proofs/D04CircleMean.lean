import Yau.Proofs.D04Truncation

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem circleAverage_add_const {φ : ℝ → ℝ} (hφ : Continuous φ) (ε : ℝ) :
    circleAverage (fun θ => φ θ + ε) = circleAverage φ + ε := by
  unfold circleAverage
  rw [intervalIntegral.integral_add (hφ.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_add]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem circleAverage_mono_on {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ θ ∈ Icc 0 (2 * Real.pi), f θ ≤ g θ) : circleAverage f ≤ circleAverage g := by
  apply mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) hfg)
  positivity

/-- Circle majorants need only dominate on the actual integration interval.
The proof supplies a continuous periodic majorant for the original frozen
predicate, so no periodicity assumption is added to the test function. -/
theorem intervalMajorant_submean
    {Ω : Set (ComplexVector n)} {u : ComplexVector n → EReal}
    (hu : IsPshOn u Ω) (z w : ComplexVector n)
    (hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ Ω)
    {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hmajor : ∀ θ ∈ Icc 0 (2 * Real.pi),
      u (z + Complex.exp (θ * Complex.I) • w) ≤ (φ θ : EReal)) :
    u z ≤ (circleAverage φ : EReal) := by
  let K : Set (ComplexVector n) :=
    (fun ζ : ℂ => z + ζ • w) '' Metric.closedBall 0 1
  have hc : Continuous (fun ζ : ℂ => z + ζ • w) := by fun_prop
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).image hc
  have hKO : K ⊆ Ω := by
    rintro y ⟨ζ, hζ, rfl⟩
    exact hdisc ζ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hζ)
  have hzK : z ∈ K := ⟨0, by simp, by simp⟩
  have hcircleK (θ : ℝ) : z + Complex.exp (θ * Complex.I) • w ∈ K := by
    exact ⟨Complex.exp (θ * Complex.I), by simp [Metric.mem_closedBall], rfl⟩
  obtain ⟨B, hB⟩ := compact_upper_bound hK (hu.2.1.mono hKO)
    (fun y hy => hu.1 y (hKO hy))
  let C : ℝ := max B 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ y ∈ K, u y ≤ (C : EReal) := fun y hy =>
    (hB y hy).trans (EReal.coe_le_coe_iff.mpr (le_max_left B 0))
  let F : ℕ → ComplexVector n → ℝ := majorantEnvelope K u
  have hFc (j : ℕ) : Continuous (F j) :=
    (majorantEnvelope_lipschitz ⟨z, hzK⟩ hC0 hC j).continuous
  have hpath : Continuous (fun θ : ℝ => z + Complex.exp (θ * Complex.I) • w) := by fun_prop
  by_contra hnot
  have hlt : (circleAverage φ : EReal) < u z := lt_of_not_ge hnot
  obtain ⟨q, hq, hqu⟩ := EReal.exists_between_coe_real hlt
  have hqreal : circleAverage φ < q := EReal.coe_lt_coe_iff.mp hq
  let ε : ℝ := (q - circleAverage φ) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  let U : ℕ → Set ℝ := fun j =>
    {θ | F j (z + Complex.exp (θ * Complex.I) • w) < φ θ + ε}
  have hUopen (j : ℕ) : IsOpen (U j) :=
    isOpen_lt ((hFc j).comp hpath) (hφ.add continuous_const)
  have hcover : Icc 0 (2 * Real.pi) ⊆ ⋃ j, U j := by
    intro θ hθ
    have hlim := tendsto_majorantEnvelope hC0 hC (hu.2.1.mono hKO) (hcircleK θ)
    have hbound : u (z + Complex.exp (θ * Complex.I) • w) < ((φ θ + ε : ℝ) : EReal) :=
      (hmajor θ hθ).trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
    obtain ⟨j, hj⟩ := ((tendsto_order.mp hlim).2 _ hbound).exists
    exact mem_iUnion.mpr ⟨j, EReal.coe_lt_coe_iff.mp hj⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro θ hθ
      exact (majorantEnvelope_antitone ⟨z, hzK⟩ hC0 hC _ (le_max_left i j)).trans_lt hθ
    · intro θ hθ
      exact (majorantEnvelope_antitone ⟨z, hzK⟩ hC0 hC _ (le_max_right i j)).trans_lt hθ
  obtain ⟨N, hN⟩ := isCompact_Icc.elim_directed_cover U hUopen hcover hdir
  have hmean : u z ≤ (circleAverage (fun θ => F N (z + Complex.exp (θ * Complex.I) • w)) : EReal) :=
    hu.2.2 z w hdisc _ ((hFc N).comp hpath)
      (fun θ => le_coe_majorantEnvelope hC0 hC N (hcircleK θ))
  have havg : circleAverage (fun θ => F N (z + Complex.exp (θ * Complex.I) • w)) ≤
      circleAverage φ + ε :=
    (circleAverage_mono_on ((hFc N).comp hpath) (hφ.add continuous_const)
      (fun θ hθ => (hN hθ).le)).trans_eq (circleAverage_add_const hφ ε)
  have hupper := hmean.trans (EReal.coe_le_coe_iff.mpr havg)
  have hstrict : ((circleAverage φ + ε : ℝ) : EReal) < u z :=
    (EReal.coe_lt_coe_iff.mpr (by dsimp only [ε]; linarith)).trans hqu
  exact (not_le_of_gt hstrict) hupper

end Yau.Proofs.D04Aux
