import Yau.Proofs.D04Majorants

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem circleAverage_const (c : ℝ) : circleAverage (fun _ => c) = c := by
  unfold circleAverage
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem circleAverage_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ θ, f θ ≤ g θ) : circleAverage f ≤ circleAverage g := by
  apply mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (fun θ _ => hfg θ))
  positivity

theorem isPshOn_const (Ω : Set (ComplexVector n)) (c : ℝ) :
    IsPshOn (fun _ => (c : EReal)) Ω := by
  refine ⟨fun _ _ => EReal.coe_lt_top c, upperSemicontinuousOn_const, ?_⟩
  intro z w _ φ hφ hmajor
  apply EReal.coe_le_coe_iff.mpr
  rw [← circleAverage_const c]
  exact circleAverage_mono continuous_const hφ (fun θ => EReal.coe_le_coe_iff.mp (hmajor θ))

theorem isPshOn_max {u v : ComplexVector n → EReal} {Ω : Set (ComplexVector n)}
    (hu : IsPshOn u Ω) (hv : IsPshOn v Ω) :
    IsPshOn (fun z => max (u z) (v z)) Ω := by
  refine ⟨fun z hz => max_lt (hu.1 z hz) (hv.1 z hz), hu.2.1.sup hv.2.1, ?_⟩
  intro z w hdisc φ hφ hmajor
  exact max_le
    (hu.2.2 z w hdisc φ hφ (fun θ => (le_max_left _ _).trans (hmajor θ)))
    (hv.2.2 z w hdisc φ hφ (fun θ => (le_max_right _ _).trans (hmajor θ)))

/-- Domainwise equality transports the complete predicate, including circle
values. It does not identify functions merely from `toReal`. -/
theorem isPshOn_congr {u v : ComplexVector n → EReal} {Ω : Set (ComplexVector n)}
    (hu : IsPshOn u Ω) (heq : Set.EqOn u v Ω) : IsPshOn v Ω := by
  refine ⟨fun z hz => (heq hz) ▸ hu.1 z hz, ?_, ?_⟩
  · intro z hz
    apply UpperSemicontinuousWithinAt.congr_of_eventuallyEq (hu.2.1 z hz) hz
    exact eventually_nhdsWithin_of_forall heq
  · intro z w hdisc φ hφ hmajor
    have hz : z ∈ Ω := by simpa using hdisc 0 (by simp)
    rw [← heq hz]
    apply hu.2.2 z w hdisc φ hφ
    intro θ
    rw [heq (hdisc (Complex.exp (θ * Complex.I)) (by simp))]
    exact hmajor θ

/-- Finite lower truncations remain psh in every complex dimension. -/
theorem isPshOn_lowerTrunc {u : ComplexVector n → EReal} {Ω : Set (ComplexVector n)}
    (hu : IsPshOn u Ω) (k : ℕ) :
    IsPshOn (fun z => (lowerTrunc u k z : EReal)) Ω := by
  apply isPshOn_congr (isPshOn_max hu (isPshOn_const Ω (-(k : ℝ))))
  intro z hz
  exact (coe_lowerTrunc k (hu.1 z hz)).symm

end Yau.Proofs.D04Aux
