import Yau.Proofs.C07ShortLiftIntegral
import Yau.Proofs.C07ShortLiftContinuation

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07ShortLiftAux

open Yau Yau.Blueprint Set MeasureTheory

variable {n : ℕ} {M : ComplexManifold n}

/-- Every sufficiently short integrable piecewise-C¹ curve starting at the
centre of a unitary local chart has a continuous lift in its original ball.
The same lift satisfies the prefix integral length estimate. -/
theorem short_curve_lift {k : HermitianField M} {o x : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hΦ : UnitaryChart k o Φ r c C)
    (γ : IntegrableCurve k o x)
    (hshort : curveLength k γ.1 < Real.sqrt (2 * c) * r) :
    ∃ η : ℝ → ComplexVector n,
      ContinuousOn η (Icc (0 : ℝ) 1) ∧ η 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, η t ∈ Metric.ball 0 r ∧ Φ (η t) = γ.1 t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        ‖η t‖ ≤ (Real.sqrt (2 * c))⁻¹ * (∫ u in Icc 0 t, curveSpeed k γ.1 u)) := by
  have hα : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.2 (by positivity)
  have hL : (Real.sqrt (2 * c))⁻¹ * curveLength k γ.1 < r :=
    (inv_mul_lt_iff₀ hα).2 hshort
  let R : ℝ := ((Real.sqrt (2 * c))⁻¹ * curveLength k γ.1 + r) / 2
  have hLR : (Real.sqrt (2 * c))⁻¹ * curveLength k γ.1 ≤ R := by
    dsimp [R]
    linarith
  have hRr : R < r := by
    dsimp [R]
    linarith
  have hKball : Metric.closedBall (0 : ComplexVector n) R ⊆ Metric.ball 0 r :=
    Metric.closedBall_subset_ball hRr
  have hp₀ : Φ 0 = γ.1 0 := hΦ.2.1.trans γ.1.start_eq.symm
  have hconf : ∀ b ∈ Icc (0 : ℝ) 1, ∀ ξ : ℝ → ComplexVector n,
      ContinuousOn ξ (Icc 0 b) → ξ 0 = 0 →
      (∀ t ∈ Icc 0 b, ξ t ∈ Metric.ball 0 r ∧ Φ (ξ t) = γ.1 t) →
      ∀ t ∈ Icc 0 b, ξ t ∈ Metric.closedBall 0 R := by
    intro b hb ξ hξ hξ₀ hξp t ht
    change dist (ξ t) 0 ≤ R
    rw [dist_zero_right]
    calc
      ‖ξ t‖ ≤ (Real.sqrt (2 * c))⁻¹ * (∫ u in Icc 0 t, curveSpeed k γ.1 u) :=
        partial_lift_norm_bound hc hΦ γ hb hξ hξ₀ hξp ht
      _ ≤ (Real.sqrt (2 * c))⁻¹ * curveLength k γ.1 :=
        mul_le_mul_of_nonneg_left (prefix_integral_le_length γ ⟨ht.1, ht.2.trans hb.2⟩)
          (inv_nonneg.mpr hα.le)
      _ ≤ R := hLR
  obtain ⟨η, hη, hη₀, hηp⟩ := exists_lift_of_compact_confinement
    (z₀ := (0 : ComplexVector n)) (by simpa using hr) hp₀
    (K := Metric.closedBall (0 : ComplexVector n) R) (isCompact_closedBall _ _) hKball
    hΦ.1.1.continuousOn
    (fun z hz => C07Aux.local_homeomorph_of_localBiholomorphism hΦ.1 hz)
    γ.1.continuous_on hconf
  refine ⟨η, hη, hη₀, hηp, ?_⟩
  intro t ht
  exact partial_lift_norm_bound hc hΦ γ ⟨zero_le_one, le_rfl⟩ hη hη₀ hηp ht

end Yau.Proofs.C07ShortLiftAux
