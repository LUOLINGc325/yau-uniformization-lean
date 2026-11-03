import Yau.LeafProofs.L19HeatGaussianTailDoubleBall
import Yau.LeafProofs.L19GaussianHarnack

/-! Extraction of the original symmetric Gaussian estimate from the actual
two-ball heat pairing. The sole remaining kernel identification is explicit,
including integrability of the outer integral. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The actual iterated kernel integral equals the pairing of the independently
constructed heat flow. Outer integrability is part of this explicit gap. -/
def BallKernelPairingIdentity (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (H : ℝ → M.Carrier → M.Carrier → ℝ) : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ (x y : M.Carrier) (rx ry : ℝ)
    (hrx : 0 < rx) (hry : 0 < ry),
    IntegrableOn (fun w => ∫ z in distBall g.form x rx, H t z w ∂μ)
      (distBall g.form y ry) μ ∧
    (∫ w in distBall g.form y ry, (∫ z in distBall g.form x rx, H t z w ∂μ) ∂μ) =
      ⟪scalarBallL2 g μ hμ y ry hry,
        scalarHeatFamily g μ hμ t (scalarBallL2 g μ hμ x rx hrx)⟫_ℝ

/-- Two original Harnack inequalities may be integrated over two genuine
finite positive balls, without any joint smoothness assumption on the kernel. -/
theorem scalarHeatKernel_two_ball_average (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ}
    (hH : LeafCandidates.ScalarHeatKernel g.form μ H)
    {t : ℝ} (ht : 0 < t) (x y : M.Carrier)
    (houter : IntegrableOn
      (fun w => ∫ z in distBall g.form x (Real.sqrt t), H (3 * t) z w ∂μ)
      (distBall g.form y (Real.sqrt t)) μ) :
    (μ (distBall g.form x (Real.sqrt t))).toReal *
        (μ (distBall g.form y (Real.sqrt t))).toReal * H t x y ≤
      (3 : ℝ) ^ n * Real.exp 1 *
        ∫ w in distBall g.form y (Real.sqrt t),
          (∫ z in distBall g.form x (Real.sqrt t), H (3 * t) z w ∂μ) ∂μ := by
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h3t : 0 < 3 * t := by positivity
  have hfx := (riemannianVolume_distBall_lt_top g μ hμ x hr).ne
  have hfy := (riemannianVolume_distBall_lt_top g μ hμ y hr).ne
  have hinner : ∀ w ∈ distBall g.form y (Real.sqrt t),
      (μ (distBall g.form x (Real.sqrt t))).toReal * H t x y ≤
        (3 : ℝ) ^ n * Real.exp 1 *
          ∫ z in distBall g.form x (Real.sqrt t), H (3 * t) z w ∂μ := by
    intro w hw
    have hi := smoothFn_integrableOn_distBall g μ hμ
      (positiveHeatSolution_slice g.form (hH.1 w) h3t) x hr
    have hmono := setIntegral_mono_on (integrableOn_const hfx (by finiteness))
      (hi.const_mul ((3 : ℝ) ^ n * Real.exp 1))
      (measurableSet_distBall g x (Real.sqrt t)) (fun z hz =>
        scalarHeatKernel_triple_time_harnack g hcomplete hK hRic hH ht x y z w
          ((mem_distBall_iff g x z hr).mp hz).le
          ((mem_distBall_iff g y w hr).mp hw).le)
    simpa only [setIntegral_const, smul_eq_mul, integral_const_mul, Measure.real] using hmono
  have hmono := setIntegral_mono_on (integrableOn_const hfy (by finiteness))
    (houter.const_mul ((3 : ℝ) ^ n * Real.exp 1))
    (measurableSet_distBall g y (Real.sqrt t)) hinner
  simp only [setIntegral_const, smul_eq_mul, integral_const_mul, Measure.real] at hmono
  simpa only [mul_assoc, mul_left_comm] using hmono

/-- The positive gap between two radius-sqrt(t) balls controls the original
distance, with the additive loss absorbed by a numerical exponential. -/
theorem gaussian_double_ball_exponent (A D t : ℝ) (hA : 1 ≤ A)
    (hD : 0 ≤ D) (ht : 0 < t) :
    -(max (D - Real.sqrt t - Real.sqrt t) 0) ^ 2 / (2 * A ^ 2 * (3 * t)) ≤
      1 - (1 / (12 * A ^ 2)) * D ^ 2 / t := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hsq := Real.sq_sqrt ht.le
  have hr := Real.sqrt_nonneg t
  have hgap : D ^ 2 ≤ 2 * (max (D - Real.sqrt t - Real.sqrt t) 0) ^ 2 + 8 * t := by
    by_cases h : 0 ≤ D - Real.sqrt t - Real.sqrt t
    · rw [max_eq_left h]
      nlinarith [sq_nonneg (D - 4 * Real.sqrt t)]
    · rw [max_eq_right (le_of_not_ge h)]
      have hsmall : D ≤ 2 * Real.sqrt t := by linarith
      nlinarith
  have hden : 0 < 12 * A ^ 2 * t := by positivity
  apply (mul_le_mul_iff_left₀ hden).mp
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hA2) ht.le]

/-- Dimension-only constants are chosen before every geometric datum. The
pairing identity is the only extra hypothesis beyond the frozen kernel type. -/
theorem exists_uniform_gaussian_of_ball_pairingIdentity (n : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : ComplexManifold n) (g : SmoothMetric M),
        IsComplete g → IsKahler g → (∀ x, (ricci g.form x).PosSemidef) →
        ∀ (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
          (H : ℝ → M.Carrier → M.Carrier → ℝ),
          LeafCandidates.ScalarHeatKernel g.form μ H → BallKernelPairingIdentity g μ hμ H →
          ∀ t, 0 < t → ∀ x y,
            H t x y ≤ C * Real.exp (-c * distFrom g.form x y ^ 2 / t) /
              Real.sqrt ((μ (distBall g.form x (Real.sqrt t))).toReal *
                (μ (distBall g.form y (Real.sqrt t))).toReal) := by
  obtain ⟨A, hA, hDG⟩ := exists_uniform_double_ball_heat_DG n
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  refine ⟨(3 : ℝ) ^ n * Real.exp 2, 1 / (12 * A ^ 2), by positivity, by positivity, ?_⟩
  intro M g hcomplete hK hRic μ hμ H hH hpair t ht x y
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h3t : 0 < 3 * t := by positivity
  obtain ⟨houter, hid⟩ := hpair (3 * t) h3t x y _ _ hr hr
  have havg := scalarHeatKernel_two_ball_average g hcomplete hK hRic μ hμ hH ht x y houter
  rw [hid] at havg
  have hdg := hDG M g μ hμ x y (Real.sqrt t) (Real.sqrt t) (3 * t) hr hr h3t
  let V := (μ (distBall g.form x (Real.sqrt t))).toReal *
    (μ (distBall g.form y (Real.sqrt t))).toReal
  have hV : 0 < V := mul_pos
    (ENNReal.toReal_pos (riemannianVolume_distBall_pos g μ hμ x hr).ne'
      (riemannianVolume_distBall_lt_top g μ hμ x hr).ne)
    (ENNReal.toReal_pos (riemannianVolume_distBall_pos g μ hμ y hr).ne'
      (riemannianVolume_distBall_lt_top g μ hμ y hr).ne)
  have hsqrt : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hsq : Real.sqrt V * Real.sqrt V = V := Real.mul_self_sqrt hV.le
  have hbound : V * H t x y ≤ (3 : ℝ) ^ n * Real.exp 1 *
      (Real.exp (-(max (inducedDistance g.form x y - Real.sqrt t - Real.sqrt t) 0) ^ 2 /
        (2 * A ^ 2 * (3 * t))) * Real.sqrt V) := by
    exact havg.trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hdg) (by positivity))
  have he := gaussian_double_ball_exponent A (inducedDistance g.form x y) t hA
    (g.induced_distance_nonneg x y) ht
  have hexp := Real.exp_le_exp.mpr he
  have hbound' : V * H t x y ≤ ((3 : ℝ) ^ n * Real.exp 2 *
      Real.exp (-(1 / (12 * A ^ 2)) * inducedDistance g.form x y ^ 2 / t)) * Real.sqrt V := by
    calc
      _ ≤ (3 : ℝ) ^ n * Real.exp 1 *
          (Real.exp (1 - (1 / (12 * A ^ 2)) * inducedDistance g.form x y ^ 2 / t) *
            Real.sqrt V) := hbound.trans (by gcongr)
      _ = _ := by
        rw [show 1 - (1 / (12 * A ^ 2)) * inducedDistance g.form x y ^ 2 / t =
          1 + (-(1 / (12 * A ^ 2)) * inducedDistance g.form x y ^ 2 / t) by ring,
          Real.exp_add]
        have hexp2 : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
          rw [← Real.exp_add]; norm_num
        calc
          _ = (3 : ℝ) ^ n * (Real.exp 1 * Real.exp 1) *
              Real.exp (-(1 / (12 * A ^ 2)) * inducedDistance g.form x y ^ 2 / t) *
                Real.sqrt V := by ring
          _ = _ := by rw [hexp2]
  change H t x y ≤ _ / Real.sqrt V
  apply (le_div_iff₀ hsqrt).mpr
  have hbound'' : Real.sqrt V * (H t x y * Real.sqrt V) ≤
      Real.sqrt V * ((3 : ℝ) ^ n * Real.exp 2 *
        Real.exp (-(1 / (12 * A ^ 2)) * inducedDistance g.form x y ^ 2 / t)) := by
    calc
      _ = (Real.sqrt V * Real.sqrt V) * H t x y := by ring
      _ = V * H t x y := by rw [hsq]
      _ ≤ _ := hbound'
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hsqrt).mp hbound''

/-- Closing the actual ball pairing identity for all original kernel data
closes the unchanged Li--Yau Gaussian target. -/
theorem liYauGaussian_of_ball_pairingIdentity
    (hpair : ∀ (n : ℕ) (M : ComplexManifold n) (g : SmoothMetric M),
      IsComplete g → IsKahler g → (∀ x, (ricci g.form x).PosSemidef) →
      ∀ (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
        (H : ℝ → M.Carrier → M.Carrier → ℝ),
        LeafCandidates.ScalarHeatKernel g.form μ H → BallKernelPairingIdentity g μ hμ H) :
    LeafCandidates.LiYauGaussian := by
  intro n hn
  obtain ⟨C, c, hC, hc, hbound⟩ := exists_uniform_gaussian_of_ball_pairingIdentity n
  refine ⟨C, c, hC, hc, ?_⟩
  intro M g hcomplete hK hRic μ hμ H hH
  exact hbound M g hcomplete hK hRic μ hμ H hH (hpair n M g hcomplete hK hRic μ hμ H hH)

end Yau.LeafProofs.L19Aux
