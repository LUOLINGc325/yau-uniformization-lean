import Yau.Proofs.F04Volume
import Yau.Proofs.F04SourcePositive

open MeasureTheory Filter Set
open scoped Topology Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

theorem ball_volume_facts {n : ℕ} (X : KahlerManifold n) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (o : Pt X) {r : ℝ} (hr : 0 < r) :
    MeasurableSet (distBall X.metric.form o r) ∧ 0 < μ (distBall X.metric.form o r) ∧
      μ (distBall X.metric.form o r) < ⊤ ∧ 0 < (μ (distBall X.metric.form o r)).toReal := by
  have hp := riemannianVolume_distBall_pos X.metric μ hμ o hr
  have hf := riemannianVolume_distBall_lt_top X.metric μ hμ o hr
  exact ⟨LeafProofs.L12Aux.measurableSet_distBall X.metric o r, hp, hf,
    ENNReal.toReal_pos hp.ne' hf.ne⟩

theorem ballIntegralLE_iff_average {n : ℕ} (X : KahlerManifold n) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (o : Pt X) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (a : Pt X → ℝ) (ha : IntegrableOn a (distBall X.metric.form o r) μ)
    (ha0 : ∀ᵐ x ∂μ.restrict (distBall X.metric.form o r), 0 ≤ a x) :
    (∫⁻ x in distBall X.metric.form o r, ENNReal.ofReal (a x) ∂μ) =
        ENNReal.ofReal (∫ x in distBall X.metric.form o r, a x ∂μ) ∧
      (BallIntegralLE X.metric.form μ o a r B ↔
        (∫ x in distBall X.metric.form o r, a x ∂μ) / (μ (distBall X.metric.form o r)).toReal ≤ B) := by
  have hv := ball_volume_facts X μ hμ o hr
  have hmass : ENNReal.ofReal B * μ (distBall X.metric.form o r) =
      ENNReal.ofReal (B * (μ (distBall X.metric.form o r)).toReal) := by
    rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_toReal hv.2.2.1.ne]
  have hi := ofReal_integral_eq_lintegral_ofReal ha ha0
  refine ⟨hi.symm, ?_⟩
  rw [BallIntegralLE, ← hi, hmass]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB ENNReal.toReal_nonneg)).trans
    (div_le_iff₀ hv.2.2.2).symm

theorem flow_ball_volume_polynomial {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (μ (distBall X.metric.form o L)).toReal ≤ C * L ^ (2 * n) := by
  have hunit := ball_volume_facts X μ hμ o (show (0 : ℝ) < 1 by norm_num)
  refine ⟨(μ (distBall X.metric.form o 1)).toReal, hunit.2.2.2, ?_⟩
  intro L hL
  have hBG := Proofs.F02Aux.flow_initial_volume_comparison X o h U P ρ hloc μ hμ
    (show (0 : ℝ) < 1 by norm_num) hL
  have hfin : ENNReal.ofReal ((L / 1) ^ (2 * n)) * μ (distBall X.metric.form o 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunit.2.2.1.ne
  have hh := ENNReal.toReal_mono hfin hBG
  simp only [div_one, ENNReal.toReal_mul] at hh
  rw [ENNReal.toReal_ofReal (pow_nonneg (show 0 ≤ L by linarith) (2 * n))] at hh
  simpa only [mul_comm] using hh

end Yau.F04Proof
