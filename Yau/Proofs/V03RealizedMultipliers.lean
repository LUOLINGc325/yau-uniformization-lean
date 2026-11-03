import Yau.Proofs.V03OuterPhase

/-! The original realization's scalar multipliers have uniform supremum
and half-order bounds from the actual log-wall energy and alpha loss. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem logSummand_le_variationEnergy (d : VariationData X q) (j : ℕ) (F : VariationDisc X) :
    scalarDSq (logTrace d j F.f) ≤ variationEnergy d j F := by
  unfold variationEnergy
  exact le_add_left le_rfl

theorem realized_h_boundaryDSq_le_energy (d : VariationData X q) (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) :
    boundaryDSq (fun θ (_ : Unit) => h (circlePoint θ)) ≤
      ENNReal.ofReal (4 * (a : ℝ) ^ 2) * variationEnergy d j F :=
  (realized_h_boundaryDSq_le d hd j a F hF E l h α fz R hR).trans
    (mul_le_mul_right (logSummand_le_variationEnergy d j F) _)

theorem realized_normalized_multiplier_norm_le (d : VariationData X q) (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) (θ : ℝ) :
    ‖α (circlePoint θ) *
      (h (circlePoint θ) / (wallPower d j a (F.f (circlePoint θ)) : ℂ))‖ ≤ 1 := by
  rw [realized_h_normalized_phase d hd j a F hF E l h α fz R hR θ, norm_mul,
    circlePoint_norm, mul_one]
  exact hR.2.2.2.2.2.2.2.2.1 _ (circlePoint_mem_closedBall θ)

theorem realized_normalized_multiplier_boundaryDSq_le (d : VariationData X q) (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) :
    boundaryDSq (fun θ (_ : Unit) => α (circlePoint θ) *
      (h (circlePoint θ) / (wallPower d j a (F.f (circlePoint θ)) : ℂ))) ≤
      ENNReal.ofReal 2 * (1 + ENNReal.ofReal ((a : ℝ) ^ 2) * variationEnergy d j F) := by
  simp_rw [realized_h_normalized_phase d hd j a F hF E l h α fz R hR]
  have hq := admissible_logTrace_contDiff hd hF
  have hp := logTrace_periodic d j F
  have hαcont := (closedDisc_trace_contDiff hR.2.2.2.2.1).continuous
  have hphasecont : Continuous (fun θ =>
      circlePoint ((a : ℝ) * harmonicConjugateTrace (logTrace d j F.f) θ)) :=
    circlePoint_contDiff.continuous.comp
      (continuous_const.mul (harmonicConjugateTrace_contDiff hq hp).continuous)
  have hphasep : Function.Periodic (fun θ =>
      circlePoint ((a : ℝ) * harmonicConjugateTrace (logTrace d j F.f) θ)) (2 * Real.pi) :=
    fun θ => congrArg (fun t => circlePoint ((a : ℝ) * t))
      (harmonicConjugateTrace_periodic (logTrace d j F.f) θ)
  have hb := boundaryDSq_mul_le hαcont hphasecont (circleTrace_periodic α) hphasep
    (M := 1) (N := 1) (by norm_num) (by norm_num)
    (fun θ => hR.2.2.2.2.2.2.2.2.1 _ (circlePoint_mem_closedBall θ))
    (fun θ => (circlePoint_norm _).le)
  have hphase := (outer_phase_boundaryDSq_le hq hp a).trans
    (mul_le_mul_right (logSummand_le_variationEnergy d j F) _)
  simp only [one_pow, mul_one] at hb
  calc
    _ ≤ ENNReal.ofReal 2 * 1 + ENNReal.ofReal 2 *
        (ENNReal.ofReal ((a : ℝ) ^ 2) * variationEnergy d j F) :=
      hb.trans (add_le_add (mul_le_mul_right hR.2.2.2.2.2.2.2.2.2 _)
        (mul_le_mul_right hphase _))
    _ = _ := by ring

end Yau.Blueprint.V03Proof
