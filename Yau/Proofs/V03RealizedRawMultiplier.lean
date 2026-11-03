import Yau.Proofs.V03RealizedMultipliers

/-! The actual unnormalized scalar multiplier αh has its supremum and
half-order bounds from the original realization and full log-wall energy. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem realized_raw_multiplier_norm_le (d : VariationData X q) (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) (θ : ℝ) :
    ‖α (circlePoint θ) * h (circlePoint θ)‖ ≤ 1 := by
  rw [norm_mul]
  have hα := hR.2.2.2.2.2.2.2.2.1 _ (circlePoint_mem_closedBall θ)
  have hh := realized_h_norm_le_one d hd j a F hF E l h α fz R hR _ (circlePoint_mem_closedBall θ)
  simpa only [one_mul] using mul_le_mul hα hh (norm_nonneg _) (by norm_num)

theorem realized_raw_multiplier_boundaryDSq_le (d : VariationData X q) (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) :
    boundaryDSq (fun θ (_ : Unit) => α (circlePoint θ) * h (circlePoint θ)) ≤
      ENNReal.ofReal 2 * (1 + ENNReal.ofReal (4 * (a : ℝ) ^ 2) * variationEnergy d j F) := by
  have hαc := (closedDisc_trace_contDiff hR.2.2.2.2.1).continuous
  have hhc := (closedDisc_trace_contDiff hR.2.2.2.1).continuous
  have hb := boundaryDSq_mul_le hαc hhc (circleTrace_periodic α) (circleTrace_periodic h)
    (M := 1) (N := 1) (by norm_num) (by norm_num)
    (fun θ => hR.2.2.2.2.2.2.2.2.1 _ (circlePoint_mem_closedBall θ))
    (fun θ => realized_h_norm_le_one d hd j a F hF E l h α fz R hR _ (circlePoint_mem_closedBall θ))
  simp only [one_pow, mul_one] at hb
  have hh := realized_h_boundaryDSq_le_energy d hd j a F hF E l h α fz R hR
  calc
    _ ≤ ENNReal.ofReal 2 * 1 + ENNReal.ofReal 2 *
        (ENNReal.ofReal (4 * (a : ℝ) ^ 2) * variationEnergy d j F) := by
      apply hb.trans
      gcongr
      · exact hR.2.2.2.2.2.2.2.2.2
    _ = _ := by ring

end Yau.Blueprint.V03Proof
