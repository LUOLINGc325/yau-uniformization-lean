import Yau.Proofs.C03ScalarCoefficients
import Yau.Proofs.C03SheetExtension

/-! A genuine compact target seed, with its exact holomorphic germ and
a bound depending only on the target covector and the fixed radius. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L14Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def seedCutoff (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : ComplexVector n) :=
  ⟨δ / 2, δ, by positivity, by linarith⟩

def targetSeed (δ : ℝ) (hδ : 0 < δ) (η : Covector n) (w : ComplexVector n) : ℂ :=
  ((seedCutoff δ hδ w : ℝ) : ℂ) * η w

theorem targetSeed_contDiff (δ : ℝ) (hδ : 0 < δ) (η : Covector n) :
    ContDiff ℝ ∞ (targetSeed δ hδ η) :=
  (Complex.ofRealCLM.contDiff.comp (seedCutoff δ hδ).contDiff).mul
    (η.contDiff.restrict_scalars ℝ)

theorem targetSeed_tsupport_subset (δ : ℝ) (hδ : 0 < δ) (η : Covector n) :
    tsupport (targetSeed δ hδ η) ⊆ closedBall (0 : ComplexVector n) δ := by
  apply closure_minimal _ isClosed_closedBall
  intro w hw
  have hne : seedCutoff δ hδ w ≠ 0 := by
    intro he
    exact hw (by simp only [targetSeed, he, Complex.ofReal_zero, zero_mul])
  have hw' : w ∈ Function.support (seedCutoff δ hδ) := hne
  rw [(seedCutoff δ hδ).support_eq] at hw'
  exact ball_subset_closedBall hw'

theorem targetSeed_hasCompactSupport (δ : ℝ) (hδ : 0 < δ) (η : Covector n) :
    HasCompactSupport (targetSeed δ hδ η) :=
  (isCompact_closedBall (0 : ComplexVector n) δ).of_isClosed_subset
    (isClosed_tsupport _) (targetSeed_tsupport_subset δ hδ η)

theorem targetSeed_eq_on_inner (δ : ℝ) (hδ : 0 < δ) (η : Covector n)
    {w : ComplexVector n} (hw : w ∈ closedBall (0 : ComplexVector n) (δ / 2)) :
    targetSeed δ hδ η w = η w := by
  simp only [targetSeed, (seedCutoff δ hδ).one_of_mem_closedBall hw,
    Complex.ofReal_one, one_mul]

theorem targetSeed_germ (δ : ℝ) (hδ : 0 < δ) (η : Covector n) :
    targetSeed δ hδ η =ᶠ[𝓝 (0 : ComplexVector n)] η := by
  filter_upwards [(seedCutoff δ hδ).eventuallyEq_one] with w hw
  simp only [targetSeed, hw, Pi.one_apply, Complex.ofReal_one, one_mul]

theorem targetSeed_norm_le (δ : ℝ) (hδ : 0 < δ) (η : Covector n)
    (w : ComplexVector n) : ‖targetSeed δ hδ η w‖ ≤ ‖η‖ * δ := by
  by_cases hw : w ∈ closedBall (0 : ComplexVector n) δ
  · have hn : ‖w‖ ≤ δ := by simpa only [mem_closedBall, dist_zero_right] using hw
    calc
      ‖targetSeed δ hδ η w‖ = seedCutoff δ hδ w * ‖η w‖ := by
        rw [targetSeed, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (seedCutoff δ hδ).nonneg]
      _ ≤ ‖η w‖ := mul_le_of_le_one_left (norm_nonneg _) (seedCutoff δ hδ).le_one
      _ ≤ ‖η‖ * δ := (η.le_opNorm w).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg η))
  · have he : targetSeed δ hδ η w = 0 := by
      apply notMem_tsupport_iff_eventuallyEq.mp
        (fun H => hw (targetSeed_tsupport_subset δ hδ η H)) |>.eq_of_nhds
    rw [he, norm_zero]
    positivity

theorem translatedTargetSeed_contDiff (δ : ℝ) (hδ : 0 < δ) (η : Covector n)
    (w0 : ComplexVector n) :
    ContDiff ℝ ∞ (fun w => targetSeed δ hδ η (w - w0)) :=
  (targetSeed_contDiff δ hδ η).comp (contDiff_id.sub contDiff_const)

theorem translatedTargetSeed_tsupport_subset (δ : ℝ) (hδ : 0 < δ) (η : Covector n)
    (w0 : ComplexVector n) :
    tsupport (fun w => targetSeed δ hδ η (w - w0)) ⊆ closedBall w0 δ := by
  apply closure_minimal _ isClosed_closedBall
  intro w hw
  have H := targetSeed_tsupport_subset δ hδ η
    (subset_closure (show w - w0 ∈ Function.support (targetSeed δ hδ η) from hw))
  simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using H

theorem translatedTargetSeed_hasCompactSupport (δ : ℝ) (hδ : 0 < δ) (η : Covector n)
    (w0 : ComplexVector n) :
    HasCompactSupport (fun w => targetSeed δ hδ η (w - w0)) :=
  (isCompact_closedBall w0 δ).of_isClosed_subset (isClosed_tsupport _)
    (translatedTargetSeed_tsupport_subset δ hδ η w0)

end Yau.Proofs.C03Aux
