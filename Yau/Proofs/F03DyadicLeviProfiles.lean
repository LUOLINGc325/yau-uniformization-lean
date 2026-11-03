import Yau.Proofs.F03LeviGradientBounds
import Yau.Proofs.F03DyadicScaleEstimates

/-! The actual dyadic profiles have uniform physical-gradient and two-sided Levi bounds at the exhaustion scale. -/
noncomputable section
open scoped ComplexOrder ContDiff
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L18Aux
variable {n : ℕ}

theorem controlledExhaustion_dyadic_profile_bounds
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ C : ℝ,0 < C ∧ ∀ j : ℕ,∀ x,
      Real.sqrt (gradNormSq X.metric.form (fun y => dyadicPartition j (u y)) x) ≤ C/u x ∧
      HermAbsLE (levi (fun y => dyadicPartition j (u y)) x) (gMat X.metric.form x) (C/(u x)^2) := by
  obtain ⟨Q,hQ,hU⟩ := hu.2.2.2
  obtain ⟨B,hB,hProfile⟩ := dyadicPartition_derivative_bounds
  let C := 1+2*B*Q+4*B*Q^2
  have hC : 0 < C := by dsimp [C];positivity
  refine ⟨C,hC,fun j x => ?_⟩
  have hu1 := hu.2.2.1 x
  have huPos : 0 < u x := zero_lt_one.trans_le hu1
  have hUSqrt : Real.sqrt (gradNormSq X.metric.form u x) ≤ Q :=
    Real.sqrt_le_iff.mpr ⟨hQ.le,(hU x).2.2.1⟩
  have hUAbs : HermAbsLE (levi u x) (gMat X.metric.form x) (Q/u x) := by
    constructor
    · simpa only [Complex.ofReal_neg,Complex.ofReal_div] using (hU x).2.2.2.1
    · exact (hU x).2.2.2.2
  have hDerivs := dyadicScale_derivative_at_value hB.le hu1 j (hProfile j (u x)).1 (hProfile j (u x)).2
  constructor
  · rw [sqrt_gradNormSq_scalar_comp X.metric.form hu.1 (dyadicPartition j) (dyadicPartition_contDiff j) x]
    calc
      _ ≤ (2*B/u x)*Q := mul_le_mul hDerivs.1 hUSqrt (Real.sqrt_nonneg _) (by positivity)
      _ = (2*B*Q)/u x := by ring
      _ ≤ C/u x := div_le_div_of_nonneg_right
        (by dsimp [C];nlinarith [mul_nonneg hB.le (sq_nonneg Q)]) huPos.le
  · have hComp := levi_scalar_comp_abs_bound X.metric.form hu.1 (dyadicPartition j)
      (dyadicPartition_contDiff j) x hUAbs hUSqrt
    apply hermAbsLE_mono (hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)).posSemidef hComp
    calc
      _ ≤ (2*B/u x)*(Q/u x)+(4*B/(u x)^2)*Q^2 := add_le_add
        (mul_le_mul_of_nonneg_right hDerivs.1 (by positivity))
        (mul_le_mul_of_nonneg_right hDerivs.2 (sq_nonneg _))
      _ = (2*B*Q+4*B*Q^2)/(u x)^2 := by field_simp <;> ring
      _ ≤ C/(u x)^2 := div_le_div_of_nonneg_right (by dsimp [C];linarith) (sq_nonneg _)

end Yau.Proofs.F03Aux
