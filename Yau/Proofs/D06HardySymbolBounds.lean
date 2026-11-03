import Yau.Proofs.D06HardyMultiplier

/-! Exact matrix-symbol bounds and multiplicativity, using the same kernel and
constant columns as the weighted wandering-basis construction. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint
variable {r : ℕ}

theorem hardySymbol_differentiableOn (T : HardySeq r →L[ℂ] HardySeq r) (i j : Fin r) :
    DifferentiableOn ℂ (fun z => hardySymbol T z i j) (Metric.ball 0 1) :=
  hardyEvalEntry_differentiableOn _ _

theorem hardySymbol_bound (T : HardySeq r →L[ℂ] HardySeq r)
    (hT : ∀ a, T (hardyShift a) = hardyShift (T a)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ a, ‖T a‖ ≤ C * ‖a‖) (z : ℂ) (hz : ‖z‖ < 1) :
    matOpNormR (hardySymbol T z) ≤ C := by
  have hq : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hs : 0 < Real.sqrt (1 - ‖z‖ ^ 2) := Real.sqrt_pos.mpr hq
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  have he := hardyEval_norm_le (T (hardyNormalizedKernel z hz v)) z hz
  rw [hardySymbol_multiplier T hT z hz, hardyEval_normalizedKernel] at he
  calc
    ‖Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (hardySymbol T z) v‖ ≤
        (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ * ‖T (hardyNormalizedKernel z hz v)‖ := he
    _ ≤ (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ * (C * ‖hardyNormalizedKernel z hz v‖) :=
      mul_le_mul_of_nonneg_left (hbound _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = C * ‖v‖ := by
      rw [hardyNormalizedKernel_norm]
      field_simp

theorem hardySymbol_comp (T R : HardySeq r →L[ℂ] HardySeq r)
    (hT : ∀ a, T (hardyShift a) = hardyShift (T a)) (z : ℂ) (hz : ‖z‖ < 1) :
    hardySymbol (T.comp R) z = hardySymbol T z * hardySymbol R z := by
  apply (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ)).injective
  rw [map_mul]
  apply ContinuousLinearMap.ext
  intro v
  change Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (hardySymbol (T.comp R) z) v =
    Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (hardySymbol T z)
      (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (hardySymbol R z) v)
  calc
    _ = hardyEval (T (R (hardyConst v))) z := hardySymbol_const _ z hz v
    _ = Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (hardySymbol T z)
        (hardyEval (R (hardyConst v)) z) := hardySymbol_multiplier T hT z hz _
    _ = _ := congrArg (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (hardySymbol T z))
      (hardySymbol_const R z hz v).symm

theorem hardySymbol_id (z : ℂ) :
    hardySymbol (ContinuousLinearMap.id ℂ (HardySeq r)) z = 1 := by
  ext i j
  change hardyEvalEntry (hardyConst (EuclideanSpace.single j 1)) i z = (1 : Matrix (Fin r) (Fin r) ℂ) i j
  have h := congrArg (fun v : EuclideanSpace ℂ (Fin r) => v i)
    (hardyEval_const (EuclideanSpace.single j 1) z)
  simpa only [hardyEval, PiLp.single_apply, Pi.single_apply, Matrix.one_apply, eq_comm] using h

end Yau.NodeProofs.D06Aux
