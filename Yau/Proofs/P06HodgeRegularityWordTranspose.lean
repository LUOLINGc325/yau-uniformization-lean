import Yau.Proofs.P06HodgeRegularitySmoothTranspose
import Yau.Proofs.P06HodgeRegularityWordCalculus

/-! True arbitrary-word integration by parts and linearity, always on
globally smooth fields and compact smooth tests. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem regularityCoefficientWord_append (v : ι → E) (w r : List ι) (u : E → ℝ) :
    regularityCoefficientWord v (w ++ r) u =
      regularityCoefficientWord v w (regularityCoefficientWord v r u) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append,regularityCoefficientWord,ih]

theorem regularityCoefficientWord_const_mul (v : ι → E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) (a : ℝ) (w : List ι) :
    regularityCoefficientWord v w (fun z => a * u z) =
      fun z => a * regularityCoefficientWord v w u z := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change regularityDirection (v i) (regularityCoefficientWord v w (fun z => a * u z)) = _
    rw [ih,regularityDirection_const_mul (regularityCoefficientWord_contDiff v hu w) a (v i)]
    rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure]

theorem regularityCoefficientWord_integral_transpose
    (v : ι → E) (u : E → ℝ) (hu : ContDiff ℝ ∞ u)
    (w : List ι) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ z, regularityCoefficientWord v w u z * φ z ∂ν) =
      (-1 : ℝ)^w.length * ∫ z, u z * regularityCoefficientWord v w.reverse φ z ∂ν := by
  induction w generalizing φ with
  | nil => simp only [regularityCoefficientWord,List.length_nil,List.reverse_nil,pow_zero,one_mul]
  | cons i w ih =>
    have hIBP := Yau.LeafProofs.L03.DivergenceEnergy.compact_ibp ν φ
      (regularityCoefficientWord v w u) hφ hcφ (regularityCoefficientWord_contDiff v hu w) (v i)
    have heq : (∫ z, regularityCoefficientWord v (i::w) u z * φ z ∂ν) =
        -(∫ z, regularityCoefficientWord v w u z * regularityDirection (v i) φ z ∂ν) := by
      have hL : (∫ z, regularityCoefficientWord v (i::w) u z * φ z ∂ν) =
          ∫ z, φ z * fderiv ℝ (regularityCoefficientWord v w u) z (v i) ∂ν :=
        integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
      have hR : (∫ z, regularityCoefficientWord v w u z * regularityDirection (v i) φ z ∂ν) =
          ∫ z, fderiv ℝ φ z (v i) * regularityCoefficientWord v w u z ∂ν :=
        integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
      rw [hL,hR]
      exact hIBP
    have hrev : regularityCoefficientWord v (i::w).reverse φ =
        regularityCoefficientWord v w.reverse (regularityDirection (v i) φ) := by
      rw [List.reverse_cons,regularityCoefficientWord_append]
      rfl
    rw [heq,ih (regularityDirection_contDiff hφ (v i)) (hcφ.fderiv_apply ℝ (v i)),hrev,List.length_cons,pow_succ]
    ring

end Yau.NodeProofs.P06Aux
