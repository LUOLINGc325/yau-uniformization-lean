import Yau.Proofs.D06HardyProductMean
import Yau.Proofs.D06HardyRadialTrace

/-! Circle translation is actual coefficient rotation, including the Hardy
product mean before any closed-disc regularity is available. -/

open scoped ComplexConjugate
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardy_fourier_argument_add (n : ℤ) (t θ : HardyCircle) :
    fourier n (t + θ) = fourier n t * fourier n θ := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem hardy_fourierCoeff_translate (f : HardyCircle → ℂ) (θ : HardyCircle) (n : ℤ) :
    fourierCoeff (fun t => f (t + θ)) n = fourier n θ * fourierCoeff f n := by
  unfold fourierCoeff
  simp only [smul_eq_mul]
  calc
    _ = ∫ t, fourier n θ * (fourier (-n) (t + θ) * f (t + θ)) ∂hardyCircleMeasure := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hardy_fourier_argument_add]
      have hc : fourier n θ * fourier (-n) θ = 1 := by
        rw [← fourier_add, add_neg_cancel, fourier_zero]
      calc
        _ = (fourier n θ * fourier (-n) θ) * (fourier (-n) t * f (t + θ)) := by rw [hc, one_mul]
        _ = _ := by ring
    _ = ∫ t, fourier n θ * (fourier (-n) t * f t) ∂hardyCircleMeasure :=
      integral_add_right_eq_self (μ := hardyCircleMeasure)
        (fun t : HardyCircle => fourier n θ * (fourier (-n) t * f t)) θ
    _ = _ := integral_const_mul _ _

theorem hardyTrace_rotation_ae (a : HardySeq r) (i : Fin r) (θ : HardyCircle) :
    (fun t => hardyTraceLp (hardyDilate (fourier 1 θ)
      (by simp only [fourier_apply, Circle.norm_coe, le_refl]) a) i t) =ᵐ[hardyCircleMeasure]
      fun t => hardyTraceLp a i (t + θ) := by
  apply hardy_fourierCoeff_unique
  · exact Lp.memLp _
  · exact (Lp.memLp (hardyTraceLp a i)).comp_measurePreserving
      (measurePreserving_add_right hardyCircleMeasure θ)
  · intro n
    rw [hardyTrace_fourierCoeff, hardy_fourierCoeff_translate, hardyTrace_fourierCoeff]
    by_cases hn : 0 ≤ n
    · rw [ite_eq_left hn, ite_eq_left hn, hardyDilate_apply]
      rw [← hardy_fourier_nat, Int.toNat_of_nonneg hn]
    · rw [ite_eq_right hn, ite_eq_right hn, mul_zero]

theorem hardyTrace_rotated_product_mean (a b : HardySeq r) (i j : Fin r) (θ : HardyCircle) :
    (∫ t, hardyTraceLp a i (t + θ) * hardyTraceLp b j t ∂hardyCircleMeasure) =
      a (0, i) * b (0, j) := by
  let aθ := hardyDilate (fourier 1 θ)
    (by simp only [fourier_apply, Circle.norm_coe, le_refl]) a
  have heq : (∫ t, hardyTraceLp a i (t + θ) * hardyTraceLp b j t ∂hardyCircleMeasure) =
      ∫ t, hardyTraceLp aθ i t * hardyTraceLp b j t ∂hardyCircleMeasure := by
    apply integral_congr_ae
    filter_upwards [hardyTrace_rotation_ae a i θ] with t ht
    rw [ht]
  rw [heq, hardyTrace_product_mean]
  simp only [aθ, hardyDilate_apply, pow_zero, one_mul]

end Yau.NodeProofs.D06Aux
