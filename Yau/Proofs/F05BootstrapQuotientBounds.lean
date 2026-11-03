import Yau.Proofs.F05BootstrapDefinitions
import Yau.LeafProofs.L16DifferenceQuotient

/-! Uniform difference-quotient estimates from actual one-variable
segment derivatives. The mean-value proof works on closed segments and
needs neither a future-time extension nor a mixed joint derivative. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_segment_quotient_norm {h C : ℝ} (hh : 0 < h)
    {g D : ℝ → V}
    (hDeriv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (h • D t) (Icc 0 1) t)
    (hBound : ∀ t ∈ Ico (0 : ℝ) 1, ‖D t‖ ≤ C) :
    ‖h⁻¹ • (g 1-g 0)‖ ≤ C := by
  have hRaw := norm_image_sub_le_of_norm_deriv_le_segment_01' hDeriv (fun t ht => by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left (hBound t ht) hh.le)
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hh]
  have hScaled := mul_le_mul_of_nonneg_left hRaw (inv_nonneg.mpr hh.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ hh.ne',one_mul] using hScaled

theorem F05_segment_quotient_holder {h α C : ℝ} (hh : 0 < h) (hC : 0 ≤ C)
    {Q : Set (Point n)} {g D : Point n → ℝ → V}
    (hDeriv : ∀ p ∈ Q, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (g p) (h • D p t) (Icc 0 1) t)
    (hBound : ∀ p ∈ Q, ∀ t ∈ Ico (0 : ℝ) 1, ‖D p t‖ ≤ C)
    (hPair : ∀ p ∈ Q, ∀ q ∈ Q, ∀ t ∈ Ico (0 : ℝ) 1,
      ‖D p t-D q t‖ ≤ C*holderWeight α p q) :
    HolderBound α Q (fun p => h⁻¹ • (g p 1-g p 0)) C := by
  refine ⟨hC,fun p hp => F05_segment_quotient_norm hh (hDeriv p hp) (hBound p hp),?_⟩
  intro p hp q hq
  have hDerivative : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun a => g p a-g q a) (h • (D p t-D q t)) (Icc 0 1) t := by
    intro t ht
    have hRaw := (hDeriv p hp t ht).sub (hDeriv q hq t ht)
    change HasDerivWithinAt (fun a => g p a-g q a) (h • D p t-h • D q t) (Icc 0 1) t at hRaw
    rwa [← smul_sub] at hRaw
  have h := F05_segment_quotient_norm hh hDerivative (hPair p hp q hq)
  convert h using 1
  congr 1
  simp only [← smul_sub]
  congr 1
  abel

theorem F05_segment_quotient_remainder {h E : ℝ} (hh : 0 < h)
    {g D : ℝ → V}
    (hDeriv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (h • D t) (Icc 0 1) t)
    (hBound : ∀ t ∈ Ico (0 : ℝ) 1, ‖D t-D 0‖ ≤ E) :
    ‖h⁻¹ • (g 1-g 0)-D 0‖ ≤ E := by
  have hDerivative : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun a => g a-a • (h • D 0))
        (h • (D t-D 0)) (Icc 0 1) t := by
    intro t ht
    have hLinear := ((hasDerivAt_id t).smul_const (h • D 0)).hasDerivWithinAt (s := Icc 0 1)
    have hRaw := (hDeriv t ht).sub hLinear
    simp only [one_smul] at hRaw
    change HasDerivWithinAt (fun a => g a-a • (h • D 0)) (h • D t-h • D 0) (Icc 0 1) t at hRaw
    rwa [← smul_sub] at hRaw
  have hEstimate := F05_segment_quotient_norm hh hDerivative hBound
  have hEq : h⁻¹ • ((g 1-(1 : ℝ) • (h • D 0))-(g 0-(0 : ℝ) • (h • D 0))) =
      h⁻¹ • (g 1-g 0)-D 0 := by
    simp only [one_smul,zero_smul,sub_zero,smul_sub,smul_smul,one_mul,zero_mul,smul_zero,inv_mul_cancel₀ hh.ne',one_smul]
    abel
  exact hEq ▸ hEstimate

end Yau.Proofs.F05Aux
