import Yau.Proofs.D06QuadraticBounds
import Yau.Proofs.D06HardyParseval

/-! Hermitian symmetry and the two exact norm-equivalence bounds of the
weighted Hardy integral. -/

open scoped Matrix ComplexConjugate ComplexOrder
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyWeightedInner_star (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ t, (L t).IsHermitian) (a b : HardySeq r) :
    star (hardyWeightedInner L a b) = hardyWeightedInner L b a := by
  unfold hardyWeightedInner
  simp only [Complex.star_def, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  have hLij := (hL t).apply i j
  simp only [Complex.star_def] at hLij
  simp only [map_mul, Complex.conj_conj, hLij]
  ring

theorem hardyTrace_entry_norm_sq_integrable (a : HardySeq r) (j : Fin r) :
    Integrable (fun t => ‖hardyTraceLp a j t‖ ^ 2) hardyCircleMeasure :=
  (Lp.memLp (hardyTraceLp a j)).integrable_norm_pow (by decide : 2 ≠ 0)

theorem hardyTraceVec_norm_sq_integrable (a : HardySeq r) :
    Integrable (fun t => ‖hardyTraceVec a t‖ ^ 2) hardyCircleMeasure := by
  have h : Integrable (fun t => ∑ j : Fin r, ‖hardyTraceLp a j t‖ ^ 2)
      hardyCircleMeasure := integrable_finsetSum _ fun j _ => hardyTrace_entry_norm_sq_integrable a j
  simpa only [hardyTraceVec, EuclideanSpace.norm_sq_eq] using h

theorem hardyTraceVec_integral_norm_sq (a : HardySeq r) :
    (∫ t, ‖hardyTraceVec a t‖ ^ 2 ∂hardyCircleMeasure) = ‖a‖ ^ 2 := by
  simp only [hardyTraceVec, EuclideanSpace.norm_sq_eq]
  rw [integral_finsetSum _ (fun j _ => hardyTrace_entry_norm_sq_integrable a j)]
  exact hardyTrace_norm_sq a

theorem hardyWeightedInner_lower
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure) (m : ℝ)
    (hL : ∀ t, (L t - (m : ℂ) • 1).PosSemidef) (a : HardySeq r) :
    m * ‖a‖ ^ 2 ≤ (hardyWeightedInner L a a).re := by
  have hpoint := hardyWeightedPoint_integrable L hLp a a
  have hre : Integrable (fun t => (hardyWeightedPoint L a a t).re) hardyCircleMeasure := by
    simpa only [RCLike.re_to_complex] using hpoint.re
  calc
    _ = ∫ t, m * ‖hardyTraceVec a t‖ ^ 2 ∂hardyCircleMeasure := by
      rw [integral_const_mul, hardyTraceVec_integral_norm_sq]
    _ ≤ ∫ t, (hardyWeightedPoint L a a t).re ∂hardyCircleMeasure :=
      integral_mono ((hardyTraceVec_norm_sq_integrable a).const_mul m) hre
        (hardyWeightedPoint_lower L m hL a)
    _ = _ := by
      rw [hardyWeightedInner_eq_integral L hLp a a]
      simpa only [RCLike.re_to_complex] using integral_re hpoint

theorem hardyWeightedInner_upper
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure) (M : ℝ)
    (hL : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef) (a : HardySeq r) :
    (hardyWeightedInner L a a).re ≤ M * ‖a‖ ^ 2 := by
  have hpoint := hardyWeightedPoint_integrable L hLp a a
  have hre : Integrable (fun t => (hardyWeightedPoint L a a t).re) hardyCircleMeasure := by
    simpa only [RCLike.re_to_complex] using hpoint.re
  calc
    _ = ∫ t, (hardyWeightedPoint L a a t).re ∂hardyCircleMeasure := by
      rw [hardyWeightedInner_eq_integral L hLp a a]
      simpa only [RCLike.re_to_complex] using (integral_re hpoint).symm
    _ ≤ ∫ t, M * ‖hardyTraceVec a t‖ ^ 2 ∂hardyCircleMeasure :=
      integral_mono hre ((hardyTraceVec_norm_sq_integrable a).const_mul M)
        (hardyWeightedPoint_upper L M hL a)
    _ = _ := by rw [integral_const_mul, hardyTraceVec_integral_norm_sq]

end Yau.NodeProofs.D06Aux
