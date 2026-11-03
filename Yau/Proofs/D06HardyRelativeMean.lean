import Yau.Proofs.D06BoundaryFactorizationAE
import Yau.Proofs.D06HardyRotation

/-! The relative factor has mean I for the original L² traces, before the
first W¹ estimate and without assuming closed-disc continuity. -/

open scoped ComplexOrder Matrix
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyMatrix_relative_entry_integrable (a b : Fin r → HardySeq r)
    (θ : HardyCircle) (i j : Fin r) :
    Integrable (fun t => (hardyMatrixTrace a (t + θ) * hardyMatrixTrace b t) i j)
      hardyCircleMeasure := by
  change Integrable (fun t => ∑ k : Fin r, hardyTraceLp (a k) i (t + θ) *
    hardyTraceLp (b j) k t) hardyCircleMeasure
  apply integrable_finsetSum _
  intro k _
  have ha : MemLp (fun t => hardyTraceLp (a k) i (t + θ)) 2 hardyCircleMeasure :=
    (Lp.memLp (hardyTraceLp (a k) i)).comp_measurePreserving
      (measurePreserving_add_right hardyCircleMeasure θ)
  exact memLp_one_iff_integrable.mp (ha.fun_mul (Lp.memLp (hardyTraceLp (b j) k)))

theorem hardyMatrix_relative_entry_mean (a b : Fin r → HardySeq r)
    (θ : HardyCircle) (i j : Fin r) :
    (∫ t, (hardyMatrixTrace a (t + θ) * hardyMatrixTrace b t) i j ∂hardyCircleMeasure) =
      (hardyMatrixInterior a 0 * hardyMatrixInterior b 0) i j := by
  change (∫ t, ∑ k : Fin r, hardyTraceLp (a k) i (t + θ) * hardyTraceLp (b j) k t
    ∂hardyCircleMeasure) = _
  have hinter (k : Fin r) : Integrable
      (fun t => hardyTraceLp (a k) i (t + θ) * hardyTraceLp (b j) k t) hardyCircleMeasure := by
    have ha : MemLp (fun t => hardyTraceLp (a k) i (t + θ)) 2 hardyCircleMeasure :=
      (Lp.memLp (hardyTraceLp (a k) i)).comp_measurePreserving
        (measurePreserving_add_right hardyCircleMeasure θ)
    exact memLp_one_iff_integrable.mp (ha.fun_mul (Lp.memLp (hardyTraceLp (b j) k)))
  rw [integral_finsetSum _ (fun k _ => hinter k)]
  simp only [hardyTrace_rotated_product_mean, Matrix.mul_apply, hardyMatrixInterior, hardyEvalEntry_zero]

variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)
variable (M : ℝ) (hM : 0 ≤ M)
variable (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef)

def hardyRelativeTrace (θ : HardyCircle) (t : HardyCircle) : Matrix (Fin r) (Fin r) ℂ :=
  hardyQTrace L hLp hHerm m hm hLower M hM hUpper (t + θ) *
    hardyPTrace L hLp hHerm m hm hLower M hM hUpper t

theorem hardyRelativeTrace_entry_mean (θ : HardyCircle) (i j : Fin r) :
    (∫ t, hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t i j
      ∂hardyCircleMeasure) = (1 : Matrix (Fin r) (Fin r) ℂ) i j := by
  have h := hardyMatrix_relative_entry_mean
    (hardyQColumns L hLp hHerm m hm hLower M hM hUpper)
    (hardyPColumns L hLp hHerm m hm hLower M hM hUpper) θ i j
  exact h.trans (congrArg (fun A : Matrix (Fin r) (Fin r) ℂ => A i j)
    (hardyQ_mul_P L hLp hHerm m hm hLower M hM hUpper 0 (by simp)))

theorem hardyRelativeTrace_realTrace_mean (θ : HardyCircle) :
    (∫ t, (Matrix.trace (hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t)).re
      ∂hardyCircleMeasure) = r := by
  have hinter (i : Fin r) : Integrable
      (fun t => hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t i i)
      hardyCircleMeasure := hardyMatrix_relative_entry_integrable _ _ θ i i
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  rw [integral_finsetSum _ (fun i _ => by
    simpa only [RCLike.re_to_complex] using (hinter i).re)]
  have hreal (i : Fin r) : (∫ t,
      (hardyRelativeTrace L hLp hHerm m hm hLower M hM hUpper θ t i i).re
      ∂hardyCircleMeasure) = 1 := by
    have h := integral_re (hinter i)
    rw [hardyRelativeTrace_entry_mean] at h
    simpa only [RCLike.re_to_complex, Matrix.one_apply_eq, Complex.one_re] using h
  simp only [hreal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end Yau.NodeProofs.D06Aux
