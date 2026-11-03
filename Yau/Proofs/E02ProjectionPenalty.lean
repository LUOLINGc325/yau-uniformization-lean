import Yau.Proofs.E02MatrixBasic

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

theorem gram_trace_re_eq_sum_norm_sq {n m : ℕ} (A : Rect n m) :
    (Matrix.trace (Aᴴ*A)).re = ∑ i, ∑ j, ‖A i j‖^2 := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Complex.re_sum,Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    Complex.sq_norm,Complex.normSq_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The real trace of the actual Gram matrix vanishes only at zero. -/
theorem gram_trace_re_zero_iff {n m : ℕ} (A : Rect n m) :
    (Matrix.trace (Aᴴ*A)).re = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hPos := Matrix.posSemidef_conjTranspose_mul_self A
    have hIm := (RCLike.nonneg_iff.mp hPos.trace_nonneg).2
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    exact Complex.ext h hIm
  · rintro rfl
    simp

/-- The penalty is half the real Gram trace of the difference of the
two genuine orthogonal projectors. No Grassmannian metric is assumed. -/
theorem projectorPenalty_eq_half_gram {n m : ℕ} (M₀ M : Rect n m)
    (hM₀ : (M₀*M₀ᴴ).PosDef) (hM : (M*Mᴴ).PosDef) :
    projectorPenalty (rowProjector M₀) M =
      (Matrix.trace ((rowProjector M-rowProjector M₀)ᴴ*
        (rowProjector M-rowProjector M₀))).re/2 := by
  let P := rowProjector M
  let P₀ := rowProjector M₀
  have hP : P.IsHermitian := rowProjector_isHermitian M hM
  have hP₀ : P₀.IsHermitian := rowProjector_isHermitian M₀ hM₀
  have hPP : P*P = P := rowProjector_idempotent M hM
  have hP₀P₀ : P₀*P₀ = P₀ := rowProjector_idempotent M₀ hM₀
  have hExpand : (P-P₀)ᴴ*(P-P₀) = P-P*P₀-P₀*P+P₀ := by
    rw [Matrix.conjTranspose_sub,hP.eq,hP₀.eq]
    calc
      (P-P₀)*(P-P₀) = P*P-P*P₀-P₀*P+P₀*P₀ := by noncomm_ring
      _ = _ := by rw [hPP,hP₀P₀]
  have htP : (Matrix.trace P).re = n := trace_rowProjector M hM
  have htP₀ : (Matrix.trace P₀).re = n := trace_rowProjector M₀ hM₀
  have htComm : Matrix.trace (P*P₀) = Matrix.trace (P₀*P) := Matrix.trace_mul_comm _ _
  change (n:ℝ)-(Matrix.trace (P₀*P)).re = (Matrix.trace ((P-P₀)ᴴ*(P-P₀))).re/2
  rw [hExpand]
  simp only [Matrix.trace_add,Matrix.trace_sub,Complex.add_re,Complex.sub_re,htP,htP₀,htComm]
  ring

theorem projectorPenalty_nonneg_eq_zero {n m : ℕ} (M₀ M : Rect n m)
    (hM₀ : (M₀*M₀ᴴ).PosDef) (hM : (M*Mᴴ).PosDef) :
    0 ≤ projectorPenalty (rowProjector M₀) M ∧
    (projectorPenalty (rowProjector M₀) M = 0 ↔ rowProjector M = rowProjector M₀) := by
  rw [projectorPenalty_eq_half_gram M₀ M hM₀ hM]
  constructor
  · exact div_nonneg (RCLike.nonneg_iff.mp
      (Matrix.posSemidef_conjTranspose_mul_self (rowProjector M-rowProjector M₀)).trace_nonneg).1
      (by norm_num)
  · rw [div_eq_zero_iff]
    simp only [OfNat.ofNat_ne_zero,or_false,gram_trace_re_zero_iff,sub_eq_zero]

theorem projectorPenalty_eq_half_sum_norm_sq {n m : ℕ} (M₀ M : Rect n m)
    (hM₀ : (M₀*M₀ᴴ).PosDef) (hM : (M*Mᴴ).PosDef) :
    projectorPenalty (rowProjector M₀) M =
      (∑ i, ∑ j, ‖(rowProjector M-rowProjector M₀) i j‖^2)/2 := by
  rw [projectorPenalty_eq_half_gram M₀ M hM₀ hM,gram_trace_re_eq_sum_norm_sq]

end Yau.NodeProofs.E02Aux
