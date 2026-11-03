import Yau.Proofs.D06WeightedIntegral

/-! Exact quadratic spectral bounds and their Hardy trace specialization. -/

open scoped Matrix ComplexOrder
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem euclidean_star_dot_re (v : EuclideanSpace ℂ (Fin r)) :
    (star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v).re = ‖v‖ ^ 2 := by
  have heq : inner ℂ v v = star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [← heq, ← RCLike.re_to_complex, inner_self_eq_norm_sq]

theorem matrix_quadratic_lower (A : Matrix (Fin r) (Fin r) ℂ) (m : ℝ)
    (hA : (A - (m : ℂ) • 1).PosSemidef) (v : EuclideanSpace ℂ (Fin r)) :
    m * ‖v‖ ^ 2 ≤ (star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)).re := by
  have h := (RCLike.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg (WithLp.ofLp v))).1
  rw [RCLike.re_to_complex] at h
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul,
    euclidean_star_dot_re] at h
  exact sub_nonneg.mp h

theorem matrix_quadratic_upper (A : Matrix (Fin r) (Fin r) ℂ) (M : ℝ)
    (hA : ((M : ℂ) • 1 - A).PosSemidef) (v : EuclideanSpace ℂ (Fin r)) :
    (star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)).re ≤ M * ‖v‖ ^ 2 := by
  have h := (RCLike.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg (WithLp.ofLp v))).1
  rw [RCLike.re_to_complex] at h
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul,
    euclidean_star_dot_re] at h
  exact sub_nonneg.mp h

def hardyTraceVec (a : HardySeq r) (t : HardyCircle) : EuclideanSpace ℂ (Fin r) :=
  WithLp.toLp 2 (fun j => hardyTraceLp a j t)

theorem hardyWeightedPoint_eq_quadratic
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (a : HardySeq r) (t : HardyCircle) :
    hardyWeightedPoint L a a t =
      star (WithLp.ofLp (hardyTraceVec a t)) ⬝ᵥ
        (L t *ᵥ WithLp.ofLp (hardyTraceVec a t)) := by
  simp only [hardyWeightedPoint, hardyTraceVec, Matrix.mulVec, dotProduct,
    Pi.star_apply, Finset.mul_sum, mul_assoc]

theorem hardyWeightedPoint_lower
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (m : ℝ)
    (hL : ∀ t, (L t - (m : ℂ) • 1).PosSemidef) (a : HardySeq r) (t : HardyCircle) :
    m * ‖hardyTraceVec a t‖ ^ 2 ≤ (hardyWeightedPoint L a a t).re := by
  rw [hardyWeightedPoint_eq_quadratic]
  exact matrix_quadratic_lower (L t) m (hL t) (hardyTraceVec a t)

theorem hardyWeightedPoint_upper
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (M : ℝ)
    (hL : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef) (a : HardySeq r) (t : HardyCircle) :
    (hardyWeightedPoint L a a t).re ≤ M * ‖hardyTraceVec a t‖ ^ 2 := by
  rw [hardyWeightedPoint_eq_quadratic]
  exact matrix_quadratic_upper (L t) M (hL t) (hardyTraceVec a t)

end Yau.NodeProofs.D06Aux
