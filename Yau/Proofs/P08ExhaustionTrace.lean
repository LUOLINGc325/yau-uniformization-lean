import Yau.Proofs.P08CanonicalRegularization

/-! Tracing the two original exhaustion Hessian inequalities. -/
noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P08Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem traceWith_real_smul_self (g : HermitianField M) (x : M.Carrier) (c : ℝ) :
    traceWith (gMat g x) ((c : ℂ) • gMat g x) = c * n := by
  have hH := L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)
  have hG : (gMat g x).PosDef := hH
  rw [traceWith, Matrix.mul_smul, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr hG.det_pos.ne'), Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, mul_zero, sub_zero]

theorem laplacian_abs_le_of_levi_bounds (g : HermitianField M)
    (u : M.Carrier → ℝ) (x : M.Carrier) (c : ℝ)
    (hlo : HermLE ((-c : ℂ) • gMat g x) (levi u x))
    (hhi : HermLE (levi u x) ((c : ℂ) • gMat g x)) :
    |laplacian g u x| ≤ c * n := by
  have hlo' := traceWith_mono g x hlo
  have hhi' := traceWith_mono g x hhi
  rw [traceWith_real_smul_self g x c] at hhi'
  have heq : (-c : ℂ) = ((-c : ℝ) : ℂ) := by simp
  rw [heq, traceWith_real_smul_self g x (-c)] at hlo'
  exact abs_le.mpr ⟨by simpa only [laplacian, neg_mul] using hlo', hhi'⟩

end Yau.NodeProofs.P08Aux
