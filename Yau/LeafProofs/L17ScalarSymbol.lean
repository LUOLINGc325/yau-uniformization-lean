import Yau.LeafProofs.L22LeviCalculus

/-!
The real principal symbol of the scalar Chern Laplacian. The realification here
has no metric factor two; the nested Wirtinger derivatives contribute one quarter.
-/

noncomputable section

open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ}

/-- Realification with the usual block convention, without a metric factor two. -/
def scalarRealification (H : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (RIdx n) (RIdx n) ℝ :=
  fun a b => if a.2 = b.2 then (H a.1 b.1).re
    else if a.2 = 0 then -(H a.1 b.1).im else (H a.1 b.1).im

theorem scalarRealification_eq_half (H : Matrix (Fin n) (Fin n) ℂ) :
    scalarRealification H = (1 / 2 : ℝ) • L12Aux.hermitianRealification H := by
  ext a b
  simp only [scalarRealification, L12Aux.hermitianRealification, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- The coordinate contraction on the actual real Hessian. -/
def realHessianContraction (A : Matrix (RIdx n) (RIdx n) ℝ)
    (f : ComplexVector n → ℝ) (z : ComplexVector n) : ℝ :=
  ∑ a, ∑ b, A a b * fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b)

/-- Exact normalization, for arbitrary complex coefficient matrices. -/
theorem trace_levi_eq_realHessianContraction
    (H : Matrix (Fin n) (Fin n) ℂ) {f : ComplexVector n → ℝ}
    {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z) :
    (Matrix.trace (H * leviC f z)).re =
      (1 / 4 : ℝ) * realHessianContraction (scalarRealification H) f z := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum,
    Complex.mul_re, leviC, (L18Aux.leviMatrix_entry_re_im hf stdVec _ _).1,
    (L18Aux.leviMatrix_entry_re_im hf stdVec _ _).2,
    realHessianContraction, Fintype.sum_prod_type, Fin.sum_univ_two,
    scalarRealification, realVec]
  norm_num only [Fin.zero_eta, Fin.mk.injEq, ↓reduceIte]
  simp only [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [stdVec, one_smul]
  norm_num
  ring

/-- The principal coefficient matrix in a holomorphic coordinate chart. -/
def scalarSymbol (G : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (RIdx n) (RIdx n) ℝ :=
  (1 / 4 : ℝ) • scalarRealification G⁻¹

theorem traceWith_levi_eq_scalarSymbol
    (G : Matrix (Fin n) (Fin n) ℂ) {f : ComplexVector n → ℝ}
    {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z) :
    traceWith G (leviC f z) = realHessianContraction (scalarSymbol G) f z := by
  rw [traceWith, trace_levi_eq_realHessianContraction G⁻¹ hf]
  simp only [realHessianContraction, scalarSymbol, Matrix.smul_apply, smul_eq_mul,
    mul_assoc, Finset.mul_sum]

theorem scalarRealification_quadratic
    (H : Matrix (Fin n) (Fin n) ℂ) (r : RIdx n → ℝ) :
    star r ⬝ᵥ (scalarRealification H *ᵥ r) =
      (star (L12Aux.complexCoordsOfReal r) ⬝ᵥ
        (H *ᵥ L12Aux.complexCoordsOfReal r)).re := by
  rw [scalarRealification_eq_half, Matrix.smul_mulVec, dotProduct_smul,
    L12Aux.hermitianRealification_quadratic]
  simp only [smul_eq_mul]
  ring

theorem scalarRealification_isHermitian
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) :
    (scalarRealification H).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨i, a⟩ ⟨j, b⟩
  have he := congrArg Complex.re (hH.apply i j)
  have hi := congrArg Complex.im (hH.apply i j)
  fin_cases a <;> fin_cases b <;>
    simp_all [scalarRealification]
  linarith

theorem scalarRealification_posSemidef
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosSemidef) :
    (scalarRealification H).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (scalarRealification_isHermitian hH.isHermitian)
  intro r
  rw [scalarRealification_quadratic]
  exact (Complex.nonneg_iff.mp (hH.dotProduct_mulVec_nonneg _)).1

theorem complexCoordsOfReal_injective :
    Function.Injective (L12Aux.complexCoordsOfReal (n := n)) := by
  intro u v h
  ext ⟨i, a⟩
  have he := congrFun h i
  fin_cases a
  · simpa [L12Aux.complexCoordsOfReal, Complex.mul_re] using congrArg Complex.re he
  · simpa [L12Aux.complexCoordsOfReal, Complex.mul_im] using congrArg Complex.im he

theorem scalarRealification_posDef
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) :
    (scalarRealification H).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (scalarRealification_isHermitian hH.isHermitian)
  intro r hr
  rw [scalarRealification_quadratic]
  apply (Complex.pos_iff.mp (hH.dotProduct_mulVec_pos ?_)).1
  intro hz
  apply hr
  apply complexCoordsOfReal_injective
  ext i
  simpa [L12Aux.complexCoordsOfReal] using congrFun hz i

theorem scalarSymbol_posDef
    {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    (scalarSymbol G).PosDef := by
  exact (scalarRealification_posDef hG.inv).smul (by norm_num : (0 : ℝ) < 1 / 4)

end Yau.LeafProofs.L17Aux
