import Yau.Proofs.C05UnitaryFrameGram

/-! Simultaneous normalization of two actual positive definite Hermitian forms. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Proofs.C05UnitaryFrameAux
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unitary_frame_exists (g A : Matrix ι ι ℂ) (hg : g.PosDef) (hA : A.PosDef) :
    ∃ (W : Matrix ι ι ℂ) (lam : ι → ℝ), W.det ≠ 0 ∧
      Wᴴ*g*W=1 ∧ Wᴴ*A*W=Matrix.diagonal (fun j => (lam j : ℂ)) ∧
      (∀ j, 0<lam j) ∧ (∑ j,lam j)=((g⁻¹*A).trace).re := by
  have hcast (r : ℝ) : RCLike.ofReal (K := ℂ) r = (r : ℂ) := rfl
  obtain ⟨D,hdet,hD,hGram⟩ := inverse_metric_orthonormal_factor g hg
  let B := Dᴴ*A*D
  have hB : B.PosDef := hA.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det D).mpr (isUnit_iff_ne_zero.mpr hdet)))
  let U := hB.isHermitian.eigenvectorUnitary
  let W : Matrix ι ι ℂ := D*U
  let lam : ι → ℝ := hB.isHermitian.eigenvalues
  have hU : (U : Matrix ι ι ℂ)ᴴ*(U : Matrix ι ι ℂ)=1 :=
    Unitary.coe_star_mul_self U
  have hWGram : Wᴴ*g*W=1 := by
    calc
      _ = (U : Matrix ι ι ℂ)ᴴ*(Dᴴ*g*D)*U := by
        simp only [W,Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = 1 := by rw [hGram,Matrix.mul_one,hU]
  have hWdet : W.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hWGram
    simp only [Matrix.det_mul,Matrix.det_conjTranspose,hz,star_zero,zero_mul,mul_zero,
      Matrix.det_one] at hh
    exact zero_ne_one hh
  have hdiag : Wᴴ*A*W=Matrix.diagonal (fun j => (lam j : ℂ)) := by
    have H := hB.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    simpa only [Unitary.conjStarAlgAut_star_apply,Matrix.star_eq_conjTranspose,W,B,U,lam,
      Matrix.conjTranspose_mul,Matrix.mul_assoc,Function.comp_def,hcast] using H
  have htrace : B.trace=(g⁻¹*A).trace := by
    dsimp only [B]
    rw [Matrix.trace_mul_cycle,←hD]
  refine ⟨W,lam,hWdet,hWGram,hdiag,hB.eigenvalues_pos,?_⟩
  have H := hB.isHermitian.trace_eq_sum_eigenvalues
  rw [htrace] at H
  simpa only [Complex.re_sum,hcast,Complex.ofReal_re,lam] using (congrArg Complex.re H).symm

 theorem eigenvalue_le_sum {lam : ι → ℝ} (hpos : ∀ j, 0 ≤ lam j) (j : ι) :
    lam j ≤ ∑ i, lam i := Finset.single_le_sum (fun i _ => hpos i) (Finset.mem_univ j)

end Yau.Proofs.C05UnitaryFrameAux
