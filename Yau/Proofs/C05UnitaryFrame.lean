import Yau.Proofs.C05UnitaryFrameSpectrum
import Yau.Geometry.Calculus

/-! Bounds on the genuine simultaneous eigenvalues from the frozen Rayleigh infimum. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Proofs.C05UnitaryFrameAux
open Yau
variable {n : ℕ}

theorem column_quadratic (H W : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    star (W.col j) ⬝ᵥ (H *ᵥ W.col j)=(Wᴴ*H*W) j j := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.col_apply,Pi.star_apply,dotProduct,Matrix.mulVec]

 theorem relMin_le_rayleigh_of_pos {g A : Matrix (Fin n) (Fin n) ℂ}
    (hpos : 0 < relMinEigenvalue g A) (v : ComplexVector n) (hv : v ≠ 0) :
    relMinEigenvalue g A ≤
      (star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)).re /
        (star (WithLp.ofLp v) ⬝ᵥ (g *ᵥ WithLp.ofLp v)).re := by
  let q : {v : ComplexVector n // v ≠ 0} → ℝ := fun v =>
    (star (WithLp.ofLp v.1) ⬝ᵥ (A *ᵥ WithLp.ofLp v.1)).re /
      (star (WithLp.ofLp v.1) ⬝ᵥ (g *ᵥ WithLp.ofLp v.1)).re
  have hbd : BddBelow (Set.range q) := by
    by_contra hn
    have hz := ConditionallyCompleteLinearOrder.csInf_of_not_bddBelow (Set.range q) hn
    change 0 < sInf (Set.range q) at hpos
    rw [hz] at hpos
    norm_num at hpos
  exact ciInf_le hbd ⟨v,hv⟩

 theorem eigenvalues_ge_relMin (g A W : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ)
    (hGram : Wᴴ*g*W=1) (hdiag : Wᴴ*A*W=Matrix.diagonal (fun j => (lam j : ℂ)))
    {mu : ℝ} (hmu : 0 < mu) (hpin : mu ≤ relMinEigenvalue g A) :
    ∀ j, mu ≤ lam j := by
  intro j
  have hgcol : star (W.col j) ⬝ᵥ (g *ᵥ W.col j)=1 := by
    rw [column_quadratic,hGram,Matrix.one_apply_eq]
  have hAcol : star (W.col j) ⬝ᵥ (A *ᵥ W.col j)=(lam j : ℂ) := by
    rw [column_quadratic,hdiag,Matrix.diagonal_apply_eq]
  let v : ComplexVector n := WithLp.toLp 2 (W.col j)
  have hv : v ≠ 0 := by
    intro hz
    have hzero : W.col j=0 := by
      have hh := congrArg WithLp.ofLp hz
      simpa only [v,WithLp.ofLp_toLp,WithLp.ofLp_zero] using hh
    simp [hzero] at hgcol
  have H := relMin_le_rayleigh_of_pos (hmu.trans_le hpin) v hv
  have hray : (star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)).re /
      (star (WithLp.ofLp v) ⬝ᵥ (g *ᵥ WithLp.ofLp v)).re=lam j := by
    simp only [v,WithLp.ofLp_toLp,hAcol,hgcol,Complex.ofReal_re,Complex.one_re,div_one]
  rw [hray] at H
  exact hpin.trans H

 theorem unitary_frame_exists_with_lower (g A : Matrix (Fin n) (Fin n) ℂ)
    (hg : g.PosDef) (hA : A.PosDef) {mu : ℝ} (hmu : 0 < mu)
    (hpin : mu ≤ relMinEigenvalue g A) :
    ∃ (W : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ), W.det ≠ 0 ∧
      Wᴴ*g*W=1 ∧ Wᴴ*A*W=Matrix.diagonal (fun j => (lam j : ℂ)) ∧
      (∀ j, 0<lam j) ∧ (∑ j,lam j)=((g⁻¹*A).trace).re ∧
      (∀ j,mu ≤ lam j) ∧ (∀ j,lam j ≤ ∑ i,lam i) := by
  obtain ⟨W,lam,hdet,hGram,hdiag,hpos,htrace⟩ := unitary_frame_exists g A hg hA
  exact ⟨W,lam,hdet,hGram,hdiag,hpos,htrace,
    eigenvalues_ge_relMin g A W lam hGram hdiag hmu hpin,
    eigenvalue_le_sum (fun j => (hpos j).le)⟩

 theorem unitary_frame_exists_trace_one (g A : Matrix (Fin n) (Fin n) ℂ)
    (hg : g.PosDef) (hA : A.PosDef) {mu : ℝ} (hmu : 0 < mu)
    (hpin : mu ≤ relMinEigenvalue g A) (htrace : ((g⁻¹*A).trace).re=1) :
    ∃ (W : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ), W.det ≠ 0 ∧
      Wᴴ*g*W=1 ∧ Wᴴ*A*W=Matrix.diagonal (fun j => (lam j : ℂ)) ∧
      (∀ j,0<lam j) ∧ (∑ j,lam j)=1 ∧
      (∀ j,mu ≤ lam j) ∧ (∀ j,lam j ≤ 1) := by
  obtain ⟨W,lam,hdet,hGram,hdiag,hpos,htr,hlower,hupper⟩ :=
    unitary_frame_exists_with_lower g A hg hA hmu hpin
  rw [htrace] at htr
  refine ⟨W,lam,hdet,hGram,hdiag,hpos,htr,hlower,?_⟩
  simpa only [htr] using hupper

end Yau.Proofs.C05UnitaryFrameAux
