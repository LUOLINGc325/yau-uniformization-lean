import Yau.LeafProofs.L17NormalizedRicciForcing

open Set Metric
open scoped Matrix ComplexOrder ContDiff Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux
local instance potentialPositivityTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

theorem leviC_quadratic_abs_le {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (v : ComplexVector n) :
    |(star (WithLp.ofLp v) ⬝ᵥ (leviC f z *ᵥ WithLp.ofLp v)).re|≤
      (‖fderiv ℝ (fderiv ℝ f) z‖/2)*‖v‖^2 := by
  let H := fderiv ℝ (fderiv ℝ f) z
  have hA := H.le_opNorm₂ v v
  have hB := H.le_opNorm₂ (Complex.I • v) (Complex.I • v)
  have hI : ‖Complex.I • v‖=‖v‖ := by simp only [norm_smul,Complex.norm_I,one_mul]
  rw [hI] at hB
  rw [L22Aux.leviC_quadratic_re hf,L22Aux.complexLeviQuadratic,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
  have hS := (abs_add_le (H v v) (H (Complex.I • v) (Complex.I • v))).trans
    (add_le_add hA hB)
  change |H v v+H (Complex.I • v) (Complex.I • v)|/4≤_
  nlinarith

theorem matrix_posSemidef_of_re_quadratic_nonneg {n : ℕ}
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (hQ : ∀ v : ComplexVector n,0≤(star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re) :
    H.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨by simpa only [WithLp.ofLp_toLp] using hQ (WithLp.toLp 2 v),?_⟩
  have he := congrArg Complex.im (hH.star_dotProduct_mulVec_comm v v)
  simp only [Complex.star_def,Complex.conj_im] at he
  linarith

theorem matrix_half_double_comparison {n : ℕ}
    {G E : Matrix (Fin n) (Fin n) ℂ} {c d : ℝ} (hc : 0<c)
    (hG : G.PosDef) (hE : E.IsHermitian)
    (hLower : ∀ v : ComplexVector n,c*‖v‖^2≤(star (WithLp.ofLp v) ⬝ᵥ (G *ᵥ WithLp.ofLp v)).re)
    (hError : ∀ v : ComplexVector n,|(star (WithLp.ofLp v) ⬝ᵥ (E *ᵥ WithLp.ofLp v)).re|≤d*‖v‖^2)
    (hd : d≤c/2) :
    (G+E).PosDef ∧ (G+E-(1/2 : ℂ) • G).PosSemidef ∧
      ((2 : ℂ) • G-(G+E)).PosSemidef := by
  have hLo : (G+E-(1/2 : ℂ) • G).PosSemidef := by
    apply matrix_posSemidef_of_re_quadratic_nonneg
      ((hG.isHermitian.add hE).sub (hG.isHermitian.smul (by simp)))
    intro v
    have hL := hLower v
    have hB := (abs_le.mp (hError v)).1
    simp only [Matrix.sub_mulVec,Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_sub,
      dotProduct_add,dotProduct_smul,smul_eq_mul,Complex.sub_re,Complex.add_re,
      Complex.mul_re]
    have hs := mul_le_mul_of_nonneg_right hd (sq_nonneg ‖v‖)
    norm_num at *
    nlinarith
  have hHi : ((2 : ℂ) • G-(G+E)).PosSemidef := by
    apply matrix_posSemidef_of_re_quadratic_nonneg
      ((hG.isHermitian.smul (by simp)).sub (hG.isHermitian.add hE))
    intro v
    have hL := hLower v
    have hB := (abs_le.mp (hError v)).2
    simp only [Matrix.sub_mulVec,Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_sub,
      dotProduct_add,dotProduct_smul,smul_eq_mul,Complex.sub_re,Complex.add_re,
      Complex.mul_re]
    have hs := mul_le_mul_of_nonneg_right hd (sq_nonneg ‖v‖)
    norm_num at *
    nlinarith
  have hPos := (hG.smul (by norm_num : (0:ℂ)<1/2)).add_posSemidef hLo
  have heq : (1/2 : ℂ) • G+(G+E-(1/2 : ℂ) • G)=G+E := by abel
  exact ⟨heq ▸ hPos,hLo,hHi⟩

end Yau.LeafProofs.L17Aux
