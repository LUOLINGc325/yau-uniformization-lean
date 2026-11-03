import Yau.Proofs.P04SquaredNormHessian

noncomputable section
open scoped Topology ContDiff InnerProductSpace Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem wirt_poleQuadratic (z₀ : ComplexVector n) (ε : ℝ) (z : ComplexVector n) (i : Fin n) :
    wirt (fun y => (poleQuadratic z₀ ε y : ℂ)) z (stdVec i) = star ((z-z₀) i) := by
  have hd := (poleQuadratic_smooth z₀ ε).differentiable (by norm_num) z
  have hD (v : ComplexVector n) :
      fderiv ℝ (poleQuadratic z₀ ε) z v = 2*⟪z-z₀,v⟫_ℝ := by
    rw [poleQuadratic_fderiv]
    rfl
  rw [wirt_ofReal_formula hd,hD,hD,model_real_inner,model_real_inner]
  simp only [inner_smul_right,stdVec,EuclideanSpace.inner_single_right,
    map_one,one_mul,Complex.star_def]
  apply Complex.ext <;> simp <;> ring

theorem gradientGram_poleQuadratic (z₀ : ComplexVector n) (ε : ℝ) (z : ComplexVector n) :
    gradientGram (poleQuadratic z₀ ε) z = fun i j => (z-z₀) i * star ((z-z₀) j) := by
  ext i j
  simp only [gradientGram,wirt_poleQuadratic,star_star]

end Yau.Proofs.P04Aux
