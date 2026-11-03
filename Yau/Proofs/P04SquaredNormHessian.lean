import Yau.Proofs.P04LeviLogChain

noncomputable section
open Filter
open scoped Topology ContDiff InnerProductSpace Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem model_real_inner (v w : ComplexVector n) :
    ⟪v,w⟫_ℝ = (⟪v,w⟫_ℂ).re := by
  simp only [PiLp.inner_apply, Complex.inner, RCLike.inner_apply]
  simpa using (map_sum Complex.reCLM (fun i : Fin n => w i * star (v i)) Finset.univ).symm

def poleQuadratic (z₀ : ComplexVector n) (ε : ℝ) (z : ComplexVector n) : ℝ :=
  ‖z-z₀‖^2+ε^2

theorem poleQuadratic_fderiv (z₀ : ComplexVector n) (ε : ℝ) (z : ComplexVector n) :
    fderiv ℝ (poleQuadratic z₀ ε) z = (2 : ℝ) • innerSL ℝ (z-z₀) := by
  unfold poleQuadratic
  have HH := ((hasFDerivAt_id z).sub_const z₀).norm_sq.add_const (ε^2)
  simpa only [id_eq,ContinuousLinearMap.comp_id,two_smul] using HH.fderiv

theorem poleQuadratic_secondFDeriv (z₀ : ComplexVector n) (ε : ℝ)
    (z v w : ComplexVector n) :
    fderiv ℝ (fderiv ℝ (poleQuadratic z₀ ε)) z v w = 2*⟪v,w⟫_ℝ := by
  have heq : fderiv ℝ (poleQuadratic z₀ ε) = fun y => (2 : ℝ) • innerSL ℝ (y-z₀) :=
    funext (fun y => poleQuadratic_fderiv z₀ ε y)
  have HH := ((innerSL ℝ : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ).hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const z₀)).const_smul (2 : ℝ)
  rw [heq]
  have Hderiv : fderiv ℝ (fun y => (2 : ℝ) • innerSL ℝ (y-z₀)) z = (2 : ℝ) • innerSL ℝ := by
    simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id,Pi.smul_def] using HH.fderiv
  rw [Hderiv]
  rfl

theorem poleQuadratic_smooth (z₀ : ComplexVector n) (ε : ℝ) :
    ContDiff ℝ ∞ (poleQuadratic z₀ ε) :=
  ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)).add contDiff_const

/-- The regularized squared Euclidean radius has precisely the identity Levi
matrix in the original convention, independently of its center and epsilon. -/
theorem leviC_poleQuadratic (z₀ : ComplexVector n) (ε : ℝ) (z : ComplexVector n) :
    leviC (poleQuadratic z₀ ε) z=1 := by
  have hf : ContDiffAt ℝ 2 (poleQuadratic z₀ ε) z :=
    (poleQuadratic_smooth z₀ ε).contDiffAt.of_le (by simp)
  ext i j
  have HH := L18Aux.leviMatrix_entry_re_im hf stdVec i j
  apply Complex.ext
  · rw [show (leviC (poleQuadratic z₀ ε) z i j).re = _ from HH.1]
    simp only [poleQuadratic_secondFDeriv]
    by_cases hij : i=j
    · subst j
      simp [stdVec,model_real_inner,inner_smul_left,inner_smul_right,EuclideanSpace.inner_single_left,norm_smul] <;> norm_num
    · simp [stdVec,model_real_inner,inner_smul_left,inner_smul_right,EuclideanSpace.inner_single_left,norm_smul,hij,Ne.symm hij]
  · rw [show (leviC (poleQuadratic z₀ ε) z i j).im = _ from HH.2]
    simp only [poleQuadratic_secondFDeriv]
    by_cases hij : i=j
    · subst j
      simp [stdVec,model_real_inner,inner_smul_left,inner_smul_right,EuclideanSpace.inner_single_left,norm_smul] <;> norm_num
    · simp [stdVec,model_real_inner,inner_smul_left,inner_smul_right,EuclideanSpace.inner_single_left,norm_smul,hij,Ne.symm hij]

end Yau.Proofs.P04Aux
