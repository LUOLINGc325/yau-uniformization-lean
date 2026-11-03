import Yau.Proofs.F01HolomorphicJacobianJets

/-! Finite holomorphic matrix inversion and the full regularity of the
actual coordinate Jacobian, with no auxiliary holomorphic-inverse premise. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem complex_contDiffOn_matrix_det {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : E → Matrix (Fin n) (Fin n) ℂ} {S : Set E}
    (hA : ∀ i j, ContDiffOn ℂ ∞ (fun w => A w i j) S) :
    ContDiffOn ℂ ∞ (fun w => (A w).det) S := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod fun i _ => hA (σ i) i)

theorem complex_contDiffOn_matrix_inv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : E → Matrix (Fin n) (Fin n) ℂ} {S : Set E}
    (hA : ∀ i j, ContDiffOn ℂ ∞ (fun w => A w i j) S)
    (hdet : ∀ w ∈ S, (A w).det ≠ 0) (i j : Fin n) :
    ContDiffOn ℂ ∞ (fun w => (A w)⁻¹ i j) S := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul, Matrix.adjugate_apply]
  apply ((complex_contDiffOn_matrix_det hA).inv hdet).mul
  apply complex_contDiffOn_matrix_det
  intro k l
  simp only [Matrix.updateRow_apply]
  by_cases hkj : k = j
  · simp only [hkj, ↓reduceIte]
    exact contDiffOn_const
  · simp only [hkj, ↓reduceIte]
    exact hA k l

theorem holomorphic_jacobian_entry_contDiffOn
    {T : ComplexVector n → ComplexVector n} {S : Set (ComplexVector n)}
    (hS : IsOpen S) (hT : ContDiffOn ℂ ∞ T S) (i j : Fin n) :
    ContDiffOn ℂ ∞ (fun w => linearMatrix (fderiv ℂ T w) i j) S := by
  intro z hz
  have hD : ContDiffAt ℂ ∞ (fderiv ℂ T) z :=
    (hT.contDiffAt (hS.mem_nhds hz)).fderiv_right (m := ∞) (by simp)
  have hcoord : ContDiffAt ℂ ∞ (fun w => fderiv ℂ T w (stdVec j)) z :=
    hD.clm_apply contDiffAt_const
  exact ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).contDiff.contDiffAt.comp z
    hcoord).contDiffWithinAt

end Yau.NodeProofs.F01Aux
