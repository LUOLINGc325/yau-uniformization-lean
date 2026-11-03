import Yau.Proofs.F01ScalarSymbolEllipticity
import Yau.Proofs.F01MatrixSmooth

/-! The canonical native scalar principal coefficient is genuinely
smooth in the original Frobenius matrix norms on the nonsingular domain. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem real_matrix_contDiffOn_of_entries {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    {S : Set E} {G : E → Matrix ι ι ℝ}
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) S) : ContDiffOn ℝ ∞ G S := by
  let L : (ι → ι → ℝ) →ₗ[ℝ] Matrix ι ι ℝ :=
    { toFun := Matrix.of
      map_add' := by intro A B; rfl
      map_smul' := by intro c A; rfl }
  let T : (ι → ι → ℝ) →L[ℝ] Matrix ι ι ℝ :=
    LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := ι → ι → ℝ) (F' := Matrix ι ι ℝ) L
  have hp : ContDiffOn ℝ ∞ (fun x : E => fun i j : ι => G x i j) S :=
    contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (hG i))
  convert! T.contDiff.comp_contDiffOn hp using 1

def frobeniusComplexEntryCLM (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    (E := Matrix (Fin n) (Fin n) ℂ) (F' := ℂ)
    { toFun := fun H => H i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem frobenius_matrix_det_contDiff :
    ContDiff ℝ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => H.det) :=
  contDiffOn_univ.mp (Yau.LeafProofs.L12Aux.contDiffOn_matrix_det
    (fun i j => (frobeniusComplexEntryCLM i j).contDiff.contDiffOn))

theorem matrix_nonsingular_domain_isOpen :
    IsOpen {H : Matrix (Fin n) (Fin n) ℂ | H.det ≠ 0} :=
  isOpen_ne_fun frobenius_matrix_det_contDiff.continuous continuous_const

theorem scalarSymbol_contDiffOn_nonsingular :
    ContDiffOn ℝ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => scalarSymbol H)
      {H | H.det ≠ 0} := by
  have hentry (i j : Fin n) :
      ContDiffOn ℝ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => H⁻¹ i j) {H | H.det ≠ 0} :=
    Yau.LeafProofs.L12Aux.contDiffOn_matrix_inv
      (fun k l => (frobeniusComplexEntryCLM k l).contDiff.contDiffOn) (fun _ h => h) i j
  apply real_matrix_contDiffOn_of_entries
  intro a b
  simp only [scalarSymbol, Matrix.smul_apply, smul_eq_mul]
  apply contDiffOn_const.mul
  have hre := Complex.reCLM.contDiff.comp_contDiffOn (hentry a.1 b.1)
  have him := Complex.imCLM.contDiff.comp_contDiffOn (hentry a.1 b.1)
  by_cases hab : a.2 = b.2
  · simp only [scalarRealification, hab, ite_true]
    convert! hre using 1
  · simp only [scalarRealification, hab, ite_false]
    by_cases ha : a.2 = 0
    · simp only [ha, ite_true]
      convert! him.neg using 1
    · simp only [ha, ite_false]
      convert! him using 1

end Yau.NodeProofs.F01Aux
