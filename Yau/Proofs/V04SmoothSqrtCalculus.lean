import Yau.Proofs.V04MatrixSmoothCoordinates
import Yau.Proofs.V04MajorantOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-! The positive regularized root is the actual continuous functional
calculus of the frozen spectral scalar. Its square and affine majorant
identities hold before any differentiability argument. -/

open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff ComplexOrder MatrixOrder
open Filter
noncomputable section
namespace Yau.Blueprint.V04Proof.V04SmoothSqrt
open Yau Yau.Blueprint

variable {I : Type*} [Fintype I] [DecidableEq I]

def regularRootScalar (δ x : ℝ) : ℝ := Real.sqrt (x ^ 2 + δ ^ 2)

def regularMatrixRoot (δ : ℝ) (A : Matrix I I ℂ) : Matrix I I ℂ := cfc (regularRootScalar δ) A

theorem regularRootScalar_continuous (δ : ℝ) : Continuous (regularRootScalar δ) :=
  Real.continuous_sqrt.comp ((continuous_id.pow 2).add continuous_const)

theorem regularRootScalar_mul_self (δ x : ℝ) :
    regularRootScalar δ x * regularRootScalar δ x = x ^ 2 + δ ^ 2 := by
  simpa only [regularRootScalar, pow_two] using
    Real.sq_sqrt (show 0 ≤ x ^ 2 + δ ^ 2 by positivity)

theorem regularMatrixRoot_square (δ : ℝ) (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    regularMatrixRoot δ A * regularMatrixRoot δ A = A * A + algebraMap ℝ (Matrix I I ℂ) (δ ^ 2) := by
  have hρ : ContinuousOn (regularRootScalar δ) (spectrum ℝ A) :=
    (regularRootScalar_continuous δ).continuousOn
  unfold regularMatrixRoot
  rw [← cfc_mul _ _ A hρ hρ]
  have heq : (fun x => regularRootScalar δ x * regularRootScalar δ x) =
      (fun x : ℝ => x ^ 2 + δ ^ 2) := funext (regularRootScalar_mul_self δ)
  rw [heq, cfc_add A (fun x : ℝ => x ^ 2) (fun _ => δ ^ 2) (by fun_prop) continuousOn_const,
    cfc_pow_id A 2 (show IsSelfAdjoint A from hA),
    cfc_const (δ ^ 2) A (show IsSelfAdjoint A from hA), pow_two]

theorem regularMatrixRoot_continuous {α : Type*} [TopologicalSpace α]
    (δ : ℝ) {A : α → Matrix I I ℂ} (hA : Continuous A) (hH : ∀ x, (A x).IsHermitian) :
    Continuous (fun x => regularMatrixRoot δ (A x)) :=
  Continuous.cfc_of_mem_nhdsSet (s := Set.univ) (regularRootScalar δ)
    Filter.univ_mem hA (fun x => (show IsSelfAdjoint (A x) from hH x))
    (regularRootScalar_continuous δ).continuousOn

theorem regularMatrixRoot_sylvester_injective {δ : ℝ} (hδ : 0 < δ)
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    Function.Injective (matrixSylvester (regularMatrixRoot δ A)) := by
  let U := hA.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U
  let r : I → ℝ := fun i => regularRootScalar δ (hA.eigenvalues i)
  have hr : ∀ i, 0 < r i := by
    intro i
    apply Real.sqrt_pos.mpr
    have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hδsq
  have hroot : regularMatrixRoot δ A = e (Matrix.diagonal (fun i => (r i : ℂ))) := by
    simpa only [regularMatrixRoot, e, r, U, Matrix.IsHermitian.cfc,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hA.cfc_eq (regularRootScalar δ)
  rw [hroot]
  exact matrixSylvester_injective_of_diagonal e r hr

variable {n : ℕ}

theorem smoothMajorant_eq_regularMatrixRoot (δ : ℝ) (A : CotangentMatrix n)
    (hA : A.IsHermitian) :
    smoothMajorant δ A = algebraMap ℝ (CotangentMatrix n) δ +
      (1 / 2 : ℝ) • (A + regularMatrixRoot δ A) := by
  rw [smoothMajorant_eq_cfc δ A hA]
  have hf : scalarMajorant δ = fun x : ℝ => δ + (1 / 2 : ℝ) * (x + regularRootScalar δ x) := by
    funext x
    unfold scalarMajorant regularRootScalar
    ring
  have hg : Continuous (fun x : ℝ => x + regularRootScalar δ x) :=
    continuous_id.add (regularRootScalar_continuous δ)
  rw [hf, cfc_const_add δ _ A (show ContinuousOn (fun x : ℝ => (1 / 2 : ℝ) * (x + regularRootScalar δ x))
      (spectrum ℝ A) from (continuous_const.mul hg).continuousOn) (show IsSelfAdjoint A from hA),
    cfc_const_mul (1 / 2 : ℝ) _ A hg.continuousOn,
    cfc_add A (fun x : ℝ => x) (regularRootScalar δ) continuousOn_id
      (regularRootScalar_continuous δ).continuousOn,
    cfc_id' (R := ℝ) A (show IsSelfAdjoint A from hA)]
  rfl

end Yau.Blueprint.V04Proof.V04SmoothSqrt
