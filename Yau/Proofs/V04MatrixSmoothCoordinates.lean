import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Basis
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! Matrix smoothness is assembled and evaluated using continuous linear
coordinates for the actual Euclidean operator norm. The Sylvester inverse
uses one fixed diagonal basis, with no nonzero-rank assumption. -/

open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrix_contDiff_of_entries (A : ℝ → Matrix I I ℂ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun t => A t i j)) : ContDiff ℝ ∞ A := by
  have hs : ContDiff ℝ ∞ (fun t => ∑ i, ∑ j, (A t i j) • Matrix.single i j (1 : ℂ)) :=
    ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      (hA i j).smul_const (Matrix.single i j (1 : ℂ))
  convert hs using 1
  funext t
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single (A t)

def matrixEntryLM (i j : I) : Matrix I I ℂ →ₗ[ℝ] ℂ where
  toFun X := X i j
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def matrixEntryCLM (i j : I) : Matrix I I ℂ →L[ℝ] ℂ :=
  (matrixEntryLM i j).toContinuousLinearMap

theorem matrix_entry_contDiff {A : ℝ → Matrix I I ℂ} (hA : ContDiff ℝ ∞ A) (i j : I) :
    ContDiff ℝ ∞ (fun t => A t i j) := (matrixEntryCLM i j).contDiff.comp hA

def matrixSylvester (R : Matrix I I ℂ) : Matrix I I ℂ →ₗ[ℝ] Matrix I I ℂ :=
  LinearMap.mulLeft ℝ R + LinearMap.mulRight ℝ R

theorem matrixSylvester_injective_of_diagonal
    (e : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix I I ℂ) (r : I → ℝ) (hr : ∀ i, 0 < r i) :
    Function.Injective (matrixSylvester (e (Matrix.diagonal (fun i => (r i : ℂ))))) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro X hX
  let D : Matrix I I ℂ := Matrix.diagonal (fun i => (r i : ℂ))
  have hD : D * e.symm X + e.symm X * D = 0 := by
    have h := congrArg e.symm hX
    change e.symm (e D * X + X * e D) = e.symm 0 at h
    simpa only [map_add, map_mul, e.symm_apply_apply, map_zero] using h
  have hY : e.symm X = 0 := by
    ext i j
    have hij := congrArg (fun Z : Matrix I I ℂ => Z i j) hD
    have hne : (r i : ℂ) + (r j : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (add_pos (hr i) (hr j)))
    have hz : ((r i : ℂ) + (r j : ℂ)) * (e.symm X) i j = 0 := by
      change (D * e.symm X + e.symm X * D) i j = 0 at hij
      simp only [D, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
      simpa only [add_mul, mul_comm ((e.symm X) i j) (r j : ℂ)] using hij
    exact (mul_eq_zero.mp hz).resolve_left hne
  have hback := congrArg e hY
  simpa only [e.apply_symm_apply, map_zero] using hback

end Yau.Blueprint.V04Proof
