import Yau.LeafProofs.L05AutonomousLocalFrame
import Yau.LeafProofs.L05AutonomousSpatialGradientMatrix
import Mathlib.Topology.Algebra.Module.Star

noncomputable section
open scoped Topology Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/- Pin the matrix structure itself.  In particular, no local normed-group
instance on `Sym n` is inferred and then used to change the matrix norm. -/
local instance autoHessianRepMatGroup (n : ℕ) : NormedAddCommGroup (Mat n) :=
  Matrix.frobeniusNormedAddCommGroup
local instance autoHessianRepMatSpace (n : ℕ) : NormedSpace ℝ (Mat n) :=
  Matrix.frobeniusNormedSpace

/-- The fixed A theorem really uses the Frobenius matrix structure. -/
theorem auto_hessian_frobenius_entry_bound {n : ℕ} (H : Sym n) {B : ℝ}
    (hB : 0 ≤ B) (hEntry : ∀ i j, |(H : Mat n) i j| ≤ B) :
    ‖(H : Mat n)‖ ≤ (2*n : ℝ)*B := by
  have h := auto_matrix_norm_le_entry_bound H hB hEntry
  change ‖(H : Mat n)‖ ≤ (2*n : ℝ)*B at h
  exact h

/-- A bridge for the norm printed in the fixed finite-frame interface.
Both sides use the actual Frobenius subgroup structure, not the Pi norm. -/
theorem auto_hessian_frobenius_reconstruction {n N : ℕ} (e : Fin N → Space n)
    (hRecon : ∀ H : Sym n,
      ‖H‖ ≤ (2*n : ℝ)*2*∑ j, |autoBilinearMap n H (e j) (e j)|) :
    ∀ H : Sym n,
      ‖(H : Mat n)‖ ≤ (2*n : ℝ)*2*∑ j, |autoBilinearMap n H (e j) (e j)| := by
  intro H
  have h := hRecon H
  change ‖(H : Mat n)‖ ≤ (2*n : ℝ)*2*∑ j, |autoBilinearMap n H (e j) (e j)| at h
  exact h

theorem auto_hessian_frobenius_pair {n N : ℕ} (e : Fin N → Space n)
    (hRecon : ∀ H : Sym n,
      ‖(H : Mat n)‖ ≤ (2*n : ℝ)*2*∑ j, |autoBilinearMap n H (e j) (e j)|)
    {S : Set (Point n)} {eta K : ℝ} {H : Point n → Sym n}
    (hDir : ∀ j, ∀ p ∈ S, ∀ q ∈ S,
      |autoBilinearMap n (H p) (e j) (e j)-autoBilinearMap n (H q) (e j) (e j)| ≤
        K*holderWeight eta p q) :
    ∀ p ∈ S, ∀ q ∈ S,
      ‖(H p : Mat n)-(H q : Mat n)‖ ≤ (2*n : ℝ)*2*(N : ℝ)*K*holderWeight eta p q := by
  intro p hp q hq
  have hFields (j : Fin N) : |autoBilinearMap n (H p-H q) (e j) (e j)| ≤
      K*holderWeight eta p q := by
    simpa only [map_sub,_root_.sub_apply] using hDir j p hp q hq
  have hSum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hFields j)
  have h := (hRecon (H p-H q)).trans
    (mul_le_mul_of_nonneg_left hSum (by positivity : (0 : ℝ) ≤ (2*n : ℝ)*2))
  convert h using 1 <;>
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] <;> ring

theorem auto_hessian_sym_frobenius_norm_le {n : ℕ} (A : Mat n) :
    ‖(sym A : Mat n)‖ ≤ ‖A‖ := by
  have hStar : ‖star A‖=‖A‖ := by
    change ‖Aᴴ‖=‖A‖
    exact Matrix.frobenius_norm_conjTranspose A
  have hFormula : (sym A : Mat n)=(1/2 : ℝ) • (A+star A) := by
    simp only [sym,selfAdjointPart_apply_coe,invOf_eq_inv,one_div]
  rw [hFormula,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  have h := norm_add_le A (star A)
  rw [hStar] at h
  linarith only [h]

theorem auto_hessian_sym_frobenius_sub_le {n : ℕ} (A B : Mat n) :
    ‖(sym A : Mat n)-(sym B : Mat n)‖ ≤ ‖A-B‖ := by
  have h : (sym (A-B) : Mat n)=(sym A : Mat n)-(sym B : Mat n) := by
    exact congrArg (fun H : Sym n => (H : Mat n)) ((selfAdjointPart ℝ).map_sub A B)
  rw [← h]
  exact auto_hessian_sym_frobenius_norm_le (A-B)

theorem auto_hessian_bilinear_matrix {n : ℕ} (H : Sym n) :
    spatialGradientBilinearMatrix (autoBilinearMap n H)=(H : Mat n) := by
  ext i j
  exact autoBilinearMap_realVec H i j

theorem auto_hessian_bilinear_frobenius_bound {n : ℕ} (H : Sym n) :
    ‖autoBilinearMap n H‖ ≤ spatialGradientDimensionBudget n*‖(H : Mat n)‖ := by
  have h := spatialGradient_bilinear_frobenius_bound (autoBilinearMap n H)
  simpa only [auto_hessian_bilinear_matrix] using h

theorem auto_hessian_bilinear_sub_frobenius_bound {n : ℕ} (H J : Sym n) :
    ‖autoBilinearMap n H-autoBilinearMap n J‖ ≤
      spatialGradientDimensionBudget n*‖(H : Mat n)-(J : Mat n)‖ := by
  have h := spatialGradient_bilinear_frobenius_bound (autoBilinearMap n H-autoBilinearMap n J)
  have hMatrix : spatialGradientBilinearMatrix (autoBilinearMap n H-autoBilinearMap n J)=
      (H : Mat n)-(J : Mat n) := by
    ext i j
    simp only [spatialGradientBilinearMatrix,ContinuousLinearMap.sub_apply,
      autoBilinearMap_realVec,Matrix.sub_apply]
  simpa only [hMatrix] using h

end Yau.LeafProofs.L05AutonomousAux
