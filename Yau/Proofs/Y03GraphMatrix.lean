import Yau.Proofs.Y03CoordinateGraphStep
import Yau.Proofs.Y03MatrixBound
import Yau.Proofs.Y03Inverse

/-! The coordinate graph lifts produce an actual unit triangular matrix. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

def lowerWeightSet (w : Fin n → ℝ) (x : ℝ) : Finset (Fin n) := Finset.univ.filter (fun i => w i ≤ x)

theorem stdVec_mem_coordinateSubspace {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) :
    stdVec i ∈ coordinateSubspace s := by
  intro l hl
  have hli : l ≠ i := by intro h; subst l; exact hl hi
  simp [stdVec, EuclideanSpace.single, hli]

def weightBasis (w : Fin n → ℝ) (i : Fin n) : coordinateSubspace (lowerWeightSet w (w i)) :=
  ⟨stdVec i, stdVec_mem_coordinateSubspace (Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩)⟩

def graphMatrix (w : Fin n → ℝ)
    (T : (x : ℝ) → coordinateSubspace (lowerWeightSet w x) →L[ℂ] ComplexVector n) : Herm n :=
  fun i l => T (w i) (weightBasis w i) l

theorem graphMatrix_entry_eq_of_le (w : Fin n → ℝ)
    (T : (x : ℝ) → coordinateSubspace (lowerWeightSet w x) →L[ℂ] ComplexVector n)
    (hT : ∀ x, (coordinateProjectionOnto (lowerWeightSet w x)).comp (T x) =
      ContinuousLinearMap.id ℂ (coordinateSubspace (lowerWeightSet w x)))
    (i l : Fin n) (hli : w l ≤ w i) : graphMatrix w T i l = if l = i then 1 else 0 := by
  have hp := congrArg (fun L : coordinateSubspace (lowerWeightSet w (w i)) →L[ℂ]
    coordinateSubspace (lowerWeightSet w (w i)) => L (weightBasis w i)) (hT (w i))
  have hcoord := congrArg (fun v : coordinateSubspace (lowerWeightSet w (w i)) =>
    (v : ComplexVector n) l) hp
  change coordinateProjection (lowerWeightSet w (w i)) (T (w i) (weightBasis w i)) l = (stdVec i) l at hcoord
  have hlmem : l ∈ lowerWeightSet w (w i) := by
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hli⟩
  rw [coordinateProjection_apply, ite_eq_left hlmem] at hcoord
  simpa [graphMatrix, stdVec, EuclideanSpace.single] using hcoord

theorem graphMatrix_diagonal (w : Fin n → ℝ)
    (T : (x : ℝ) → coordinateSubspace (lowerWeightSet w x) →L[ℂ] ComplexVector n)
    (hT : ∀ x, (coordinateProjectionOnto (lowerWeightSet w x)).comp (T x) =
      ContinuousLinearMap.id ℂ (coordinateSubspace (lowerWeightSet w x))) :
    ∀ i, graphMatrix w T i i = 1 := by
  intro i
  simpa only [ite_true] using graphMatrix_entry_eq_of_le w T hT i i le_rfl

theorem graphMatrix_strict_support (w : Fin n → ℝ)
    (T : (x : ℝ) → coordinateSubspace (lowerWeightSet w x) →L[ℂ] ComplexVector n)
    (hT : ∀ x, (coordinateProjectionOnto (lowerWeightSet w x)).comp (T x) =
      ContinuousLinearMap.id ℂ (coordinateSubspace (lowerWeightSet w x))) :
    ∀ i l, i ≠ l → graphMatrix w T i l ≠ 0 → w i < w l := by
  intro i l hil hentry
  by_contra hn
  have hz := graphMatrix_entry_eq_of_le w T hT i l (le_of_not_gt hn)
  exact hentry (by simpa only [ite_eq_right (Ne.symm hil)] using hz)

theorem graphMatrix_norm_le (w : Fin n → ℝ)
    (T : (x : ℝ) → coordinateSubspace (lowerWeightSet w x) →L[ℂ] ComplexVector n)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ x, ‖T x‖ ≤ C) :
    matOpNorm (graphMatrix w T) ≤ (n : ℝ) ^ 2 * C := by
  apply matOpNorm_le_card_sq_mul hC
  intro i l
  have hb : ‖weightBasis w i‖ = 1 := by change ‖stdVec i‖ = 1; simp [stdVec, EuclideanSpace.single]
  exact (PiLp.norm_apply_le (T (w i) (weightBasis w i)) l).trans
    (((T (w i)).le_opNorm _).trans (by rw [hb, mul_one]; exact hT (w i)))

end Yau.Blueprint.Alignment.Y03Proof
