import Yau.Proofs.V03ChartKahlerTwoForm

/-! The actual base Hermitian metric as a cotangent-coordinate matrix,
with zero vertical directions and the original tangent-vector contraction. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

def baseCotangentMatrix (h : HermitianField M) (x : M.Carrier) (z : CotangentCoord n) :
    CotangentMatrix n := fun i j => match i, j with
  | .inl a, .inl b => hMat h x z.1 a b
  | _, _ => 0

theorem baseCotangentMatrix_contract (h : HermitianField M) (x : M.Carrier)
    (z : CotangentCoord n) (u v : CotangentIndex n → ℂ) :
    star u ⬝ᵥ (baseCotangentMatrix h x z *ᵥ v) =
      (h (chartInv x z.1)).toFun
        (chartVec x (chartInv x z.1) (cotangentVectorOfCoords u).1)
        (chartVec x (chartInv x z.1) (cotangentVectorOfCoords v).1) := by
  simp only [dotProduct, Matrix.mulVec, baseCotangentMatrix, Fintype.sum_sum_type,
    Pi.star_apply, Finset.sum_const_zero, zero_mul, mul_zero, add_zero, zero_add]
  exact hMat_pair h x z.1 (WithLp.toLp 2 (fun i => u (.inl i)))
    (WithLp.toLp 2 (fun i => v (.inl i)))

theorem cotangentVectorOfCoords_single (i : CotangentIndex n) :
    cotangentVectorOfCoords (Pi.single i (1 : ℂ)) = cotangentDir i := by
  classical
  rw [cotangentVectorOfCoords_eq_sum]
  simp [Pi.single_apply]

theorem baseCotangentMatrix_entry (h : HermitianField M) (x : M.Carrier)
    (z : CotangentCoord n) (i j : CotangentIndex n) :
    baseCotangentMatrix h x z i j =
      (h (chartInv x z.1)).toFun (chartVec x (chartInv x z.1) (cotangentDir i).1)
        (chartVec x (chartInv x z.1) (cotangentDir j).1) := by
  classical
  have hh := baseCotangentMatrix_contract h x z (Pi.single i 1) (Pi.single j 1)
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply, cotangentVectorOfCoords_single] using hh

theorem baseCotangentMatrix_isHermitian (h : HermitianField M) (x : M.Carrier)
    (z : CotangentCoord n) : (baseCotangentMatrix h x z).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, baseCotangentMatrix_entry]
  exact ((h (chartInv x z.1)).conjugate_symmetric _ _).symm

theorem baseCotangentMatrix_entry_contDiffOn (g : SmoothMetric M) (x : M.Carrier)
    (i j : CotangentIndex n) :
    ContDiffOn ℝ ∞ (fun z => baseCotangentMatrix g.form x z i j) (cotangentTarget x) := by
  cases i with
  | inl a =>
    cases j with
    | inl b => exact (hMat_contDiffOn g x a b).comp contDiff_fst.contDiffOn (fun z hz => hz.1)
    | inr b => exact contDiffOn_const
  | inr a => exact contDiffOn_const

end Yau.Blueprint.V03Proof
