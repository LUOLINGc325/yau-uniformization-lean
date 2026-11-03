import Yau.LeafProofs.L21WeightedSmallC1
import Yau.LeafProofs.L21CoordinateChart
import Yau.LeafProofs.L21CorrectedLevi

/-! Actual scalar columns assemble to a smooth vector correction, and
subtracting it from the identity produces the literal graph coordinates. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def columnVector (v : Fin n → X n → ℂ) (x : X n) : X n := ∑ k, v k x • Yau.stdVec k

theorem columnVector_apply (v : Fin n → X n → ℂ) (x : X n) (k : Fin n) :
    columnVector v x k = v k x := by
  classical
  simp [columnVector, Yau.stdVec, PiLp.single_apply, Pi.single_apply, eq_comm]

theorem contDiff_columnVector (v : Fin n → X n → ℂ) (hv : ∀ k, ContDiff ℝ ∞ (v k)) :
    ContDiff ℝ ∞ (columnVector v) :=
  ContDiff.sum fun k _ => (hv k).smul_const _

theorem norm_real_clm_le_sum_coordinates (L : X n →L[ℝ] X n) :
    ‖L‖ ≤ ∑ k : Fin n, ‖((EuclideanSpace.proj k).restrictScalars ℝ).comp L‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg fun k _ => norm_nonneg _)
  intro z
  calc
    _ ≤ ∑ k, ‖L z k‖ := euclidean_norm_le_sum_coordinates _
    _ ≤ ∑ k, ‖((EuclideanSpace.proj k).restrictScalars ℝ).comp L‖ * ‖z‖ := by
      apply Finset.sum_le_sum
      intro k _
      exact (((EuclideanSpace.proj k).restrictScalars ℝ).comp L).le_opNorm z
    _ = _ := by rw [Finset.sum_mul]

theorem columnVector_fderiv_norm_le (v : Fin n → X n → ℂ) (hv : ∀ k, ContDiff ℝ ∞ (v k))
    (x : X n) : ‖fderiv ℝ (columnVector v) x‖ ≤ ∑ k, ‖fderiv ℝ (v k) x‖ := by
  have hV := (contDiff_columnVector v hv).differentiable (by simp) x
  have hCoord (k : Fin n) : ((EuclideanSpace.proj k).restrictScalars ℝ).comp (fderiv ℝ (columnVector v) x) =
      fderiv ℝ (v k) x := by
    have h := (((EuclideanSpace.proj k).restrictScalars ℝ).hasFDerivAt.comp x hV.hasFDerivAt).fderiv
    have he : (fun y => columnVector v y k) = v k := funext fun y => columnVector_apply v y k
    change fderiv ℝ (fun y => columnVector v y k) x = _ at h
    rw [he] at h
    exact h.symm
  exact (norm_real_clm_le_sum_coordinates _).trans_eq (by simp only [hCoord])

theorem fderiv_coordinate (x : X n) (k : Fin n) :
    fderiv ℝ (fun y : X n => y k) x = (EuclideanSpace.proj k).restrictScalars ℝ :=
  (((EuclideanSpace.proj k).restrictScalars ℝ).hasFDerivAt (x := x)).fderiv

theorem wirt_coordinate (x z : X n) (k : Fin n) :
    Yau.wirt (fun y : X n => y k) x z = z k := by
  rw [Yau.wirt, fderiv_coordinate]
  change (1 / 2 : ℂ) * (z k - Complex.I * (Complex.I * z k)) = z k
  rw [← mul_assoc, Complex.I_mul_I]
  ring

theorem wirtBar_coordinate (x z : X n) (k : Fin n) :
    Yau.wirtBar (fun y : X n => y k) x z = 0 := by
  rw [Yau.wirtBar, fderiv_coordinate]
  change (1 / 2 : ℂ) * (z k + Complex.I * (Complex.I * z k)) = 0
  rw [← mul_assoc, Complex.I_mul_I]
  ring

theorem dbarA_coordinate (A : X n → Matrix (Fin n) (Fin n) ℂ) (x : X n) (i k : Fin n) :
    dbarA A i (fun y => y k) x = A x i k := by
  classical
  simp [dbarA, wirtBar_coordinate, wirt_coordinate, Yau.stdVec, PiLp.single_apply,
    Pi.single_apply, eq_comm]

def correctedCoordinates (v : Fin n → X n → ℂ) (x : X n) : X n := x - columnVector v x

theorem contDiff_correctedCoordinates (v : Fin n → X n → ℂ) (hv : ∀ k, ContDiff ℝ ∞ (v k)) :
    ContDiff ℝ ∞ (correctedCoordinates v) := contDiff_id.sub (contDiff_columnVector v hv)

theorem correctedCoordinates_dbar_eq_zero (v : Fin n → X n → ℂ) (hv : ∀ k, ContDiff ℝ ∞ (v k))
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (x : X n)
    (heq : ∀ i k, dbarA A i (v k) x = A x i k) (i k : Fin n) :
    dbarA A i (fun y => correctedCoordinates v y k) x = 0 := by
  have hFun : (fun y => correctedCoordinates v y k) = fun y => y k - v k y := by
    funext y
    simp only [correctedCoordinates, PiLp.sub_apply, columnVector_apply]
  rw [hFun]
  change dbarA A i ((fun y : X n => y k) - v k) x = 0
  have hProj : DifferentiableAt ℝ (fun y : X n => y k) x :=
    (((EuclideanSpace.proj k).restrictScalars ℝ).hasFDerivAt (x := x)).differentiableAt
  rw [dbarA_sub A i (f := fun y : X n => y k) (g := v k) hProj
    ((hv k).differentiable (by simp) x), dbarA_coordinate, heq, sub_self]

theorem correctedCoordinates_fderiv_close (v : Fin n → X n → ℂ) (hv : ∀ k, ContDiff ℝ ∞ (v k))
    (x : X n) {b : ℝ} (hb : ∀ k, ‖fderiv ℝ (v k) x‖ ≤ b) :
    ‖fderiv ℝ (correctedCoordinates v) x - ContinuousLinearMap.id ℝ (X n)‖ ≤ (n : ℝ) * b := by
  have hV := (contDiff_columnVector v hv).differentiable (by simp) x
  have hDF : fderiv ℝ (correctedCoordinates v) x - ContinuousLinearMap.id ℝ (X n) =
      -fderiv ℝ (columnVector v) x := by
    change fderiv ℝ (fun y : X n => y - columnVector v y) x - _ = _
    rw [fderiv_fun_sub (f := fun y : X n => y) (g := columnVector v) differentiableAt_id hV, fderiv_fun_id]
    abel
  rw [hDF, norm_neg]
  exact (columnVector_fderiv_norm_le v hv x).trans
    ((Finset.sum_le_sum fun k _ => hb k).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]))

end Yau.LeafProofs.L21Aux
