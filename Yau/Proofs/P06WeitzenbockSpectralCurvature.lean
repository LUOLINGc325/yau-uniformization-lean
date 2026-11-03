import Yau.Proofs.P06WeitzenbockReaction
import Yau.Proofs.P06WeitzenbockHermitian

noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.P06Weitzenbock
open Yau G01Aux
variable {n : ℕ}

def curvatureContraction (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (B D : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * B i j * D k l

theorem curvatureContraction_eq_trace (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (B D : Matrix (Fin n) (Fin n) ℂ) :
    curvatureContraction R B D = Matrix.trace (B * finiteCurvatureAction R D) := by
  simp only [curvatureContraction, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    finiteCurvatureAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem curvatureContraction_comm (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hR : ∀ i j k l, R i j k l = R k l i j) (B D : Matrix (Fin n) (Fin n) ℂ) :
    curvatureContraction R B D = curvatureContraction R D B := by
  rw [curvatureContraction_eq_trace, curvatureContraction_eq_trace,
    finiteCurvatureAction_trace_selfadjoint R hR]

theorem curvatureContraction_add_left (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (B D V : Matrix (Fin n) (Fin n) ℂ) :
    curvatureContraction R (B + D) V = curvatureContraction R B V + curvatureContraction R D V := by
  simp only [curvatureContraction, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem curvatureContraction_add_right (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (B D V : Matrix (Fin n) (Fin n) ℂ) :
    curvatureContraction R V (B + D) = curvatureContraction R V B + curvatureContraction R V D := by
  simp only [curvatureContraction, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem curvatureContraction_smul_left (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (B D : Matrix (Fin n) (Fin n) ℂ) (v : ℂ) :
    curvatureContraction R (v • B) D = v * curvatureContraction R B D := by
  simp only [curvatureContraction, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem curvatureContraction_smul_right (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (B D : Matrix (Fin n) (Fin n) ℂ) (v : ℂ) :
    curvatureContraction R B (v • D) = v * curvatureContraction R B D := by
  simp only [curvatureContraction, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem curvatureContraction_sum_left {ι : Type*} (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (s : Finset ι) (B : ι → Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin n) (Fin n) ℂ) :
    curvatureContraction R (∑ i ∈ s, B i) D = ∑ i ∈ s, curvatureContraction R (B i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [curvatureContraction]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, curvatureContraction_add_left, ih]

theorem curvatureContraction_sum_right {ι : Type*} (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (s : Finset ι) (B : Matrix (Fin n) (Fin n) ℂ) (D : ι → Matrix (Fin n) (Fin n) ℂ) :
    curvatureContraction R B (∑ i ∈ s, D i) = ∑ i ∈ s, curvatureContraction R B (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [curvatureContraction]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, curvatureContraction_add_right, ih]

def columnRankOne (E : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => E a i * star (E b i)

theorem spectralMatrix_eq_sum (E : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    E * Matrix.diagonal v * Eᴴ = ∑ i, v i • columnRankOne E i := by
  ext a b
  change (∑ i, (E * Matrix.diagonal v) a i * star (E b i)) = _
  simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, columnRankOne]
  apply Finset.sum_congr rfl
  intro i _
  ring

def frameCurvatureCoefficient (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (E : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ℂ :=
  curvatureContraction R (columnRankOne E i) (columnRankOne E j)

theorem curvatureContraction_spectral (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (E : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    curvatureContraction R (E * Matrix.diagonal v * Eᴴ) (E * Matrix.diagonal w * Eᴴ) =
      ∑ i, ∑ j, v i * w j * frameCurvatureCoefficient R E i j := by
  rw [spectralMatrix_eq_sum, spectralMatrix_eq_sum, curvatureContraction_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [curvatureContraction_smul_left, curvatureContraction_sum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [curvatureContraction_smul_right]
  unfold frameCurvatureCoefficient
  ring

theorem frameCurvatureCoefficient_comm (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hR : ∀ i j k l, R i j k l = R k l i j)
    (E : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    frameCurvatureCoefficient R E i j = frameCurvatureCoefficient R E j i :=
  curvatureContraction_comm R hR _ _

theorem curvatureContraction_spectral_re (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (E : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℝ) :
    (curvatureContraction R (E * Matrix.diagonal (fun i => (v i : ℂ)) * Eᴴ)
      (E * Matrix.diagonal (fun i => (w i : ℂ)) * Eᴴ)).re =
      ∑ i, ∑ j, v i * w j * (frameCurvatureCoefficient R E i j).re := by
  rw [curvatureContraction_spectral]
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]

def matrixColumn (E : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ComplexVector n :=
  WithLp.toLp 2 (fun a => E a i)

variable {M : ComplexManifold n}

theorem frameCurvatureCoefficient_eq_bisectionalForm (h : HermitianField M)
    (x : M.Carrier) (E : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (frameCurvatureCoefficient (chernCurvature h x) E i j).re =
      bisectionalForm h x (matrixColumn E i) (matrixColumn E j) := by
  unfold frameCurvatureCoefficient curvatureContraction columnRankOne bisectionalForm
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp only [matrixColumn, PiLp.toLp_apply]
  ring

theorem frameCurvatureCoefficient_eq_paperHBC (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (E : Matrix (Fin n) (Fin n) ℂ)
    (hunit : ∀ i, hermitianNormSq (h x) (chartVec x x (matrixColumn E i)) = 1)
    (i j : Fin n) :
    (frameCurvatureCoefficient (chernCurvature h x) E i j).re =
      paperHolomorphicBisectionalCurvature h x (chartVec x x (matrixColumn E i))
        (chartVec x x (matrixColumn E j)) := by
  rw [hbc_unit_norm_eq_chern h hs hk x _ _ (hunit i) (hunit j)]
  rw [show tangentCoordinates x (chartVec x x (matrixColumn E i)) = matrixColumn E i from
    Yau.LeafProofs.L12Aux.tangentCoords_chartVec x x (mem_extChartAt_source x) _,
    show tangentCoordinates x (chartVec x x (matrixColumn E j)) = matrixColumn E j from
      Yau.LeafProofs.L12Aux.tangentCoords_chartVec x x (mem_extChartAt_source x) _]
  exact frameCurvatureCoefficient_eq_bisectionalForm h x E i j

end Yau.NodeProofs.P06Weitzenbock
