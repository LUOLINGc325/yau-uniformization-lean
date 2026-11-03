import Yau.Proofs.P06WeitzenbockEndomorphism
import Yau.Proofs.P06SpectralClipVariation

noncomputable section
open scoped Matrix ContDiff Topology
namespace Yau.NodeProofs.P06Aux.FiberPoly
open Yau Yau.LeafProofs L12Aux

set_option backward.isDefEq.respectTransparency false

/-- The finite coefficient expansion used in every polynomial calculation below. -/
theorem aeval_sum {B : Type*} [Ring B] [Algebra ℝ B]
    (p : Polynomial ℝ) (S : B) :
    Polynomial.aeval S p = ∑ m ∈ p.support, p.coeff m • S ^ m := by
  simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype ι] [DecidableEq ι]

/-- Entrywise differentiability of a finite matrix power. -/
theorem entries_differentiable_pow {S : E → Matrix ι ι ℝ} {z : E}
    (hS : ∀ i j, DifferentiableAt ℝ (fun w => S w i j) z) (m : ℕ) :
    ∀ i j, DifferentiableAt ℝ (fun w => (S w ^ m) i j) z := by
  induction m with
  | zero => intro i j; simpa only [pow_zero] using
      (differentiableAt_const ((1 : Matrix ι ι ℝ) i j) : DifferentiableAt ℝ
        (fun _ : E => (1 : Matrix ι ι ℝ) i j) z)
  | succ m hm => simpa only [pow_succ] using matrix_entries_differentiable_mul hm hS

/-- Actual entry derivatives obey the full noncommutative power rule. -/
theorem directional_pow {S : E → Matrix ι ι ℝ} {z : E}
    (hS : ∀ i j, DifferentiableAt ℝ (fun w => S w i j) z) (v : E) (m : ℕ) :
    matrixDirectionalDerivative (fun w => S w ^ m) z v =
      Clip.powerVariation (S z) (matrixDirectionalDerivative S z v) m := by
  induction m with
  | zero => ext i j; simp [matrixDirectionalDerivative, Clip.powerVariation]
  | succ m hm =>
      simp only [pow_succ]
      rw [matrixDirectionalDerivative_mul (entries_differentiable_pow hS m) hS, hm]
      rfl

/-- Entrywise differentiability follows from the finite coefficient expansion. -/
theorem entries_differentiable_aeval {S : E → Matrix ι ι ℝ} {z : E}
    (hS : ∀ i j, DifferentiableAt ℝ (fun w => S w i j) z) (p : Polynomial ℝ) :
    ∀ i j, DifferentiableAt ℝ (fun w => Polynomial.aeval (S w) p i j) z := by
  intro i j
  simp only [aeval_sum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply DifferentiableAt.fun_sum
  intro m hm
  exact (entries_differentiable_pow hS m i j).const_mul _

/-- Polynomial differentiation here is differentiation of each actual matrix entry. -/
theorem directional_aeval {S : E → Matrix ι ι ℝ} {z : E}
    (hS : ∀ i j, DifferentiableAt ℝ (fun w => S w i j) z) (v : E)
    (p : Polynomial ℝ) :
    matrixDirectionalDerivative (fun w => Polynomial.aeval (S w) p) z v =
      Clip.polynomialVariation p (S z) (matrixDirectionalDerivative S z v) := by
  ext i j
  simp only [matrixDirectionalDerivative, aeval_sum, Clip.polynomialVariation,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fderiv_fun_sum (fun m hm => (entries_differentiable_pow hS m i j).const_mul _)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro m hm
  rw [fderiv_const_mul (entries_differentiable_pow hS m i j)]
  change p.coeff m * matrixDirectionalDerivative (fun w => S w ^ m) z v i j = _
  rw [directional_pow hS]

/-- The connection commutator is itself a polynomial differential. -/
theorem polynomialVariation_commutator (p : Polynomial ℝ) (S Γ : Matrix ι ι ℝ) :
    Clip.polynomialVariation p S (Γ * S - S * Γ) =
      Γ * Polynomial.aeval S p - Polynomial.aeval S p * Γ := by
  classical
  simp only [Clip.polynomialVariation, Clip.powerVariation_commutator, aeval_sum,
    Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul, smul_sub, Finset.sum_sub_distrib,
    Matrix.mul_smul, Matrix.smul_mul]

/-- The full derivative with a connection acts by the same polynomial variation. -/
theorem covariant_aeval {S : E → Matrix ι ι ℝ} {z : E}
    (hS : ∀ i j, DifferentiableAt ℝ (fun w => S w i j) z)
    (v : E) (p : Polynomial ℝ) (Γ : Matrix ι ι ℝ) :
    matrixDirectionalDerivative (fun w => Polynomial.aeval (S w) p) z v +
      Γ * Polynomial.aeval (S z) p - Polynomial.aeval (S z) p * Γ =
    Clip.polynomialVariation p (S z)
      (matrixDirectionalDerivative S z v + Γ * S z - S z * Γ) := by
  have hadd (D F : Matrix ι ι ℝ) : Clip.polynomialVariation p (S z) (D + F) =
      Clip.polynomialVariation p (S z) D + Clip.polynomialVariation p (S z) F := by
    simp only [Clip.polynomialVariation, Clip.powerVariation_add, smul_add,
      Finset.sum_add_distrib]
  rw [show matrixDirectionalDerivative S z v + Γ * S z - S z * Γ =
    matrixDirectionalDerivative S z v + (Γ * S z - S z * Γ) by abel,
    hadd, polynomialVariation_commutator, directional_aeval hS]
  abel

variable {n : ℕ} {M : ComplexManifold n}

/-- This bridge already uses the genuine two-form covariant derivative of the input. -/
theorem relative_polynomial_covariant_derivative (g : SmoothMetric M) (hK : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (a : RIdx n) (p : Polynomial ℝ) :
    matrixDirectionalDerivative
        (fun w => Polynomial.aeval (P06Weitzenbock.relativeEndomorphism g.form A c w) p)
        z (realVec a) +
      connectionMatrix g.form c z a *
        Polynomial.aeval (P06Weitzenbock.relativeEndomorphism g.form A c z) p -
      Polynomial.aeval (P06Weitzenbock.relativeEndomorphism g.form A c z) p *
        connectionMatrix g.form c z a =
    Clip.polynomialVariation p (P06Weitzenbock.relativeEndomorphism g.form A c z)
      ((realMetricFn g.form c z)⁻¹ * P06Weitzenbock.covariantTwoMatrix g.form A c z a * jMatrix n) := by
  have hs := L12Aux.metricSmooth_of_smoothMetric g
  have hH (i j : RIdx n) : DifferentiableAt ℝ
      (fun w => (realMetricFn g.form c w)⁻¹ i j) z :=
    ((L23Aux.realMetricFn_inverse_contDiffOn g.form hs c i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hC (i j : RIdx n) : DifferentiableAt ℝ
      (fun w => G04Aux.chartFormMatrix A c w i j) z :=
    ((hA c ![i,j]).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hS : ∀ i j, DifferentiableAt ℝ
      (fun w => P06Weitzenbock.relativeEndomorphism g.form A c w i j) z :=
    matrix_entries_differentiable_mul (matrix_entries_differentiable_mul hH hC)
      (fun i j => differentiableAt_const (jMatrix n i j))
  rw [covariant_aeval hS, P06Weitzenbock.relativeEndomorphism_covariant_derivative
    g.form hs hK A hA c hz a]

end Yau.NodeProofs.P06Aux.FiberPoly

namespace Yau.NodeProofs.P06Aux.FiberPoly
open Yau Yau.LeafProofs L12Aux
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype ι] [DecidableEq ι]

/-- Smooth matrix multiplication is checked on its actual finite entries. -/
theorem entries_contDiffOn_mul {A B : E → Matrix ι ι ℝ} {U : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun w => A w i j) U)
    (hB : ∀ i j, ContDiffOn ℝ ∞ (fun w => B w i j) U) :
    ∀ i j, ContDiffOn ℝ ∞ (fun w => (A w * B w) i j) U := by
  intro i j
  apply ContDiffOn.sum
  intro k hk
  exact (hA i k).mul (hB k j)

theorem entries_contDiffOn_pow {S : E → Matrix ι ι ℝ} {U : Set E}
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun w => S w i j) U) (m : ℕ) :
    ∀ i j, ContDiffOn ℝ ∞ (fun w => (S w ^ m) i j) U := by
  induction m with
  | zero => intro i j; simpa only [pow_zero] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (1 : Matrix ι ι ℝ) i j) U)
  | succ m hm => simpa only [pow_succ] using entries_contDiffOn_mul hm hS

theorem entries_contDiffOn_aeval {S : E → Matrix ι ι ℝ} {U : Set E}
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun w => S w i j) U) (p : Polynomial ℝ) :
    ∀ i j, ContDiffOn ℝ ∞ (fun w => Polynomial.aeval (S w) p i j) U := by
  intro i j
  simp only [aeval_sum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply ContDiffOn.sum
  intro m hm
  exact contDiffOn_const.mul (entries_contDiffOn_pow hS m i j)

end Yau.NodeProofs.P06Aux.FiberPoly
