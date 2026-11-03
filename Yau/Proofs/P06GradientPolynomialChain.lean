import Yau.Proofs.P06GradientPolynomialMetric
import Yau.Proofs.P06FiberPolynomial

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux.GradientPoly
open Yau Yau.LeafProofs G04Aux L12Aux Clip FiberPoly
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem rawReal_injective (n : ℕ) : Function.Injective (G01Aux.rawReal (n := n)) := by
  intro A B h
  ext i j
  apply Complex.ext
  · simpa [G01Aux.rawReal] using congrArg (fun X => X (i,0) (j,0)) h
  · have hi := congrArg (fun X => X (i,0) (j,1)) h
    simpa [G01Aux.rawReal] using hi

theorem rawReal_smul (r : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    G01Aux.rawReal (r • A) = r • G01Aux.rawReal A := by
  ext a b
  simp only [G01Aux.rawReal, Matrix.smul_apply, Complex.smul_re, Complex.smul_im,
    smul_eq_mul]
  split_ifs <;> ring

theorem rawReal_pow (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    G01Aux.rawReal (A ^ m) = G01Aux.rawReal A ^ m := by
  induction m with
  | zero => exact G01Aux.rawReal_one
  | succ m hm => rw [pow_succ, G01Aux.rawReal_mul, hm, pow_succ]

theorem powerVariation_raw (S D : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    G01Aux.rawReal (powerVariation S D m) =
      powerVariation (G01Aux.rawReal S) (G01Aux.rawReal D) m := by
  induction m with
  | zero => exact G01Aux.rawReal_zero
  | succ m hm =>
    simp only [powerVariation, G01Aux.rawReal_add, G01Aux.rawReal_mul, rawReal_pow, hm]

theorem polynomialVariation_raw (p : Polynomial ℝ) (S D : Matrix (Fin n) (Fin n) ℂ) :
    G01Aux.rawReal (polynomialVariation p S D) =
      polynomialVariation p (G01Aux.rawReal S) (G01Aux.rawReal D) := by
  simp only [polynomialVariation, G01Aux.rawReal_sum, rawReal_smul, powerVariation_raw]

theorem covariant_relative_raw (g : SmoothMetric M) (hK : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a : RIdx n) :
    (realMetricFn g.form c z)⁻¹ *
        P06Weitzenbock.covariantTwoMatrix g.form A c z a * jMatrix n =
      G01Aux.rawReal ((hMat g.form c z)⁻¹ * covariantHermitianMatrix g.form A c z a) := by
  rw [covariantTwoMatrix_eq_raw g hK A hA h11 c hz a,
    G01Aux.realMetricFn_inverse_eq g.form c z hz]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num only [show (1 / 2 : ℝ) * (-2) = -1 by norm_num, neg_one_smul]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, jMatrix_sq]
  simp only [Matrix.mul_neg, Matrix.mul_one, neg_neg]
  rw [← G01Aux.rawReal_mul]

/-- The actual covariant polynomial chain rule in the complex Hermitian
matrix representation of each real derivative direction. -/
theorem covariantHermitianMatrix_polynomial (g : SmoothMetric M) (hK : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (p : Polynomial ℝ) (x : M.Carrier) (a : RIdx n) :
    covariantHermitianMatrix g.form (polynomialForm g.form A h11 p) x (chartPt x x) a =
      gMat g.form x * polynomialVariation p ((gMat g.form x)⁻¹ * formHermitianMatrix A x)
        ((gMat g.form x)⁻¹ * covariantHermitianMatrix g.form A x (chartPt x x) a) := by
  have he := polynomialForm_covariant_chain g hK A hA h11 p x (mem_extChartAt_target x) a
  rw [covariant_relative_raw g hK _ (polynomialForm_smooth g A hA h11 p)
      (polynomialForm_oneOne g.form A h11 p) x (mem_extChartAt_target x) a,
    covariant_relative_raw g hK A hA h11 x (mem_extChartAt_target x) a] at he
  change G01Aux.rawReal ((gMat g.form x)⁻¹ *
      covariantHermitianMatrix g.form (polynomialForm g.form A h11 p) x (chartPt x x) a) =
    polynomialVariation p (P06Weitzenbock.relativeEndomorphism g.form A x (chartPt x x))
      (G01Aux.rawReal ((gMat g.form x)⁻¹ * covariantHermitianMatrix g.form A x (chartPt x x) a)) at he
  rw [P06Weitzenbock.relativeEndomorphism_center_eq_raw g.form A h11 x,
    ← polynomialVariation_raw] at he
  have hc := rawReal_injective n he
  have hH : IsUnit (gMat g.form x).det :=
    (L12Aux.hMat_posDef g.form x (chartPt x x) (mem_extChartAt_target x)).isUnit.map Matrix.detMonoidHom
  calc
    _ = gMat g.form x * ((gMat g.form x)⁻¹ *
        covariantHermitianMatrix g.form (polynomialForm g.form A h11 p) x (chartPt x x) a) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hH, Matrix.one_mul]
    _ = _ := congrArg (fun X => gMat g.form x * X) hc

theorem powerVariation_smul (S D : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (m : ℕ) :
    powerVariation S (r • D) m = r • powerVariation S D m := by
  induction m with
  | zero => simp only [powerVariation, smul_zero]
  | succ m hm =>
    simp only [powerVariation, hm, Matrix.smul_mul, Matrix.mul_smul, smul_add]

theorem polynomialVariation_smul (p : Polynomial ℝ)
    (S D : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    polynomialVariation p S (r • D) = r • polynomialVariation p S D := by
  simp only [polynomialVariation, powerVariation_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact smul_comm _ _ _

theorem polynomialVariation_add (p : Polynomial ℝ)
    (S D E : Matrix (Fin n) (Fin n) ℂ) :
    polynomialVariation p S (D + E) = polynomialVariation p S D + polynomialVariation p S E := by
  simp only [polynomialVariation, powerVariation_add, smul_add, Finset.sum_add_distrib]

theorem polynomialVariation_sum {ι : Type*} (p : Polynomial ℝ)
    (S : Matrix (Fin n) (Fin n) ℂ) (s : Finset ι) (D : ι → Matrix (Fin n) (Fin n) ℂ) :
    polynomialVariation p S (∑ i ∈ s, D i) = ∑ i ∈ s, polynomialVariation p S (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialVariation, powerVariation_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, polynomialVariation_add, ih]

end Yau.NodeProofs.P06Aux.GradientPoly
