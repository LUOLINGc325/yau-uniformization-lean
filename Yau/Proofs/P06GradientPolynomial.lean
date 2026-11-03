import Yau.Proofs.P06GradientPolynomialGram
import Yau.Proofs.P06GradientPolynomialChain
import Yau.Proofs.P06RelativePolynomial
import Yau.Proofs.P06RelativeMatrixPairing

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder InnerProductSpace
namespace Yau.NodeProofs.P06Aux.GradientPoly
open Yau Yau.LeafProofs G04Aux L12Aux Clip FiberPoly
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem relativeMatrixHS_smul (H D : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    relativeMatrixHS H (r • D) = r • relativeMatrixHS H D := by
  simp only [relativeMatrixHS, metricWhiten_smul]
  rfl

theorem relativeMatrixHS_sum {ι : Type*} (H : Matrix (Fin n) (Fin n) ℂ)
    (s : Finset ι) (D : ι → Matrix (Fin n) (Fin n) ℂ) :
    relativeMatrixHS H (∑ i ∈ s, D i) = ∑ i ∈ s, relativeMatrixHS H (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, relativeMatrixHS, metricWhiten_zero]; rfl
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, relativeMatrixHS, metricWhiten_add] at *
    change matrixToHS (metricWhiten H (D i)) +
        matrixToHS (metricWhiten H (∑ j ∈ s, D j)) = _
    rw [ih]

/-- Exact original gradient energy, expressed in the same Hermitian
Hilbert--Schmidt metric that contracts the polynomial differential. -/
theorem gradientPair_eq_gram (g : SmoothMetric M) (hK : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A) (x : M.Carrier) :
    P06Weitzenbock.gradientPair g.form A A x =
      ∑ a, ∑ b, (realMetricFn g.form x (chartPt x x))⁻¹ a b *
        inner ℝ
          (relativeMatrixHS (gMat g.form x) (covariantHermitianMatrix g.form A x (chartPt x x) a))
          (relativeMatrixHS (gMat g.form x) (covariantHermitianMatrix g.form A x (chartPt x x) b)) := by
  unfold P06Weitzenbock.gradientPair P06Weitzenbock.chartGradientPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hinner := relativeMatrixHS_inner (gMat g.form x)
    (covariantHermitianMatrix g.form A x (chartPt x x) a)
    (covariantHermitianMatrix g.form A x (chartPt x x) b)
    (L12Aux.hMat_posDef g.form x (chartPt x x) (mem_extChartAt_target x))
    (covariantHermitianMatrix_hermitian g hK A hA h11 x (mem_extChartAt_target x) a)
  rw [hinner]
  calc
    _ = (realMetricFn g.form x (chartPt x x))⁻¹ a b *
      ((1 / 2 : ℝ) * L03.tensorCoefficientPairing (realMetricFn g.form x (chartPt x x))⁻¹
        (fun I => covariantComponents g.form x (formComponents A x) (chartPt x x) a I)
        (fun I => covariantComponents g.form x (formComponents A x) (chartPt x x) b I)) := by ring
    _ = _ := congrArg (fun t => (realMetricFn g.form x (chartPt x x))⁻¹ a b * t)
      (covariant_pairing_eq_trace g hK A A hA hA h11 h11 x (mem_extChartAt_target x) a b)

theorem weighted_polynomialVariation_sum {ι : Type*} [Fintype ι]
    (H C : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℝ)
    (D : ι → Matrix (Fin n) (Fin n) ℂ) (r : ι → ℝ) :
    (∑ a, r a • (H * polynomialVariation p (H⁻¹ * C) (H⁻¹ * D a))) =
      H * polynomialVariation p (H⁻¹ * C) (H⁻¹ * ∑ a, r a • D a) := by
  simp only [Matrix.mul_sum, Matrix.mul_smul, polynomialVariation_sum,
    polynomialVariation_smul]

/-- A real polynomial whose derivative contracts on the spectrum at x
contracts the actual original gradientPair at x. All metric factors and
the original 1/2! are retained; no closedness or curvature assumption is used. -/
theorem polynomialForm_gradientPair_le (g : SmoothMetric M) (hK : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (p : Polynomial ℝ) (x : M.Carrier) {R : ℝ}
    (hlam : ∀ i,
      (metricWhiten_hermitian (gMat g.form x) (formHermitianMatrix A x)
        ((representsSelf A h11).2 x)).eigenvalues i ∈ Set.Icc (-R) R)
    (hder : ∀ r ∈ Set.Icc (-R) R, |p.derivative.eval r| ≤ 1) :
    P06Weitzenbock.gradientPair g.form (polynomialForm g.form A h11 p)
        (polynomialForm g.form A h11 p) x ≤
      P06Weitzenbock.gradientPair g.form A A x := by
  rw [gradientPair_eq_gram g hK _ (polynomialForm_smooth g A hA h11 p)
      (polynomialForm_oneOne g.form A h11 p) x,
    gradientPair_eq_gram g hK A hA h11 x]
  apply inverse_metric_gram_contraction _
    (L12Aux.realMetricFn_posDef g.form x (chartPt x x) (mem_extChartAt_target x))
  intro r
  simp only [← relativeMatrixHS_smul, ← relativeMatrixHS_sum,
    covariantHermitianMatrix_polynomial g hK A hA h11 p x,
    weighted_polynomialVariation_sum]
  exact relative_polynomialVariation_energy_le _ _ _
    (L12Aux.hMat_posDef g.form x (chartPt x x) (mem_extChartAt_target x))
    ((representsSelf A h11).2 x) p hlam hder

end Yau.NodeProofs.P06Aux.GradientPoly
