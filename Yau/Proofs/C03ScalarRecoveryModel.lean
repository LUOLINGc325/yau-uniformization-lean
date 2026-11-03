import Yau.Proofs.C03FlatComplete
import Yau.Proofs.P04LocalCanonicalRepresentative
import Yau.Proofs.P03HolomorphicCorrection

/-! Genuine global scalar coefficients and the exact weighted Euclidean norm bridge. -/
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff Manifold Matrix ENNReal
namespace Yau.Proofs.C03Aux.ScalarRecovery
open Yau Yau.LeafProofs L14Aux Yau.Proofs.P04Aux BundleDbar
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

def scalarCoefficient (hn : 1 ≤ n)
    (u : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 0)
    (z : ComplexVector n) : ℂ :=
  coefficients (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
    u (0 : ComplexVector n) z Fin.elim0 0

theorem source_chartInv (hn : 1 ≤ n) (a z : ComplexVector n) :
    chartInv (M := ComplexEuclideanManifold n hn) a z = z := by
  change (extChartAt (ComplexModel n) (a : ComplexVector n)).symm z = z
  rw [extChartAt_model_space_eq_id]
  rfl

theorem source_localDomain (hn : 1 ≤ n) (a : ComplexVector n) :
    localDomain (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn)) a = univ := by
  rw [coefficient_localDomain]
  change (extChartAt (ComplexModel n) (a : ComplexVector n)).target = univ
  rw [extChartAt_model_space_eq_id]
  rfl

theorem source_bundleChartSource (hn : 1 ≤ n) (a : ComplexVector n) :
    bundleChartSource (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn)) a = univ := by
  rw [coefficient_bundleChartSource]
  change (extChartAt (ComplexModel n) (a : ComplexVector n)).source = univ
  rw [extChartAt_model_space_eq_id]
  rfl

theorem scalarCoefficient_sub (hn : 1 ≤ n)
    (u v : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 0) :
    scalarCoefficient hn (subForm _ u v) = scalarCoefficient hn u - scalarCoefficient hn v := by
  funext z
  exact Yau.NodeProofs.P03Aux.coefficients_subForm _ u v _ z _ _

theorem scalarCoefficient_differentiable (hn : 1 ≤ n)
    (w : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 0)
    (hw : HolomorphicTopForm (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn)) w) :
    Differentiable ℂ (scalarCoefficient hn w) := by
  have H := hw (0 : ComplexVector n) (0 : Fin 1)
  rw [source_localDomain hn] at H
  exact differentiableOn_univ.mp H

theorem chartTopNorm_scalar (hn : 1 ≤ n)
    (u : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 0)
    (z : ComplexVector n) :
    chartTopCoefficientNormSq (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn)) flatMetric u
      (0 : ComplexVector n) z = ‖scalarCoefficient hn u z‖ ^ 2 := by
  simp only [chartTopCoefficientNormSq, flat_metricMatrix, Fin.sum_univ_one,
    Matrix.one_apply, ite_true, mul_one]
  change (star (scalarCoefficient hn u z) * scalarCoefficient hn u z).re = _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem weightedNormSq_scalar (hn : 1 ≤ n)
    (u : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) 0)
    (hu : LocallyL2 (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn)) u)
    (ψ : ComplexVector n → ℝ) (hψ : SmoothFn (M := ComplexEuclideanManifold n hn) ψ) :
    weightedNormSq (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric
      (FlatComplete.euclideanVolume n hn) ψ u =
      ENNReal.ofReal ((2 : ℝ) ^ n) *
        ∫⁻ z, ENNReal.ofReal (‖scalarCoefficient hn u z‖ ^ 2 * Real.exp (-ψ z))
          ∂(volume : Measure (ComplexVector n)) := by
  have H := weighted_top_chart_integral
    (CanonicalCoefficients (ComplexEuclideanManifold n hn))
    (FlatComplete.euclideanCompleteMetric n hn) (FlatComplete.euclideanVolume n hn)
    (FlatComplete.euclideanCompleteMetric_volume n hn) flatMetric flatMetric_smooth
    ψ hψ u hu (0 : ComplexVector n)
  rw [source_bundleChartSource hn, source_localDomain hn, Measure.restrict_univ,
    Measure.restrict_univ, lebesgueC_eq_volume] at H
  simpa only [weightedNormSq, chartTopNorm_scalar, source_chartInv] using H

end Yau.Proofs.C03Aux.ScalarRecovery
