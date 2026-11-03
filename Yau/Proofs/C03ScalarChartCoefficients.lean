import Yau.Proofs.C03ScalarCoefficients
import Yau.Proofs.C03ChernGaugeFlat

/-! Every actual Euclidean chart uses the same coefficients of the
trivial line tensor, including the point-centered chart used by L14. -/

noncomputable section
open scoped Manifold
namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs Yau.Proofs.P04Aux BundleDbar
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem scalar_coefficients_chart_independent (hn : 1 ≤ n) {q : ℕ}
    (u : NQForm (CanonicalCoefficients (ComplexEuclideanManifold n hn)) q)
    (a b z : ComplexVector n) (I : Fin q → Fin n) (α : Fin 1) :
    coefficients (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn)) u a z I α =
      coefficients (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn)) u b z I α := by
  have hinv (x : ComplexVector n) : chartInv (M := ComplexEuclideanManifold n hn) x z = z :=
    ChernGauge.flat_chartInv hn x z
  simp only [coefficients, coefficient_localTriv,
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply,
    chartVec_euclidean]
  dsimp only [chartInv]
  rw [extChartAt_model_space_eq_id, extChartAt_model_space_eq_id]

theorem scalarSeedDbar_centered_coefficient (hn : 1 ≤ n) (f : ComplexVector n → ℂ)
    (z : ComplexVector n) (i : Fin n) :
    coefficients (r := 1) (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (scalarSeedDbar hn f) z (chartPt (M := ComplexEuclideanManifold n hn) z z)
      (fun _ => i) 0 = wirtBar f z (stdVec i) := by
  rw [ChernGauge.flat_chartPt hn,
    scalar_coefficients_chart_independent hn _ z (0 : ComplexVector n),
    scalarSeedDbar_coefficient]

end Yau.Proofs.C03Aux
