import Yau.Proofs.C02NormalConnection
import Yau.Proofs.C02NormalDifferentialCoords
import Yau.Proofs.C02OperatorFactorDerivative

/-! Torsion freeness for the actual differential and radial frame connection,
obtained by differentiating Q B = D phi in a fixed valid target chart. -/

noncomputable section
open Set Filter
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalConnection_torsion (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x u v : ComplexVector n) :
    fderiv ℝ (normalDifferential g p U hU) x u v - fderiv ℝ (normalDifferential g p U hU) x v u +
      normalConnection g p U hU x u (normalDifferential g p U hU x v) -
      normalConnection g p U hU x v (normalDifferential g p U hU x u) = 0 := by
  letI := manifold_realSmooth M
  let c := normalRealMap g p U x
  let φ := normalCoordinateMap g p U c
  let Q := normalParallelCoefficients g p U hU c
  let B := normalDifferential g p U hU
  let A := normalConnection g p U hU
  have hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hO := (normalRealMap_smooth g p U hU).continuous.continuousAt.preimage_mem_nhds
    ((chartAt (ComplexVector n) c).open_source.mem_nhds hx)
  have hQ : DifferentiableAt ℝ Q x :=
    ((normalParallelCoefficients_smooth g p U hU c).contDiffAt hO).differentiableAt (by simp)
  have hB : DifferentiableAt ℝ B x := (normalDifferential_smooth g p U hU).differentiable (by simp) x
  have hφ : ContDiffAt ℝ 2 φ x :=
    ((normalCoordinateMap_smooth g p U hU c).contDiffAt hO).of_le (by simp)
  have heq : (fun y => (Q y).comp (B y)) =ᶠ[𝓝 x] fderiv ℝ φ := by
    filter_upwards [hO] with y hy
    apply ContinuousLinearMap.ext
    intro w
    exact normalDifferential_coords g p U hU c y w hy
  have hDuv := operator_factor_fderiv hQ hB heq u v
  have hDvu := operator_factor_fderiv hQ hB heq v u
  have hRec (a b : ComplexVector n) : Q x (A x a b) =
      fderiv ℝ Q x a b + chartChristoffelBilin g.form c (φ x) (fderiv ℝ φ x a) (Q x b) := by
    change Q x (normalConnection g p U hU x a b) = _
    rw [normalConnection_eq_chart g p U hU c x hx]
    exact normalConnectionInChart_reconstruct g p U hU c x a b hx
  have hQB (w : ComplexVector n) : Q x (B x w) = fderiv ℝ φ x w :=
    normalDifferential_coords g p U hU c x w hx
  have hSymm := hφ.isSymmSndFDerivAt (by norm_num) u v
  apply (normalParallelCoefficients_isInvertible g p U hU c x hx).bijective.injective
  change Q x (fderiv ℝ B x u v - fderiv ℝ B x v u + A x u (B x v) - A x v (B x u)) = Q x 0
  rw [map_sub, map_add, map_sub, map_zero, hRec, hRec, hQB, hQB]
  calc
    _ = (Q x (fderiv ℝ B x u v) + fderiv ℝ Q x u (B x v)) -
        (Q x (fderiv ℝ B x v u) + fderiv ℝ Q x v (B x u)) +
        (chartChristoffelBilin g.form c (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) -
          chartChristoffelBilin g.form c (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x u)) := by abel
    _ = 0 := by rw [hDuv, hDvu, hSymm, chartChristoffelBilin_symm]; abel

end Yau.Blueprint.C02Proof
