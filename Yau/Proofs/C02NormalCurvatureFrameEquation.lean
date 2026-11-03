import Yau.Proofs.C02NormalHomotopies
import Yau.Proofs.C02GaugeCurvatureTransform
import Yau.Proofs.C02ConnectionPullbackCurvature

/-! The computed curvature of the genuine radial connection is the actual
target-chart connection curvature expressed through the genuine parallel
frame. The base-map differential need not be invertible for this identity. -/

noncomputable section
open Set Filter
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalConnectionCurvature_frame_equation (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x u v : ComplexVector n)
    (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    (normalParallelCoefficients g p U hU c x).comp (normalConnectionCurvature g p U hU x u v) =
      (connectionCurvature (chartChristoffelBilin g.form c) (normalCoordinateMap g p U c x)
        (fderiv ℝ (normalCoordinateMap g p U c) x u) (fderiv ℝ (normalCoordinateMap g p U c) x v)).comp
          (normalParallelCoefficients g p U hU c x) := by
  letI := manifold_realSmooth M
  let φ := normalCoordinateMap g p U c
  let Q := normalParallelCoefficients g p U hU c
  let A := normalConnection g p U hU
  let Γ := chartChristoffelBilin g.form c
  let Ω := pullbackConnection Γ φ
  have hO := (normalRealMap_smooth g p U hU).continuous.continuousAt.preimage_mem_nhds
    ((chartAt (ComplexVector n) c).open_source.mem_nhds hx)
  have hφ : ContDiffAt ℝ ∞ φ x := (normalCoordinateMap_smooth g p U hU c).contDiffAt hO
  have hQ : ContDiffAt ℝ 2 Q x :=
    ((normalParallelCoefficients_smooth g p U hU c).contDiffAt hO).of_le (by simp)
  have hA : DifferentiableAt ℝ A x := (normalConnection_smooth g p U hU).differentiable (by simp) x
  have hy : φ x ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hx)
  have hΓ : ContDiffAt ℝ ∞ Γ (φ x) :=
    (chartChristoffelBilin_contDiffOn g c).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hy)
  have hDφ : ContDiffAt ℝ ∞ (fderiv ℝ φ) x := hφ.fderiv_right (by simp)
  have hΩ : ContDiffAt ℝ ∞ Ω x := (hΓ.comp x hφ).clm_comp hDφ
  have hConn (a : ComplexVector n) :
      (fun y => fderiv ℝ Q y a + (Ω y a).comp (Q y)) =ᶠ[𝓝 x]
        (fun y => (Q y).comp (A y a)) := by
    filter_upwards [hO] with y hy
    apply ContinuousLinearMap.ext
    intro z
    change fderiv ℝ Q y a z + Γ (φ y) (fderiv ℝ φ y a) (Q y z) = Q y (normalConnection g p U hU y a z)
    rw [normalConnection_eq_chart g p U hU c y hy]
    exact (normalConnectionInChart_reconstruct g p U hU c y a z hy).symm
  have hGauge := gauge_curvature_transform Q A Ω x u v hQ hA (hΩ.differentiableAt (by simp)) hConn
  have hPull := connectionCurvature_pullback Γ φ x u v (hΓ.differentiableAt (by simp))
    (hφ.of_le (by simp))
  exact hGauge.trans (congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L.comp (Q x)) hPull)

end Yau.Blueprint.C02Proof
