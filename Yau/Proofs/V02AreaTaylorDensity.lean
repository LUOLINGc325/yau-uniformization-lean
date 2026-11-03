import Yau.Proofs.V02AreaTaylorForms
import Yau.Proofs.V03JointAmbientDifferential
import Yau.Proofs.V03VectorAreaSum

/-! Literal density and finite integral of all three original spatial areas.
The fixed-chart formula uses the original closed-disc differential. -/

open scoped Topology ContDiff Matrix Manifold
open Filter MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

def spatialDensity (d : VariationData X q) (f : ℂ → CotangentPoint X.manifold) (ζ : ℂ) : ℝ :=
  baseDensityWithin X.metric.form f ζ + 2 * ‖closedDiscDerivative (fun w => d.G (f w)) ζ‖ ^ 2 +
    gaussDensityWithin d.G f ζ

theorem spatialDensity_eq_coordinate {d : VariationData X q} (hG : CotangentImmersion d.G)
    {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f)
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1) (x : Pt X) (hx : f ζ ∈ cotangentSource x) :
    spatialDensity d f ζ =
      complexDiagonal (spatialChartBilinear d.G X.metric.form x (cotangentChart x (f ζ)))
        (fderivWithin ℂ (fun w => cotangentChart x (f w)) (Metric.closedBall 0 1) ζ 1) := by
  have hc := (cotangentDisc_coords_contDiffWithinAt hf hζ x hx).differentiableWithinAt (by simp)
  have hbase := congrArg (fun A : ℂ →L[ℂ] ComplexVector n => A 1)
    (hc.hasFDerivWithinAt.fst.fderivWithin (uniqueDiffOn_complex_closedDisc ζ hζ))
  have hambient := congrArg (fun A : ℂ →L[ℂ] ComplexVector q => A 1)
    (cotangentHolomorphicOn_ambient_fderivWithin hG.1 (cotangentDisc_holomorphicOn hf)
      hζ (uniqueDiffOn_complex_closedDisc ζ hζ) x hx)
  simp only [ContinuousLinearMap.comp_apply] at hbase hambient
  change (fderivWithin ℂ (fun η => chartPt x (f η).1) (Metric.closedBall 0 1) ζ 1) =
    (fderivWithin ℂ (fun η => cotangentChart x (f η)) (Metric.closedBall 0 1) ζ 1).1 at hbase
  rw [spatialChartBilinear_diagonal hG x (cotangentChart_mapsTo x hx)]
  unfold spatialDensity closedDiscDerivative
  rw [baseDensityWithin_eq_fixed_chart X.metric.form hf hζ x hx,
    gaussDensityWithin_eq_fixed_chart hG hf hζ x hx, hbase, hambient]
  rfl

theorem spatialDensity_integrableOn {d : VariationData X q} (hG : CotangentImmersion d.G)
    {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f) :
    IntegrableOn (spatialDensity d f) (Metric.ball (0 : ℂ) 1) := by
  have hAmb := cotangentDisc_ambient_contDiffOn hf hG.1
  have hEucl : IntegrableOn (fun ζ => 2 * ‖closedDiscDerivative (fun w => d.G (f w)) ζ‖ ^ 2)
      (Metric.ball (0 : ℂ) 1) :=
    ((continuousOn_const.mul ((continuousOn_closedDiscDerivative hAmb).norm.pow 2)).integrableOn_compact
      (μ := volume) (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall
  exact ((baseDensityWithin_integrableOn X.metric hf).add hEucl).add
    (gaussDensityWithin_integrableOn hG hf)

theorem spatialArea_eq_integral_spatialDensity {d : VariationData X q}
    (hG : CotangentImmersion d.G) {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f) :
    spatialArea d f = ∫ ζ in Metric.ball (0 : ℂ) 1, spatialDensity d f ζ := by
  have hAmb := cotangentDisc_ambient_contDiffOn hf hG.1
  have hEucl : IntegrableOn (fun ζ => 2 * ‖closedDiscDerivative (fun w => d.G (f w)) ζ‖ ^ 2)
      (Metric.ball (0 : ℂ) 1) :=
    ((continuousOn_const.mul ((continuousOn_closedDiscDerivative hAmb).norm.pow 2)).integrableOn_compact
      (μ := volume) (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall
  have hEA : euclideanArea (fun ζ => d.G (f ζ)) = ENNReal.ofReal
      (∫ ζ in Metric.ball (0 : ℂ) 1, 2 * ‖closedDiscDerivative (fun w => d.G (f w)) ζ‖ ^ 2) := by
    change normDiscArea (fun ζ => d.G (f ζ)) = _
    simpa only [radialEuclideanDensity, Complex.ofReal_one, one_mul, one_smul] using
      (normDiscArea_radial_eq_integral hAmb (r := 1) (by simp))
  rw [spatialArea, discArea_eq_ofReal_integral X.metric hf,
    ENNReal.toReal_ofReal (integral_nonneg (baseDensityWithin_nonneg X.metric.form f)),
    hEA, ENNReal.toReal_ofReal (integral_nonneg (fun ζ => by positivity)),
    gaussArea_eq_integral_densityWithin]
  rw [← integral_add (baseDensityWithin_integrableOn X.metric hf) hEucl,
    ← integral_add (μ := volume.restrict (Metric.ball (0 : ℂ) 1)) (f := fun ζ => baseDensityWithin X.metric.form f ζ +
      2 * ‖closedDiscDerivative (fun w => d.G (f w)) ζ‖ ^ 2)
      (by simpa only [IntegrableOn, Pi.add_def] using (baseDensityWithin_integrableOn X.metric hf).add hEucl)
      (gaussDensityWithin_integrableOn hG hf)]
  rfl

end Yau.Blueprint.V02AreaTaylorProof
