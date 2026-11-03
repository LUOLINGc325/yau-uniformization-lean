import Yau.Proofs.V03HolomorphicBoundaryTrace
import Yau.Proofs.V03AmbientScalarContraction
import Yau.Proofs.V03CoordinateDerivative

/-! The original radial derivative is minus i times the actual angular
derivative. Intrinsic scalar coefficient jets therefore use genuine signed boundary currents. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem closedDisc_complex_radial_derivative (f : ℂ → ℂ) (θ : ℝ) :
    fderivWithin ℂ f (Metric.closedBall (0 : ℂ) 1) (circlePoint θ) (circlePoint θ) =
      -Complex.I * holomorphicAngularTrace f θ := by
  have hv : fderivWithin ℂ f (Metric.closedBall (0 : ℂ) 1) (circlePoint θ) (circlePoint θ) =
      circlePoint θ * closedDiscDerivative f (circlePoint θ) := by
    simpa only [closedDiscDerivative, smul_eq_mul, mul_one] using
      (fderivWithin ℂ f (Metric.closedBall (0 : ℂ) 1) (circlePoint θ)).map_smul (circlePoint θ) (1 : ℂ)
  rw [hv, holomorphicAngularTrace]
  calc
    _ = -(Complex.I * Complex.I) * (circlePoint θ * closedDiscDerivative f (circlePoint θ)) := by
      rw [Complex.I_mul_I]
      ring
    _ = _ := by ring

theorem closedDisc_holomorphic_radial_derivative {f : ℂ → ℂ}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) (θ : ℝ) :
    fderivWithin ℝ f (Metric.closedBall (0 : ℂ) 1) (circlePoint θ) (circlePoint θ) =
      -Complex.I * holomorphicAngularTrace f θ := by
  have hd := (hf.differentiableOn (by simp)) _ (circlePoint_mem_closedBall θ)
  rw [← hd.restrictScalars_fderivWithin ℝ
    (uniqueDiffOn_real_closedDisc _ (circlePoint_mem_closedBall θ))]
  exact closedDisc_complex_radial_derivative f θ

theorem cotangentDisc_scalar_radial_ambient {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) {b : CotangentPoint M → ℝ}
    (θ : ℝ) (hb : DifferentiableAt ℝ (fun z => b (cotangentChartInv (f (circlePoint θ)).1 z))
      (cotangentChart (f (circlePoint θ)).1 (f (circlePoint θ)))) :
    fderivWithin ℝ (fun ζ => b (f ζ)) (Metric.closedBall (0 : ℂ) 1)
      (circlePoint θ) (circlePoint θ) =
      2 * (ambientScalarCovector G b (f (circlePoint θ)) ⬝ᵥ
        (fun a => -Complex.I * holomorphicAngularTrace (fun ζ => G (f ζ) a) θ)).re := by
  have hH := cotangentDisc_ambient_contDiffOn hf hG.1
  rw [cotangentHolomorphicOn_scalar_ambient_fderivWithin hG (cotangentDisc_holomorphicOn hf)
    (circlePoint_mem_closedBall θ) (uniqueDiffOn_real_closedDisc _ (circlePoint_mem_closedBall θ)) hb]
  congr 2
  apply congrArg (fun v : Fin q → ℂ => ambientScalarCovector G b (f (circlePoint θ)) ⬝ᵥ v)
  funext a
  rw [← fderivWithin_euclidean_component (uniqueDiffOn_complex_closedDisc _ (circlePoint_mem_closedBall θ))
    ((hH.differentiableOn (by simp)) _ (circlePoint_mem_closedBall θ)),
    closedDisc_complex_radial_derivative]

end Yau.Blueprint.V03Proof
