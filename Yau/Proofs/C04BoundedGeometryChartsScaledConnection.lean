import Yau.Proofs.C04BoundedGeometryChartsRadialConnectionComplex
import Yau.Proofs.C04FrameComplexConnection

/-! The scaled genuine coframe induces a torsion-free complex-parallel connection. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L21Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

def scaledRadialCoframe (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ) (x : ComplexVector n) :=
  radialCoframe g p U (d • x)

def scaledRadialConnection (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ) (x : ComplexVector n) :=
  d • radialConnection g p U (d • x)

def scaledNormalComplex (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ) (x : ComplexVector n) :=
  (scaledRadialCoframe g p U d x).inverse.comp ((stdComplex n).comp (scaledRadialCoframe g p U d x))

theorem scaledRadialCoframe_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ) :
    ContDiff ℝ ∞ (scaledRadialCoframe g p U d) :=
  (radialCoframe_smooth g p U).comp (contDiff_id.const_smul d)

theorem scaledRadialConnection_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ) :
    ContDiff ℝ ∞ (scaledRadialConnection g p U d) :=
  ((radialConnection_smooth g p U).comp (contDiff_id.const_smul d)).const_smul d

theorem scaledRadialCoframe_fderiv (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ) (x u v : ComplexVector n) :
    fderiv ℝ (scaledRadialCoframe g p U d) x u v =
      d • fderiv ℝ (radialCoframe g p U) (d • x) u v := by
  have H := ((radialCoframe_smooth g p U).differentiable (by simp) (d • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul d)
  have HH := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n => L u v) H.fderiv
  change fderiv ℝ (fun y => radialCoframe g p U (d • y)) x u v = _
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul] using HH

theorem scaledRadialConnection_complex (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (d : ℝ) (x u v : ComplexVector n) :
    scaledRadialConnection g p U d x u (Complex.I • v) =
      Complex.I • scaledRadialConnection g p U d x u v := by
  change d • radialConnection g p U (d • x) u (Complex.I • v) =
    Complex.I • (d • radialConnection g p U (d • x) u v)
  rw [radialConnection_complex g hk]
  exact smul_comm d Complex.I _

theorem scaledRadialCoframe_torsion (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ) (x u v : ComplexVector n) :
    fderiv ℝ (scaledRadialCoframe g p U d) x u v - fderiv ℝ (scaledRadialCoframe g p U d) x v u +
      scaledRadialConnection g p U d x u (scaledRadialCoframe g p U d x v) -
        scaledRadialConnection g p U d x v (scaledRadialCoframe g p U d x u) = 0 := by
  rw [scaledRadialCoframe_fderiv, scaledRadialCoframe_fderiv]
  change d • fderiv ℝ (radialCoframe g p U) (d • x) u v -
      d • fderiv ℝ (radialCoframe g p U) (d • x) v u +
      d • radialConnection g p U (d • x) u (radialCoframe g p U (d • x) v) -
      d • radialConnection g p U (d • x) v (radialCoframe g p U (d • x) u) = 0
  rw [← smul_sub, ← smul_add, ← smul_sub, radialCoframe_torsion, smul_zero]

theorem scaledNormalConnection_symm (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ) (x u v : ComplexVector n) :
    C04Aux.coframeModelConnection (scaledRadialCoframe g p U d) (scaledRadialConnection g p U d) x u v =
      C04Aux.coframeModelConnection (scaledRadialCoframe g p U d) (scaledRadialConnection g p U d) x v u :=
  C04Aux.coframe_model_connection_symm _ _ x (scaledRadialCoframe_torsion g p U d x) u v

theorem scaledNormalComplex_eq_actual (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ) :
    scaledNormalComplex g p U d = fun x => realPullbackJ (unitaryExponential g p U) (d • x) := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  exact (realPullbackJ_eq_radial_conjugation g hk p U (d • x) v).symm

theorem scaledNormalComplex_parallel (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ) (x u v : ComplexVector n)
    (hi : (scaledRadialCoframe g p U d x).IsInvertible) :
    fderiv ℝ (scaledNormalComplex g p U d) x u v +
      C04Aux.coframeModelConnection (scaledRadialCoframe g p U d) (scaledRadialConnection g p U d) x u
        (scaledNormalComplex g p U d x v) =
      scaledNormalComplex g p U d x
        (C04Aux.coframeModelConnection (scaledRadialCoframe g p U d) (scaledRadialConnection g p U d) x u v) :=
  C04Aux.coframe_model_complex_parallel _ (stdComplex n) _ x (scaledRadialCoframe_smooth g p U d) hi
    (scaledRadialConnection_complex g hk p U d x) u v

theorem scaledNormalComplex_inverse_frame (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ) (x v : ComplexVector n)
    (hi : (scaledRadialCoframe g p U d x).IsInvertible) :
    (scaledRadialCoframe g p U d x).inverse (Complex.I • v) =
      scaledNormalComplex g p U d x ((scaledRadialCoframe g p U d x).inverse v) := by
  change _ = (scaledRadialCoframe g p U d x).inverse
    (Complex.I • scaledRadialCoframe g p U d x ((scaledRadialCoframe g p U d x).inverse v))
  rw [hi.self_apply_inverse]

end Yau.Proofs.C04ChartsAux
