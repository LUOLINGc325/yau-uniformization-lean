import Yau.LeafProofs.L05AutonomousMollifierSpace
import Yau.LeafProofs.L05AutonomousSpatialGradientMatrix

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
set_option maxHeartbeats 2200000
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- A real dual CLM is reconstructed in its actual operator-norm space, also in dimension zero. -/
theorem auto_gradient_dual_expansion {n : ℕ} (l : Space n →L[ℝ] ℝ) :
    l = ∑ i : Yau.RIdx n, l (Yau.realVec i) • innerSL ℝ (Yau.realVec i) := by
  ext z
  have hcoords : (∑ i : Yau.RIdx n, inner ℝ (Yau.realVec i) z • Yau.realVec i) = z := by
    simpa only [complexVector_realOrthonormalBasis_apply] using
      (complexVector_realOrthonormalBasis n).sum_repr' z
  have hh := congrArg l hcoords
  simpa only [map_sum, map_smul, smul_eq_mul, _root_.sum_apply, _root_.smul_apply,
    innerSL_apply_apply, mul_comm] using hh.symm

/-- True fixed-time evaluation commutes with the actual first spatial Frechet derivative. -/
theorem auto_gradient_bcf_slice_first {n : ℕ} {g : Space n → ℝ →ᵇ ℝ}
    (hg : ContDiff ℝ ∞ g) (x : Space n) (t : ℝ) (v : Space n) :
    fderiv ℝ (fun y => g y t) x v = (fderiv ℝ g x v) t := by
  let ev : (ℝ →ᵇ ℝ) →L[ℝ] ℝ := BoundedContinuousFunction.evalCLM ℝ t
  have hdg := (hg.differentiable (by simp) x).hasFDerivAt
  have hD : HasFDerivAt (ev ∘ g) (ev.comp (fderiv ℝ g x)) x :=
    ev.hasFDerivAt.comp x hdg
  simpa only [ev, Function.comp_def, ContinuousLinearMap.comp_apply,
    BoundedContinuousFunction.evalCLM_apply] using
    congrArg (fun A : Space n →L[ℝ] ℝ => A v) hD.fderiv

/-- The genuine spatial derivative of the actual mollification is jointly continuous in CLM norm. -/
theorem autoSpatialMollify_spatialD_continuous {n : ℕ} (eps : ℝ) (heps : 0 < eps)
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ)) :
    Continuous (spatialD (autoSpatialMollify eps heps w)) := by
  have hm := autoSpatialMollifyBCF_contDiff eps heps w hw
  have hcoord (i : Yau.RIdx n) :
      Continuous (fun p : Point n => spatialD (autoSpatialMollify eps heps w) p (Yau.realVec i)) := by
    have hc : Continuous (fun x : Space n =>
        fderiv ℝ (autoSpatialMollifyBCF eps heps w) x (Yau.realVec i)) :=
      ((hm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
    have hactual := (hc.comp continuous_fst).eval continuous_snd
    have heq : (fun p : Point n => spatialD (autoSpatialMollify eps heps w) p (Yau.realVec i)) =
        (fun p : Point n => (fderiv ℝ (autoSpatialMollifyBCF eps heps w) p.1
          (Yau.realVec i)) p.2) := by
      funext p
      exact auto_gradient_bcf_slice_first hm p.1 p.2 (Yau.realVec i)
    rwa [heq]
  have hrepr : spatialD (autoSpatialMollify eps heps w) =
      fun p => ∑ i : Yau.RIdx n,
        spatialD (autoSpatialMollify eps heps w) p (Yau.realVec i) •
          innerSL ℝ (Yau.realVec i) :=
    funext (fun p => auto_gradient_dual_expansion (spatialD (autoSpatialMollify eps heps w) p))
  rw [hrepr]
  exact continuous_finsetSum _ (fun i _ => (hcoord i).smul continuous_const)

end Yau.LeafProofs.L05AutonomousAux
