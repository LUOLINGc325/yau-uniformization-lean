import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic

/-! The actual connection of a smooth coframe. Parallelism and torsion
follow from the displayed formulas in an arbitrary real Banach space. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coframeModelConnection (A : E → E →L[ℝ] E)
    (conn : E → E →L[ℝ] E →L[ℝ] E) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E E E (A x).inverse).comp
    (fderiv ℝ A x + (ContinuousLinearMap.precompR E (conn x)).flip (A x))

@[simp] theorem coframeModelConnection_apply (A : E → E →L[ℝ] E)
    (conn : E → E →L[ℝ] E →L[ℝ] E) (x u v : E) :
    coframeModelConnection A conn x u v =
      (A x).inverse (fderiv ℝ A x u v + conn x u (A x v)) := rfl

theorem coframe_model_connection_forward (A : E → E →L[ℝ] E)
    (conn : E → E →L[ℝ] E →L[ℝ] E) (x : E) (hInv : (A x).IsInvertible) (u v : E) :
    A x (coframeModelConnection A conn x u v) =
      fderiv ℝ A x u v + conn x u (A x v) := hInv.self_apply_inverse _

theorem coframe_model_complex_forward (L I : E →L[ℝ] E) (hInv : L.IsInvertible) (v : E) :
    L (L.inverse.comp (I.comp L) v) = I (L v) := hInv.self_apply_inverse _

theorem coframe_model_connection_symm (A : E → E →L[ℝ] E)
    (conn : E → E →L[ℝ] E →L[ℝ] E) (x : E)
    (htor : ∀ u v, fderiv ℝ A x u v - fderiv ℝ A x v u +
      conn x u (A x v) - conn x v (A x u) = 0) (u v : E) :
    coframeModelConnection A conn x u v = coframeModelConnection A conn x v u := by
  have hh : fderiv ℝ A x u v + conn x u (A x v) =
      fderiv ℝ A x v u + conn x v (A x u) := by
    apply sub_eq_zero.mp
    convert htor u v using 1; abel
  exact congrArg (A x).inverse hh

variable [CompleteSpace E]

theorem coframe_model_complex_contDiffAt (A : E → E →L[ℝ] E) (I : E →L[ℝ] E)
    (x : E) (hA : ContDiff ℝ ∞ A) (hInv : (A x).IsInvertible) :
    ContDiffAt ℝ ∞ (fun y => (A y).inverse.comp (I.comp (A y))) x :=
  (hInv.contDiffAt_map_inverse.comp x hA.contDiffAt).clm_comp
    (contDiffAt_const.clm_comp hA.contDiffAt)

theorem coframe_model_complex_intertwining_derivative
    (A : E → E →L[ℝ] E) (I : E →L[ℝ] E) (x : E)
    (hA : ContDiff ℝ ∞ A) (hInv : (A x).IsInvertible) (u v : E) :
    fderiv ℝ A x u ((A x).inverse.comp (I.comp (A x)) v) +
      A x (fderiv ℝ (fun y => (A y).inverse.comp (I.comp (A y))) x u v) =
        I (fderiv ℝ A x u v) := by
  let J : E → E →L[ℝ] E := fun y => (A y).inverse.comp (I.comp (A y))
  have hAd : DifferentiableAt ℝ A x := hA.differentiable (by simp) x
  have hJd : DifferentiableAt ℝ J x :=
    (coframe_model_complex_contDiffAt A I x hA hInv).differentiableAt (by simp)
  have hJv : HasFDerivAt (fun y => J y v) ((fderiv ℝ J x).flip v) x := by
    simpa using hJd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hAv : HasFDerivAt (fun y => A y v) ((fderiv ℝ A x).flip v) x := by
    simpa using hAd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hl := hAd.hasFDerivAt.clm_apply hJv
  have hr : HasFDerivAt (fun y => I (A y v))
      (I.comp ((fderiv ℝ A x).flip v)) x := I.hasFDerivAt.comp x hAv
  have hnear : ∀ᶠ y in 𝓝 x, (A y).IsInvertible :=
    hA.continuous.continuousAt.eventually hInv.eventually_nhds
  have he : (fun y => A y (J y v)) =ᶠ[𝓝 x] (fun y => I (A y v)) := by
    filter_upwards [hnear] with y hy
    exact hy.self_apply_inverse _
  have heq : fderiv ℝ (fun y => A y (J y v)) x =
      fderiv ℝ (fun y => I (A y v)) x := he.fderiv_eq
  rw [hl.fderiv, hr.fderiv] at heq
  have hh := congrArg (fun L : E →L[ℝ] E => L u) heq
  change A x (fderiv ℝ J x u v) + fderiv ℝ A x u (J x v) =
    I (fderiv ℝ A x u v) at hh
  exact (add_comm _ _).trans hh

theorem coframe_model_complex_parallel
    (A : E → E →L[ℝ] E) (I : E →L[ℝ] E)
    (conn : E → E →L[ℝ] E →L[ℝ] E) (x : E)
    (hA : ContDiff ℝ ∞ A) (hInv : (A x).IsInvertible)
    (hcomm : ∀ u v, conn x u (I v) = I (conn x u v)) (u v : E) :
    fderiv ℝ (fun y => (A y).inverse.comp (I.comp (A y))) x u v +
      coframeModelConnection A conn x u ((A x).inverse.comp (I.comp (A x)) v) =
        (A x).inverse.comp (I.comp (A x)) (coframeModelConnection A conn x u v) := by
  let J : E → E →L[ℝ] E := fun y => (A y).inverse.comp (I.comp (A y))
  have hJforward (v : E) : A x (J x v) = I (A x v) := hInv.self_apply_inverse _
  have hGforward (u v : E) : A x (coframeModelConnection A conn x u v) =
      fderiv ℝ A x u v + conn x u (A x v) :=
    coframe_model_connection_forward A conn x hInv u v
  have hd := coframe_model_complex_intertwining_derivative A I x hA hInv u v
  have hInjective : Function.Injective (A x) := by
    obtain ⟨e, he⟩ := hInv
    rw [← he]
    exact e.injective
  change fderiv ℝ J x u v + coframeModelConnection A conn x u (J x v) =
    J x (coframeModelConnection A conn x u v)
  apply hInjective
  simp only [map_add, hGforward, hJforward, hcomm]
  have hh := congrArg (fun z : E => z + I (conn x u (A x v))) hd
  simpa only [add_assoc, add_left_comm, add_comm] using hh

end Yau.Proofs.C04Aux
