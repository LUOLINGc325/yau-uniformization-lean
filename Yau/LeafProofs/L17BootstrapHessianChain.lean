import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Native first and second chain rules from genuine C2 regularity. -/

noncomputable section
open Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Yau.LeafProofs.L17BootstrapHessianChainAux

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The actual bilinear second-chain-rule expression, bundled as nested CLMs. -/
def compositionHessian (f : F → G) (psi : E → F) (z : E) : E →L[ℝ] E →L[ℝ] G :=
  (ContinuousLinearMap.compL ℝ E F G (fderiv ℝ f (psi z))).comp
      (fderiv ℝ (fderiv ℝ psi) z) +
    ((ContinuousLinearMap.compL ℝ E F G).flip (fderiv ℝ psi z)).comp
      ((fderiv ℝ (fderiv ℝ f) (psi z)).comp (fderiv ℝ psi z))

theorem compositionHessian_apply (f : F → G) (psi : E → F) (z a b : E) :
    compositionHessian f psi z a b =
      fderiv ℝ (fderiv ℝ f) (psi z) (fderiv ℝ psi z a) (fderiv ℝ psi z b) +
        fderiv ℝ f (psi z) (fderiv ℝ (fderiv ℝ psi) z a b) := by
  change fderiv ℝ f (psi z) (fderiv ℝ (fderiv ℝ psi) z a b) +
    fderiv ℝ (fderiv ℝ f) (psi z) (fderiv ℝ psi z a) (fderiv ℝ psi z b) = _
  exact add_comm _ _

theorem hasFDerivAt_comp_of_contDiffAt_two {psi : E → F} {f : F → G} {z : E}
    (hpsi : ContDiffAt ℝ 2 psi z) (hf : ContDiffAt ℝ 2 f (psi z)) :
    HasFDerivAt (fun w => f (psi w))
      ((fderiv ℝ f (psi z)).comp (fderiv ℝ psi z)) z :=
  (hf.differentiableAt (by norm_num)).hasFDerivAt.comp z
    (hpsi.differentiableAt (by norm_num)).hasFDerivAt

theorem fderiv_comp_of_contDiffAt_two {psi : E → F} {f : F → G} {z : E}
    (hpsi : ContDiffAt ℝ 2 psi z) (hf : ContDiffAt ℝ 2 f (psi z)) :
    fderiv ℝ (fun w => f (psi w)) z =
      (fderiv ℝ f (psi z)).comp (fderiv ℝ psi z) :=
  (hasFDerivAt_comp_of_contDiffAt_two hpsi hf).fderiv

/-- The differentiated native first derivative. Only C2 at the two actual points
is used; the germ of the first chain rule is obtained at finite order. -/
theorem hasFDerivAt_fderiv_comp_of_contDiffAt_two {psi : E → F} {f : F → G} {z : E}
    (hpsi : ContDiffAt ℝ 2 psi z) (hf : ContDiffAt ℝ 2 f (psi z)) :
    HasFDerivAt (fderiv ℝ (fun w => f (psi w))) (compositionHessian f psi z) z := by
  have hp : HasFDerivAt psi (fderiv ℝ psi z) z :=
    (hpsi.differentiableAt (by norm_num)).hasFDerivAt
  have hpD : HasFDerivAt (fderiv ℝ psi) (fderiv ℝ (fderiv ℝ psi) z) z :=
    ((hpsi.fderiv_right (by norm_num : (1 : ℕ∞ω)+1 ≤ 2)).differentiableAt (by norm_num)).hasFDerivAt
  have hfD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (psi z)) (psi z) :=
    ((hf.fderiv_right (by norm_num : (1 : ℕ∞ω)+1 ≤ 2)).differentiableAt (by norm_num)).hasFDerivAt
  have hA : HasFDerivAt (fun w => fderiv ℝ f (psi w))
      ((fderiv ℝ (fderiv ℝ f) (psi z)).comp (fderiv ℝ psi z)) z := hfD.comp z hp
  have hProduct : HasFDerivAt
      (fun w => (fderiv ℝ f (psi w)).comp (fderiv ℝ psi w))
      (compositionHessian f psi z) z := hA.clm_comp hpD
  have hpNear : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 psi w :=
    hpsi.eventually (by simp : (2 : ℕ∞ω) ≠ ∞)
  have hfNear : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 f (psi w) :=
    hpsi.continuousAt.eventually (hf.eventually (by simp : (2 : ℕ∞ω) ≠ ∞))
  have hGerm : (fderiv ℝ (fun w => f (psi w))) =ᶠ[𝓝 z]
      (fun w => (fderiv ℝ f (psi w)).comp (fderiv ℝ psi w)) := by
    filter_upwards [hpNear,hfNear] with w hpw hfw
    exact fderiv_comp_of_contDiffAt_two hpw hfw
  exact hProduct.congr_of_eventuallyEq hGerm

theorem second_derivative_comp_of_contDiffAt_two {psi : E → F} {f : F → G} {z : E}
    (hpsi : ContDiffAt ℝ 2 psi z) (hf : ContDiffAt ℝ 2 f (psi z)) (a b : E) :
    fderiv ℝ (fderiv ℝ (fun w => f (psi w))) z a b =
      fderiv ℝ (fderiv ℝ f) (psi z) (fderiv ℝ psi z a) (fderiv ℝ psi z b) +
        fderiv ℝ f (psi z) (fderiv ℝ (fderiv ℝ psi) z a b) := by
  rw [(hasFDerivAt_fderiv_comp_of_contDiffAt_two hpsi hf).fderiv]
  exact compositionHessian_apply f psi z a b

end Yau.LeafProofs.L17BootstrapHessianChainAux
