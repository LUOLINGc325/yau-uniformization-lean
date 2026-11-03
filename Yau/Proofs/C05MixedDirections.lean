import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Commutation of the actual constant-direction derivatives in a fixed chart. -/

noncomputable section
open scoped ContDiff Topology
namespace Yau.Proofs.C05Aux
open Filter
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def directionalDerivative (v : E) (f : E → F) (x : E) : F := fderiv ℝ f x v

theorem contDiffAt_directionalDerivative {f : E → F} {x : E} {m n : ℕ∞ω}
    (hf : ContDiffAt ℝ n f x) (hm : m + 1 ≤ n) (v : E) :
    ContDiffAt ℝ m (directionalDerivative v f) x :=
  (hf.fderiv_right hm).clm_apply contDiffAt_const

theorem directionalDerivative_directionalDerivative {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    directionalDerivative w (directionalDerivative v f) x =
      fderiv ℝ (fderiv ℝ f) x w v := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he := ((ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  exact congrArg (fun A => A w) he

theorem directionalDerivative_commute {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    directionalDerivative v (directionalDerivative w f) x =
      directionalDerivative w (directionalDerivative v f) x := by
  rw [directionalDerivative_directionalDerivative hf,
    directionalDerivative_directionalDerivative hf]
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq v w

theorem directionalDerivative_third_rotate {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (a b c : E) :
    directionalDerivative a (directionalDerivative b (directionalDerivative c f)) x =
      directionalDerivative b (directionalDerivative c (directionalDerivative a f)) x := by
  have hdc : ContDiffAt ℝ 2 (directionalDerivative c f) x :=
    contDiffAt_directionalDerivative hf (by norm_num) c
  rw [directionalDerivative_commute hdc a b]
  have he : directionalDerivative a (directionalDerivative c f) =ᶠ[𝓝 x]
      directionalDerivative c (directionalDerivative a f) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact directionalDerivative_commute (hy.of_le (by norm_num)) a c
  exact congrArg (fun A : E →L[ℝ] F => A b) (he.fderiv_eq (𝕜 := ℝ))

end Yau.Proofs.C05Aux
