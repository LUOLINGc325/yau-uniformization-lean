import Yau.Proofs.V03LeviChain

/-! Native third Fréchet derivative symmetry, obtained by differentiating
the genuine local second-derivative symmetry and applying Schwarz to Df. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_secondFDeriv_apply {f : E → F} {z : E}
    (hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) z) (u v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ f) y v w) z u =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z u v w := by
  rw [fderiv_clm_apply (hH.clm_apply (differentiableAt_const v)) (differentiableAt_const w),
    fderiv_clm_apply hH (differentiableAt_const v)]
  simp

theorem thirdFDeriv_swap_first {f : E → F} {z : E} (hf : ContDiffAt ℝ 3 f z) (u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z v u w := by
  have hDf : ContDiffAt ℝ 2 (fderiv ℝ f) z := hf.fderiv_right (by norm_num)
  exact congrArg (fun A : E →L[ℝ] F => A w) (hDf.isSymmSndFDerivAt (by norm_num) u v)

theorem thirdFDeriv_swap_last {f : E → F} {z : E} (hf : ContDiffAt ℝ 3 f z) (u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z u w v := by
  have hnear : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 f y :=
    (hf.of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)).eventually (by norm_num)
  have heq : (fun y => fderiv ℝ (fderiv ℝ f) y v w) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ (fderiv ℝ f) y w v) := by
    filter_upwards [hnear] with y hy
    exact hy.isSymmSndFDerivAt (by norm_num) v w
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) z :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero
  have hh := congrArg (fun A : E →L[ℝ] F => A u) heq.fderiv_eq
  simpa only [fderiv_secondFDeriv_apply hH] using hh

end Yau.Blueprint.V03Proof
