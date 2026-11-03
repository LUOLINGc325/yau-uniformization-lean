import Yau.Proofs.E02PolynomialJet

open Set Filter Asymptotics Metric
open scoped Topology ContDiff Asymptotics
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second Peano expansion is local: a finite C² germ is enough.
No common C∞ neighborhood is extracted from a pointwise C∞ hypothesis. -/
theorem realSecondJet_of_eventually_derivative_field (H : E → ℝ) (P : E → E →L[ℝ] ℝ)
    (x : E) (hH : ∀ᶠ y in 𝓝 x, HasFDerivAt H (P y) y)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : HasFDerivAt P A x) :
    RealSecondJet H x (P x) A := by
  have hSym : ∀ v w, A v w = A w v := second_derivative_symmetric_of_eventually hH hA
  refine ⟨hSym,?_⟩
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp hH
  let R : E → ℝ := fun y => H y-jetPolynomial (H x) x (P x) A y
  let R' : E → E →L[ℝ] ℝ := fun y => P y-P x-A (y-x)
  have hR (y : E) (hy : y ∈ ball x r) : HasFDerivAt R (R' y) y := by
    have hD : P y-(P x+A (y-x)) = R' y := by dsimp [R']; abel
    rw [←hD]
    exact (hBall hy).sub (jetPolynomial_hasFDerivAt (H x) x (P x) A hSym y)
  have hRem : R' =o[𝓝 x] (fun y => y-x) := hasFDerivAt_iff_isLittleO.mp hA
  have hSmall : R' =o[𝓝[ball x r] x] (fun y => ‖y-x‖^1) := by
    simpa only [pow_one,isLittleO_norm_right] using hRem.mono nhdsWithin_le_nhds
  have hFinal := (convex_ball x r).isLittleO_pow_succ (n := 1) (mem_ball_self hr)
    (fun y hy => (hR y hy).hasFDerivWithinAt) hSmall
  have hR0 : R x = 0 := by simp [R,jetPolynomial]
  rw [hR0,nhdsWithin_eq_nhds.mpr (ball_mem_nhds x hr)] at hFinal
  simp only [sub_zero] at hFinal
  convert hFinal using 1
  funext y
  dsimp [R,jetPolynomial]
  ring

theorem realSecondJet_of_contDiffAt_two {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    RealSecondJet f x (fderiv ℝ f x) (fderiv ℝ (fderiv ℝ f) x) := by
  have hNear : ∀ᶠ y in 𝓝 x, HasFDerivAt f (fderiv ℝ f y) y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact (hy.differentiableAt (by norm_num)).hasFDerivAt
  exact realSecondJet_of_eventually_derivative_field f (fderiv ℝ f) x hNear _
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt

end Yau.NodeProofs.E02Aux
