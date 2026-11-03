import Yau.LeafProofs.L10DiscClosedContinuity

/-! Genuine extension of derivative fields to a convex boundary, and the
precise remaining identification needed for the Green solution's first derivative. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs

/-- Continuous tensor fields which are actual derivative fields in an
open convex set form an actual Taylor series on its closure. -/
theorem closed_convex_jets_hasFTaylorSeries
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : E → F} {p : E → FormalMultilinearSeries ℝ E F}
    (hzero : ∀ x ∈ closure s, (p x 0).curry0 = f x)
    (hcont : ∀ m : ℕ, ContinuousOn (fun x => p x m) (closure s))
    (hderiv : ∀ m : ℕ, ∀ x ∈ s,
      HasFDerivAt (fun y => p y m) (p x (m + 1)).curryLeft x) :
    HasFTaylorSeriesUpToOn ∞ f p (closure s) := by
  refine ⟨hzero, ?_, fun m _ => hcont m⟩
  intro m _ x hx
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hderiv m y hy).differentiableAt.differentiableWithinAt) hconv hs
  · intro y hy
    exact ((hcont m) y hy).mono subset_closure
  · have hlim : Tendsto (fun y => (p y (m + 1)).curryLeft) (𝓝[s] x)
        (𝓝 (p x (m + 1)).curryLeft) := by
      have hc := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).continuous.comp_continuousOn
        (hcont (m + 1))
      exact (hc x hx).mono subset_closure
    have heq : (fun y => (p y (m + 1)).curryLeft) =ᶠ[𝓝[s] x]
        (fun y => fderiv ℝ (fun z => p z m) y) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hderiv m y hy).fderiv.symm
    exact Filter.Tendsto.congr' heq hlim

theorem closed_convex_jets_contDiffOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : E → F} {p : E → FormalMultilinearSeries ℝ E F}
    (hzero : ∀ x ∈ closure s, (p x 0).curry0 = f x)
    (hcont : ∀ m : ℕ, ContinuousOn (fun x => p x m) (closure s))
    (hderiv : ∀ m : ℕ, ∀ x ∈ s,
      HasFDerivAt (fun y => p y m) (p x (m + 1)).curryLeft x) :
    ContDiffOn ℝ ∞ f (closure s) :=
  (closed_convex_jets_hasFTaylorSeries hs hconv hzero hcont hderiv).contDiffOn

/-- This exact identification is still required. Interior smoothness,
absolute convergence of the integral, and continuity on the closed disc
have already been proved independently. -/
def DiscGreenInteriorGradientGap : Prop :=
  ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1) →
    ∀ z ∈ Metric.ball (0 : ℂ) 1,
      fderiv ℝ (discGreenSolution f) z = discGreenDerivative f z

theorem discGreenSolution_hasFDerivWithinAt_of_interiorGradient
    (hgradient : DiscGreenInteriorGradientGap) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    HasFDerivWithinAt (discGreenSolution f) (discGreenDerivative f z)
      (Metric.closedBall (0 : ℂ) 1) z := by
  have hclosure : closure (Metric.ball (0 : ℂ) 1) = Metric.closedBall (0 : ℂ) 1 :=
    closure_ball 0 (by norm_num)
  rw [← hclosure]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    ((discGreenSolution_contDiffOn_interior hf).differentiableOn (by simp))
    (convex_ball _ _) Metric.isOpen_ball
  · intro y hy
    exact ((discGreenSolution_continuousOn hf.continuousOn) y (hclosure ▸ hy)).mono
      Metric.ball_subset_closedBall
  · have hlim := ((discGreenDerivative_continuousOn hf.continuousOn) z hz).mono
      Metric.ball_subset_closedBall
    have heq : discGreenDerivative f =ᶠ[𝓝[Metric.ball (0 : ℂ) 1] z]
        fderiv ℝ (discGreenSolution f) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hgradient f hf y hy).symm
    exact Filter.Tendsto.congr' heq hlim

theorem disc_closedBall_uniqueDiffOn : UniqueDiffOn ℝ (Metric.closedBall (0 : ℂ) 1) := by
  apply uniqueDiffOn_convex (convex_closedBall _ _)
  rw [interior_closedBall 0 (by norm_num)]
  exact ⟨0, by simp⟩

theorem discGreenSolution_contDiffOn_one_of_interiorGradient
    (hgradient : DiscGreenInteriorGradientGap) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ 1 (discGreenSolution f) (Metric.closedBall (0 : ℂ) 1) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn disc_closedBall_uniqueDiffOn]
  refine ⟨by simp, discGreenDerivative f, contDiffOn_zero.mpr
    (discGreenDerivative_continuousOn hf.continuousOn), ?_⟩
  intro z hz
  exact discGreenSolution_hasFDerivWithinAt_of_interiorGradient hgradient hf hz

end Yau.LeafProofs
