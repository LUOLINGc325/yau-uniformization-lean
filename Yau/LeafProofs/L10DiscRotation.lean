import Yau.LeafProofs.L10DiscGradient

/-! Rotation differentiates the density rather than the singular kernel.
The resulting angular derivatives have genuine closed-disc C¹ regularity. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff ComplexConjugate

namespace Yau.LeafProofs

def discRotation (θ : ℝ) (z : ℂ) : ℂ := (Circle.exp θ : ℂ) * z

@[simp] theorem discRotation_zero (z : ℂ) : discRotation 0 z = z := by
  simp [discRotation]

@[simp] theorem discRotation_norm (θ : ℝ) (z : ℂ) : ‖discRotation θ z‖ = ‖z‖ := by
  simp [discRotation]

theorem discRotation_mem_closedBall (θ : ℝ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discRotation θ z ∈ Metric.closedBall (0 : ℂ) 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right, discRotation_norm] using hz

theorem discRotation_hasDerivAt (θ : ℝ) (z : ℂ) :
    HasDerivAt (fun t : ℝ => discRotation t z) (Complex.I * discRotation θ z) θ := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I).cexp.mul_const z
  simpa [discRotation, Circle.coe_exp, mul_assoc, mul_comm, mul_left_comm] using h

/-- The tangential vector field uses the actual within derivative. -/
def discAngular (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  fderivWithin ℝ f (Metric.closedBall (0 : ℂ) 1) z (Complex.I * z)

theorem discAngular_contDiffOn {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (discAngular f) (Metric.closedBall (0 : ℂ) 1) := by
  exact (hf.fderivWithin disc_closedBall_uniqueDiffOn (by simp)).clm_apply
    (contDiffOn_const.mul contDiffOn_id)

theorem discRotation_comp_hasDerivAt {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    (θ : ℝ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    HasDerivAt (fun t => f (discRotation t z)) (discAngular f (discRotation θ z)) θ := by
  have hd := ((hf.differentiableOn (by simp)) _ (discRotation_mem_closedBall θ hz)).hasFDerivWithinAt
  exact hd.comp_hasDerivAt θ (discRotation_hasDerivAt θ z)
    (Eventually.of_forall fun t => discRotation_mem_closedBall t hz)

private theorem discRotation_density_continuousOn {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) (θ : ℝ) :
    ContinuousOn (fun w => f (discRotation θ w)) (Metric.closedBall (0 : ℂ) 1) := by
  exact hf.comp (show ContinuousOn (discRotation θ) _ by unfold discRotation; fun_prop)
    (fun w hw => discRotation_mem_closedBall θ hw)

theorem discGreenSolution_rotation_density_hasDerivAt {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    HasDerivAt (fun θ : ℝ => discGreenSolution (fun w => f (discRotation θ w)) z)
      (discGreenSolution (discAngular f) z) 0 := by
  have hTf := discAngular_contDiffOn hf
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hTf.continuousOn
  have hFmeas : ∀ᶠ θ in 𝓝 (0 : ℝ), AEStronglyMeasurable
      (fun w => discGreenKernel z w • f (discRotation θ w))
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    exact Eventually.of_forall fun θ =>
      (discGreen_solution_integrable (discRotation_density_continuousOn hf.continuousOn θ) hz).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable
      (fun w => discGreenKernel z w • discAngular f (discRotation (0 : ℝ) w))
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    simpa only [discRotation_zero] using (discGreen_solution_integrable hTf.continuousOn hz).aestronglyMeasurable
  have hbound : ∀ᵐ w ∂(volume.restrict (Metric.ball (0 : ℂ) 1)),
      ∀ θ ∈ (Set.univ : Set ℝ),
        ‖discGreenKernel z w • discAngular f (discRotation θ w)‖ ≤ ‖discGreenKernel z w‖ * M := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    intro θ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (hM _ (discRotation_mem_closedBall θ (Metric.ball_subset_closedBall hw))) (norm_nonneg _)
  have hdiff : ∀ᵐ w ∂(volume.restrict (Metric.ball (0 : ℂ) 1)),
      ∀ θ ∈ (Set.univ : Set ℝ), HasDerivAt
        (fun θ => discGreenKernel z w • f (discRotation θ w))
        (discGreenKernel z w • discAngular f (discRotation θ w)) θ := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    intro θ _
    exact HasDerivAt.const_smul (discGreenKernel z w)
      (discRotation_comp_hasDerivAt hf θ (Metric.ball_subset_closedBall hw))
  have hI : IntegrableOn (fun w => discGreenKernel z w • f (discRotation (0 : ℝ) w))
      (Metric.ball (0 : ℂ) 1) volume := by
    simpa only [discRotation_zero] using discGreen_solution_integrable hf.continuousOn hz
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (by simp) hFmeas hI hDmeas hbound ((discGreen_integrable hz).norm.mul_const M) hdiff).2
  simpa only [discGreenSolution, discRotation_zero] using h

theorem discAngular_green_commutes {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discAngular (discGreenSolution f) z = discGreenSolution (discAngular f) z := by
  have hu : HasFDerivWithinAt (discGreenSolution f) (discGreenDerivative f z)
      (Metric.closedBall (0 : ℂ) 1) (discRotation (0 : ℝ) z) := by
    simpa only [discRotation_zero] using discGreenSolution_hasFDerivWithinAt hf hz
  have hleft : HasDerivAt (fun θ => discGreenSolution f (discRotation θ z))
      (discGreenDerivative f z (Complex.I * z)) 0 := by
    simpa only [Function.comp_def, discRotation_zero] using hu.comp_hasDerivAt (0 : ℝ)
      (discRotation_hasDerivAt 0 z) (Eventually.of_forall fun θ => discRotation_mem_closedBall θ hz)
  have hright : HasDerivAt (fun θ => discGreenSolution f (discRotation θ z))
      (discGreenSolution (discAngular f) z) 0 := by
    apply (discGreenSolution_rotation_density_hasDerivAt hf hz).congr_of_eventuallyEq
    exact Eventually.of_forall fun θ => discGreenSolution_rotation (Circle.exp θ) f z
  rw [discAngular, discGreenSolution_fderivWithin hf hz]
  exact hleft.unique hright

def discAngularIterate : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, f => f
  | k + 1, f => discAngular (discAngularIterate k f)

theorem discAngularIterate_contDiffOn {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) (k : ℕ) :
    ContDiffOn ℝ ∞ (discAngularIterate k f) (Metric.closedBall (0 : ℂ) 1) := by
  induction k with
  | zero => exact hf
  | succ k hk => exact discAngular_contDiffOn hk

theorem discAngular_congr {f g : ℂ → ℂ}
    (hfg : Set.EqOn f g (Metric.closedBall (0 : ℂ) 1)) :
    Set.EqOn (discAngular f) (discAngular g) (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz
  rw [discAngular, discAngular, fderivWithin_congr' hfg hz]

theorem discAngularIterate_green_commutes {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) (k : ℕ) :
    Set.EqOn (discAngularIterate k (discGreenSolution f))
      (discGreenSolution (discAngularIterate k f)) (Metric.closedBall (0 : ℂ) 1) := by
  induction k with
  | zero => intro z hz; rfl
  | succ k hk =>
    intro z hz
    exact ((discAngular_congr hk) hz).trans
      (discAngular_green_commutes (discAngularIterate_contDiffOn hf k) hz)

theorem discAngularIterate_green_contDiffOn_one {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) (k : ℕ) :
    ContDiffOn ℝ 1 (discAngularIterate k (discGreenSolution f)) (Metric.closedBall (0 : ℂ) 1) := by
  apply (discGreenSolution_contDiffOn_one (discAngularIterate_contDiffOn hf k)).congr
  exact fun z hz => discAngularIterate_green_commutes hf k hz

theorem discAngularIterate_green_contDiffOn_interior {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) (k : ℕ) :
    ContDiffOn ℝ ∞ (discAngularIterate k (discGreenSolution f)) (Metric.ball (0 : ℂ) 1) := by
  apply (discGreenSolution_contDiffOn_interior (discAngularIterate_contDiffOn hf k)).congr
  exact fun z hz => discAngularIterate_green_commutes hf k (Metric.ball_subset_closedBall hz)

theorem discAngularIterate_green_laplacian {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) (k : ℕ)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    LeafCandidates.planarLaplacian (discAngularIterate k (discGreenSolution f)) z =
      discAngularIterate k f z := by
  have hA : ContDiffAt ℝ 2 (discAngularIterate k (discGreenSolution f)) z :=
    ((discAngularIterate_green_contDiffOn_interior hf k).contDiffAt
      (Metric.isOpen_ball.mem_nhds hz)).of_le (by simp)
  have hG : ContDiffAt ℝ 2 (discGreenSolution (discAngularIterate k f)) z :=
    ((discGreenSolution_contDiffOn_interior (discAngularIterate_contDiffOn hf k)).contDiffAt
      (Metric.isOpen_ball.mem_nhds hz)).of_le (by simp)
  have heq : discAngularIterate k (discGreenSolution f) =ᶠ[𝓝 z]
      discGreenSolution (discAngularIterate k f) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact discAngularIterate_green_commutes hf k (Metric.ball_subset_closedBall hw)
  rw [disc_planarLaplacian_eq_laplacian hA,
    (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds,
    ← disc_planarLaplacian_eq_laplacian hG]
  exact discGreenSolution_laplacian (discAngularIterate_contDiffOn hf k) hz

end Yau.LeafProofs
