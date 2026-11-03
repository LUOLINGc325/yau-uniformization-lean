import Yau.LeafProofs.L17HolomorphicCauchy

/-!
Continuity and one further complex derivative of the single-circle formula.
Finite-dimensional reconstruction then gives joint Fréchet smoothness.
-/

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff

namespace Yau.LeafProofs.L17Holomorphic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def lineIntegral (R : ℝ) (v : E) (g : E → F) (x : E) : F :=
  ∫ θ in Icc 0 (2 * Real.pi), lineWeight R θ • g (x + circleMap 0 R θ • v)

omit [CompleteSpace F] in
theorem lineIntegrand_continuous {s : Set E} {g : E → F}
    (hg : ContinuousOn g s) {x v : E} {R : ℝ} (hR : 0 < R)
    (hc : ∀ θ, x + circleMap 0 R θ • v ∈ s) :
    Continuous (fun θ => lineWeight R θ • g (x + circleMap 0 R θ • v)) := by
  exact (lineWeight_continuous hR).smul
    (hg.comp_continuous (continuous_const.add
      ((continuous_circleMap 0 R).smul continuous_const)) hc)

omit [CompleteSpace F] in
theorem lineIntegrand_integrable {s : Set E} {g : E → F}
    (hg : ContinuousOn g s) {x v : E} {R : ℝ} (hR : 0 < R)
    (hc : ∀ θ, x + circleMap 0 R θ • v ∈ s) :
    IntegrableOn (fun θ => lineWeight R θ • g (x + circleMap 0 R θ • v))
      (Icc 0 (2 * Real.pi)) :=
  (lineIntegrand_continuous hg hR hc).integrableOn_Icc

variable [FiniteDimensional ℂ E]

omit [CompleteSpace F] in
/-- The local Cauchy integral is continuous using only continuity of its data. -/
theorem continuousAt_lineIntegral {s : Set E} {g : E → F}
    (hs : IsOpen s) (hg : ContinuousOn g s) (a v : E) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closedBall a ρ ⊆ s) :
    ContinuousAt (lineIntegral ((ρ / 4) / (1 + ‖v‖)) v g) a := by
  let := FiniteDimensional.proper ℂ E
  let R := (ρ / 4) / (1 + ‖v‖)
  have hr : 0 < ρ / 4 := by positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hKsub : closedBall a (ρ / 2) ⊆ s := by
    intro y hy
    apply hsub
    exact mem_closedBall.mpr ((mem_closedBall.mp hy).trans (by linarith))
  obtain ⟨B, hB⟩ := (isCompact_closedBall a (ρ / 2)).exists_bound_of_continuousOn
    (hg.mono hKsub)
  have htube (x : E) (hx : x ∈ closedBall a (ρ / 4)) (θ : ℝ) :
      x + circleMap 0 R θ • v ∈ closedBall a (ρ / 2) :=
    lineTube_mem_closedBall hρ hx (circleMap_mem_closedBall hR θ)
  have hθ (x : E) (hx : x ∈ closedBall a (ρ / 4)) :
      Continuous (fun θ => lineWeight R θ • g (x + circleMap 0 R θ • v)) :=
    lineIntegrand_continuous hg hR (fun θ => hKsub (htube x hx θ))
  let C := ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ / R
  have hC : 0 ≤ C := div_nonneg (norm_nonneg _) hR.le
  unfold lineIntegral
  change ContinuousAt (fun x => ∫ θ in Icc 0 (2 * Real.pi),
    lineWeight R θ • g (x + circleMap 0 R θ • v)) a
  apply continuousAt_of_dominated (bound := fun _ : ℝ => C * B)
  · filter_upwards [ball_mem_nhds a hr] with x hx
    exact (hθ x (ball_subset_closedBall hx)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds a hr] with x hx
    exact Eventually.of_forall fun θ => by
      rw [norm_smul, lineWeight_norm hR]
      exact mul_le_mul_of_nonneg_left (hB _ (htube x (ball_subset_closedBall hx) θ)) hC
  · exact continuous_const.integrableOn_Icc
  · exact Eventually.of_forall fun θ =>
      continuousAt_const.smul ((hg.continuousAt (hs.mem_nhds
        (hKsub (htube a (mem_closedBall_self hr.le) θ)))).comp
          (f := fun x : E => x + circleMap 0 R θ • v)
          (continuousAt_id.add continuousAt_const))

/-- First complex differentiability already makes the whole derivative continuous. -/
theorem continuousOn_fderiv_of_complex {s : Set E} {f : E → F}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    ContinuousOn (fderiv ℂ f) s := by
  apply continuousOn_clm_apply.mpr
  intro v a ha
  obtain ⟨ρ, hρ, hsub⟩ := exists_closedBall_subset hs ha
  have hR : 0 < (ρ / 4) / (1 + ‖v‖) := by positivity
  have hc := continuousAt_lineIntegral hs hf.continuousOn a v hρ hsub
  apply ContinuousAt.continuousWithinAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds a (by positivity : 0 < ρ / 4)] with x hx
  exact (directional_eq_lineIntegral hs hf hR
    (fun ζ hζ => lineTube_mem hρ hsub (ball_subset_closedBall hx) hζ)).symm

/-- The operator-valued integral used for the next derivative is genuinely integrable. -/
theorem lineDerivative_integrable {s : Set E} {f : E → F}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) (a v : E) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closedBall a ρ ⊆ s) :
    IntegrableOn (fun θ => lineWeight ((ρ / 4) / (1 + ‖v‖)) θ •
      fderiv ℂ f (a + circleMap 0 ((ρ / 4) / (1 + ‖v‖)) θ • v))
      (Icc 0 (2 * Real.pi)) := by
  have hr : 0 < ρ / 4 := by positivity
  have hR : 0 < (ρ / 4) / (1 + ‖v‖) := by positivity
  exact lineIntegrand_integrable (continuousOn_fderiv_of_complex hs hf) hR
    (fun θ => lineTube_mem hρ hsub (mem_closedBall_self hr.le)
      (circleMap_mem_closedBall hR θ))

/-- One complex Fréchet parameter derivative under a fixed circle integral. -/
theorem hasFDerivAt_lineIntegral {s : Set E} {f : E → F}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) (a v : E) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closedBall a ρ ⊆ s) :
    HasFDerivAt (lineIntegral ((ρ / 4) / (1 + ‖v‖)) v f)
      (∫ θ in Icc 0 (2 * Real.pi), lineWeight ((ρ / 4) / (1 + ‖v‖)) θ •
        fderiv ℂ f (a + circleMap 0 ((ρ / 4) / (1 + ‖v‖)) θ • v)) a := by
  let := FiniteDimensional.proper ℂ E
  let R := (ρ / 4) / (1 + ‖v‖)
  have hr : 0 < ρ / 4 := by positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hKsub : closedBall a (ρ / 2) ⊆ s := by
    intro y hy
    apply hsub
    exact mem_closedBall.mpr ((mem_closedBall.mp hy).trans (by linarith))
  have hDf := continuousOn_fderiv_of_complex hs hf
  obtain ⟨B, hB⟩ := (isCompact_closedBall a (ρ / 2)).exists_bound_of_continuousOn
    (hDf.mono hKsub)
  have htube (x : E) (hx : x ∈ closedBall a (ρ / 4)) (θ : ℝ) :
      x + circleMap 0 R θ • v ∈ closedBall a (ρ / 2) :=
    lineTube_mem_closedBall hρ hx (circleMap_mem_closedBall hR θ)
  have hθ (x : E) (hx : x ∈ closedBall a (ρ / 4)) :
      Continuous (fun θ => lineWeight R θ • f (x + circleMap 0 R θ • v)) :=
    lineIntegrand_continuous hf.continuousOn hR (fun θ => hKsub (htube x hx θ))
  let C := ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ / R
  have hC : 0 ≤ C := div_nonneg (norm_nonneg _) hR.le
  unfold lineIntegral
  change HasFDerivAt (fun x => ∫ θ in Icc 0 (2 * Real.pi),
    lineWeight R θ • f (x + circleMap 0 R θ • v))
    (∫ θ in Icc 0 (2 * Real.pi), lineWeight R θ •
      fderiv ℂ f (a + circleMap 0 R θ • v)) a
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun x θ => lineWeight R θ • fderiv ℂ f (x + circleMap 0 R θ • v))
    (bound := fun _ : ℝ => C * B) (s := ball a (ρ / 4)) (ball_mem_nhds a hr)
  · filter_upwards [ball_mem_nhds a hr] with x hx
    exact (hθ x (ball_subset_closedBall hx)).aestronglyMeasurable
  · exact (hθ a (mem_closedBall_self hr.le)).integrableOn_Icc
  · exact (lineIntegrand_continuous hDf hR
      (fun θ => hKsub (htube a (mem_closedBall_self hr.le) θ))).aestronglyMeasurable
  · exact Eventually.of_forall fun θ x hx => by
      rw [norm_smul, lineWeight_norm hR]
      exact mul_le_mul_of_nonneg_left (hB _ (htube x (ball_subset_closedBall hx) θ)) hC
  · exact continuous_const.integrableOn_Icc
  · exact Eventually.of_forall fun θ x hx => by
      have hinner : HasFDerivAt (fun y : E => y + circleMap 0 R θ • v)
          (ContinuousLinearMap.id ℂ E) x := (hasFDerivAt_id x).add_const _
      have hd := (hf.differentiableAt (hs.mem_nhds
        (hKsub (htube x (ball_subset_closedBall hx) θ)))).hasFDerivAt.comp x hinner
      simpa only [ContinuousLinearMap.comp_id, Pi.smul_def, Function.comp_def] using
        hd.const_smul (lineWeight R θ)

/-- Directional differentiation preserves complex differentiability on the same open set. -/
theorem differentiableOn_directional_of_complex {s : Set E} {f : E → F}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) (v : E) :
    DifferentiableOn ℂ (fun x => fderiv ℂ f x v) s := by
  intro a ha
  obtain ⟨ρ, hρ, hsub⟩ := exists_closedBall_subset hs ha
  have hR : 0 < (ρ / 4) / (1 + ‖v‖) := by positivity
  have hd := hasFDerivAt_lineIntegral hs hf a v hρ hsub
  apply DifferentiableAt.differentiableWithinAt
  apply HasFDerivAt.differentiableAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds a (by positivity : 0 < ρ / 4)] with x hx
  exact (directional_eq_lineIntegral hs hf hR
    (fun ζ hζ => lineTube_mem hρ hsub (ball_subset_closedBall hx) hζ)).symm

theorem allNat {s : Set E} (hs : IsOpen s) :
    ∀ k : ℕ, ∀ f : E → F, DifferentiableOn ℂ f s → ContDiffOn ℂ k f s := by
  intro k
  induction k with
  | zero =>
      intro f hf
      simpa only [Nat.cast_zero, contDiffOn_zero] using hf.continuousOn
  | succ k ih =>
      intro f hf
      have hdir : ∀ v : E,
          ContDiffOn ℂ (k : ℕ∞ω) (fun x => fderivWithin ℂ f s x v) s := by
        intro v
        have h := ih (fun x => fderiv ℂ f x v)
          (differentiableOn_directional_of_complex hs hf v)
        exact h.congr (fun x hx => by rw [fderivWithin_of_isOpen hs hx])
      have hstep : ContDiffOn ℂ ((k : ℕ∞ω) + 1) f s :=
        contDiffOn_succ_of_fderiv_apply hf (by simp) hdir
      simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hstep

theorem contDiffOn_of_complexDiff {s : Set E} {f : E → F}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    ContDiffOn ℂ ∞ f s :=
  contDiffOn_infty.mpr (fun k => allNat hs k f hf)

theorem real_contDiffOn_of_complexDiff {s : Set E} {f : E → F}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    ContDiffOn ℝ ∞ f s :=
  (contDiffOn_of_complexDiff hs hf).restrict_scalars ℝ

theorem complexVector_contDiffOn {n m : ℕ} {s : Set (Yau.ComplexVector n)}
    {T : Yau.ComplexVector n → Yau.ComplexVector m}
    (hs : IsOpen s) (hT : DifferentiableOn ℂ T s) :
    ContDiffOn ℂ ∞ T s := contDiffOn_of_complexDiff hs hT

theorem complexVector_real_contDiffOn {n m : ℕ} {s : Set (Yau.ComplexVector n)}
    {T : Yau.ComplexVector n → Yau.ComplexVector m}
    (hs : IsOpen s) (hT : DifferentiableOn ℂ T s) :
    ContDiffOn ℝ ∞ T s := (complexVector_contDiffOn hs hT).restrict_scalars ℝ

end Yau.LeafProofs.L17Holomorphic
