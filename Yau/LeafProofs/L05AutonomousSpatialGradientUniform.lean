import Yau.LeafProofs.L05AutonomousSpatialGradientCalculus
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Cauchy

open Filter Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2200000
namespace Yau.LeafProofs.L05AutonomousAux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Closed spatial collar with both temporal endpoints retained. -/
def spatialGradientCylinder (V : Type*) [NormedAddCommGroup V] (r a b : ℝ) : Set (V × ℝ) :=
  closedBall (0 : V) r ×ˢ Icc a b

/-- The actual spatial first Frechet derivative. -/
def spatialGradientOf (f : V × ℝ → ℝ) (p : V × ℝ) : V →L[ℝ] ℝ :=
  fderiv ℝ (fun x => f (x, p.2)) p.1

/-- Actual uniform C0 convergence and a Hessian budget imply uniformly Cauchy actual gradients. -/
theorem spatialGradient_uniform_cauchy {r R a b B : ℝ} (hrR : r < R) (hB : 0 ≤ B)
    (f : ℕ → V × ℝ → ℝ) (u : V × ℝ → ℝ)
    (hf : ∀ j, ∀ t ∈ Icc a b, ContDiff ℝ ∞ (fun x => f j (x, t)))
    (hH : ∀ j, ∀ p ∈ spatialGradientCylinder V R a b,
      ‖fderiv ℝ (fderiv ℝ (fun x => f j (x, p.2))) p.1‖ ≤ B)
    (hu : TendstoUniformlyOn f u atTop (spatialGradientCylinder V R a b)) :
    UniformCauchySeqOn (fun j => spatialGradientOf (f j)) atTop (spatialGradientCylinder V r a b) := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro eps heps
  let step := min ((R - r) / 2) (eps / (8 * (1 + B)))
  have hstep : 0 < step := lt_min (by linarith) (by positivity)
  have hbuffer : r + step ≤ R := by have := min_le_left ((R-r)/2) (eps/(8*(1+B))); dsimp [step]; linarith
  have hsmall : 8 * (1 + B) * step ≤ eps := by
    have hh : step ≤ eps/(8*(1+B)) := min_le_right _ _
    have hm := (le_div_iff₀ (by positivity : 0 < 8*(1+B))).mp hh
    nlinarith
  let delta := eps * step / 8
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hu.uniformCauchySeqOn delta hdelta
  refine ⟨N, ?_⟩
  intro j hj k hk p hp
  have hbound : ‖spatialGradientOf (f j) p - spatialGradientOf (f k) p‖ ≤
      2 * delta / step + 2 * B * step := by
    exact spatialGradient_interpolation (hf j p.2 hp.2) (hf k p.2 hp.2)
      hstep hbuffer hB hdelta.le
      (fun z hz => hH j (z, p.2) ⟨hz, hp.2⟩)
      (fun z hz => hH k (z, p.2) ⟨hz, hp.2⟩)
      (fun z hz => by simpa only [Real.dist_eq] using (hN j hj k hk (z,p.2) ⟨hz,hp.2⟩).le)
      hp.1
  rw [dist_eq_norm]
  apply hbound.trans_lt
  have hfrac : 2 * delta / step = eps / 4 := by dsimp [delta]; field_simp [hstep.ne']; ring
  rw [hfrac]
  nlinarith [mul_nonneg hB hstep.le]

/-- Completeness gives the actual jointly continuous gradient limit on a closed collar. -/
theorem spatialGradient_exists_uniform_limit {r R a b B : ℝ} (hrR : r < R) (hB : 0 ≤ B)
    (f : ℕ → V × ℝ → ℝ) (u : V × ℝ → ℝ)
    (hf : ∀ j, ∀ t ∈ Icc a b, ContDiff ℝ ∞ (fun x => f j (x, t)))
    (hH : ∀ j, ∀ p ∈ spatialGradientCylinder V R a b,
      ‖fderiv ℝ (fderiv ℝ (fun x => f j (x, p.2))) p.1‖ ≤ B)
    (hg : ∀ j, ContinuousOn (spatialGradientOf (f j)) (spatialGradientCylinder V R a b))
    (hu : TendstoUniformlyOn f u atTop (spatialGradientCylinder V R a b)) :
    ∃ G : V × ℝ → (V →L[ℝ] ℝ),
      ContinuousOn G (spatialGradientCylinder V r a b) ∧
      TendstoUniformlyOn (fun j => spatialGradientOf (f j)) G atTop (spatialGradientCylinder V r a b) := by
  classical
  have hC := spatialGradient_uniform_cauchy hrR hB f u hf hH hu
  have hpoint : ∀ p ∈ spatialGradientCylinder V r a b,
      ∃ v : V →L[ℝ] ℝ, Tendsto (fun j => spatialGradientOf (f j) p) atTop (𝓝 v) := by
    intro p hp
    exact cauchySeq_tendsto_of_complete (hC.cauchySeq hp)
  let G : V × ℝ → (V →L[ℝ] ℝ) := fun p =>
    if hp : p ∈ spatialGradientCylinder V r a b then (hpoint p hp).choose else 0
  have hlim : TendstoUniformlyOn (fun j => spatialGradientOf (f j)) G atTop (spatialGradientCylinder V r a b) :=
    hC.tendstoUniformlyOn_of_tendsto (fun p hp => by simpa [G, hp] using (hpoint p hp).choose_spec)
  refine ⟨G, ?_, hlim⟩
  apply hlim.continuousOn
  exact (Filter.Eventually.of_forall (fun j => (hg j).mono (by
    intro p hp
    exact ⟨closedBall_subset_closedBall hrR.le hp.1, hp.2⟩))).frequently

end Yau.LeafProofs.L05AutonomousAux
