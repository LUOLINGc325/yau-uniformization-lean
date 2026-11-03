import Yau.Proofs.C02TransportScale

/-! Parallel transport along the same physical radial geodesic is unchanged
by moving the scalar speed into the time argument. -/

noncomputable section
open scoped Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem mfderiv_transportVelocityScale_spray (g : SmoothMetric M) (c : ℝ)
    (q : realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    mfderiv (realTransportModel n) (realTransportModel n) (transportVelocityScale c) q
      (c • realParallelTransportSpray g q) = realParallelTransportSpray g (transportVelocityScale c q) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  rw [mfderiv_transportVelocityScale]
  change transportScaleCLM n c (c • chartParallelTransportField g.form q.proj (realTransportChart q.proj q)) =
    chartParallelTransportField g.form q.proj (realTransportChart q.proj (transportVelocityScale c q))
  rw [realTransportChart_scale, transportScaleCLM_apply]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change c • (c • (-chartChristoffelBilin g.form q.proj
        (realTransportChart q.proj q).1 (realTransportChart q.proj q).2.1
        (realTransportChart q.proj q).2.1)) =
      -chartChristoffelBilin g.form q.proj (realTransportChart q.proj q).1
        (c • (realTransportChart q.proj q).2.1) (c • (realTransportChart q.proj q).2.1)
      simp only [map_smul, smul_apply, smul_neg]
    · change c • (-chartChristoffelBilin g.form q.proj
        (realTransportChart q.proj q).1 (realTransportChart q.proj q).2.1
        (realTransportChart q.proj q).2.2) =
      -chartChristoffelBilin g.form q.proj (realTransportChart q.proj q).1
        (c • (realTransportChart q.proj q).2.1) (realTransportChart q.proj q).2.2
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_neg]

theorem parallelTransport_rescale (g : SmoothMetric M)
    (γ : ℝ → realTransportBundle M) (c : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    IsMIntegralCurve γ (realParallelTransportSpray g) →
      IsMIntegralCurve (transportVelocityScale c ∘ γ ∘ (· * c)) (realParallelTransportSpray g) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  intro hγ t
  have hm := hγ.comp_mul c
  have hH := ((transportVelocityScale_smooth (M := M) c (γ (t * c))).mdifferentiableAt
    (by simp)).hasMFDerivAt
  have hcomp := hH.comp t (hm t)
  apply hcomp.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  let a₀ : ℝ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) t) a
  change mfderiv (realTransportModel n) (realTransportModel n) (transportVelocityScale c) (γ (t * c))
      (a₀ • (c • realParallelTransportSpray g (γ (t * c)))) =
    a₀ • realParallelTransportSpray g (transportVelocityScale c (γ (t * c)))
  rw [map_smul, mfderiv_transportVelocityScale_spray]

theorem parallelTransportFlow_rescale (g : SmoothMetric M) (c : ℝ)
    (p : realTransportBundle M) (t : ℝ) :
    realParallelTransportFlow g (transportVelocityScale c p) t =
      transportVelocityScale c (realParallelTransportFlow g p (t * c)) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  have h := realParallelTransportFlow_unique g (transportVelocityScale c p)
    (transportVelocityScale c ∘ realParallelTransportFlow g p ∘ (· * c))
    (by simp [realParallelTransportFlow_zero])
    (parallelTransport_rescale g (realParallelTransportFlow g p) c
      (realParallelTransportFlow_integral g p))
  exact (congrFun h t).symm

end Yau.Blueprint.C02Proof
