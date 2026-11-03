import Yau.Proofs.C02TransportDiagonal

/-! The velocity of the chosen physical geodesic is precisely the parallel
transport of its initial velocity, by uniqueness of the actual transport ODE. -/

noncomputable section
open scoped Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem mfderiv_phaseDuplicate_spray (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := manifold_realTransport M
    mfderiv (realPhaseModel n) (realTransportModel n) phaseDuplicate q
      (realGeodesicSpray g q) = realParallelTransportSpray g (phaseDuplicate q) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  rw [mfderiv_phaseDuplicate]
  change phaseDuplicateCLM n (chartGeodesicSpray g.form q.proj (realPhaseChart q.proj q)) =
    chartParallelTransportField g.form q.proj (realTransportChart q.proj (phaseDuplicate q))
  rw [realTransportChart_duplicate, phaseDuplicateCLM_apply]
  change ((realPhaseChart q.proj q).2,
    (chartGeodesicAcceleration g.form q.proj (realPhaseChart q.proj q).1 (realPhaseChart q.proj q).2,
      chartGeodesicAcceleration g.form q.proj (realPhaseChart q.proj q).1 (realPhaseChart q.proj q).2)) =
    ((realPhaseChart q.proj q).2,
      (-chartChristoffelBilin g.form q.proj (realPhaseChart q.proj q).1
        (realPhaseChart q.proj q).2 (realPhaseChart q.proj q).2,
      -chartChristoffelBilin g.form q.proj (realPhaseChart q.proj q).1
        (realPhaseChart q.proj q).2 (realPhaseChart q.proj q).2))
  rw [chartGeodesicAcceleration_eq]

theorem phaseDuplicate_integral (g : SmoothMetric M)
    (γ : ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := manifold_realTransport M
    IsMIntegralCurve γ (realGeodesicSpray g) →
      IsMIntegralCurve (phaseDuplicate ∘ γ) (realParallelTransportSpray g) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  intro hγ t
  have hD := ((phaseDuplicate_smooth (M := M) (γ t)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp := hD.comp t (hγ t)
  apply hcomp.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  let a₀ : ℝ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) t) a
  change mfderiv (realPhaseModel n) (realTransportModel n) phaseDuplicate (γ t)
      (a₀ • realGeodesicSpray g (γ t)) = a₀ • realParallelTransportSpray g (phaseDuplicate (γ t))
  rw [map_smul, mfderiv_phaseDuplicate_spray]

theorem parallelTransportFlow_velocity_diagonal (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    realParallelTransportFlow g (phaseDuplicate p) t = phaseDuplicate (realGeodesicFlow g p t) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  have heq := realParallelTransportFlow_unique g (phaseDuplicate p) (phaseDuplicate ∘ realGeodesicFlow g p)
    (by rw [Function.comp_apply, realGeodesicFlow_zero])
    (phaseDuplicate_integral g (realGeodesicFlow g p) (realGeodesicFlow_integral g p))
  exact (congrFun heq t).symm

theorem parallelField_velocity_totalSpace (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    (⟨(realGeodesicFlow g p t).proj, realParallelField g p p.2 t⟩ :
      TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = realGeodesicFlow g p t := by
  rw [realParallelField_totalSpace]
  change realTransportVector (realParallelTransportFlow g (phaseDuplicate p) t) = _
  rw [parallelTransportFlow_velocity_diagonal]
  rfl

end Yau.Blueprint.C02Proof
