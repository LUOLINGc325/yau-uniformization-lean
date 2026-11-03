import Yau.Proofs.F04DiffusionIntegrationByParts

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.LeafProofs.L18Aux

/-- The actual derivative of a compact test times a locally C1 coefficient
 is a genuine global L2 test. Its two summands are precisely the flux and
 coefficient-drift terms appearing in the weak nondivergence operator. -/
theorem compactCoefficient_direction_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsLocallyFiniteMeasure μ]
    {O : Set E} (hO : IsOpen O) {η A : E → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O)
    (hA : ContDiffOn ℝ 1 A O) (v : E) :
    MemLp (fun x => A x * fderiv ℝ η x v + fderiv ℝ A x v * η x) 2 μ := by
  have hdη : Continuous (fun x => fderiv ℝ η x v) :=
    (hη.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcdη : HasCompactSupport (fun x => fderiv ℝ η x v) := hcη.fderiv_apply ℝ v
  have hdηO : tsupport (fun x => fderiv ℝ η x v) ⊆ O :=
    (tsupport_fderiv_apply_subset ℝ v).trans hηO
  have hdA : ContinuousOn (fun x => fderiv ℝ A x v) O :=
    (hA.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
  have hFlux : Continuous (fun x => fderiv ℝ η x v * A x) :=
    continuous_mul_of_continuousAt_tsupport hdη (fun x hx =>
      hA.continuousOn.continuousAt (hO.mem_nhds (hdηO hx)))
  have hDrift : Continuous (fun x => η x * fderiv ℝ A x v) :=
    continuous_mul_of_continuousAt_tsupport hη.continuous (fun x hx =>
      hdA.continuousAt (hO.mem_nhds (hηO hx)))
  have hh : MemLp (fun x => fderiv ℝ η x v * A x + η x * fderiv ℝ A x v) 2 μ :=
    (hFlux.add hDrift).memLp_of_hasCompactSupport
    (hcdη.mul_right.add hcη.mul_right)
  simpa only [mul_comm] using hh

end Yau.F04Proof
