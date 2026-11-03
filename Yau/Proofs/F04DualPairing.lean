import Yau.Proofs.F04FiniteMass

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace Yau.F04Proof

/-- Actual Bochner L2 primal/dual curves have a genuinely integrable pairing. -/
theorem dualPairing_integrable_L2 {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure X}
    {u : X → V} {R : X → StrongDual ℝ V} (hu : MemLp u 2 μ) (hR : MemLp R 2 μ) :
    Integrable (fun t => R t (u t)) μ := by
  have hm : AEStronglyMeasurable (fun t => R t (u t)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hR.aestronglyMeasurable.prodMk hu.aestronglyMeasurable)
  exact (hR.norm.integrable_mul hu.norm).mono' hm (ae_of_all μ fun t => (R t).le_opNorm (u t))

end Yau.F04Proof
