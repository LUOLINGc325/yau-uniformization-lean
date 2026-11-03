import Yau.Proofs.V03NativeMaps
import Yau.Proofs.V03HolomorphicSmooth

/-! Actual ambient smoothness of cotangent discs and joint families, derived
from the original chartwise holomorphic immersion hypothesis. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

theorem nativeCotangentMap_contMDiff
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G) :
    ContMDiff 𝓘(ℂ, CotangentCoord n) (ComplexModel q) ∞
      (fun y : NativeCotangentPoint M => G y.val) := by
  intro y
  apply contMDiffAt_iff.mpr
  refine ⟨(nativeCotangentMap_continuous hG).continuousAt, ?_⟩
  have htarget : cotangentChart y.val.1 y.val ∈ cotangentTarget y.val.1 :=
    cotangentChart_mapsTo y.val.1 (mem_extChartAt_source y.val.1)
  have hAt : ContDiffAt ℂ ∞ (fun z => G (cotangentChartInv y.val.1 z))
      (cotangentChart y.val.1 y.val) :=
    (cotangentHolomorphic_chart_contDiffOn hG y.val.1).contDiffAt
      (((isOpen_extChartAt_target (I := ComplexModel n) y.val.1).prod isOpen_univ).mem_nhds htarget)
  simp only [mfld_simps]
  change ContDiffWithinAt ℂ ∞
    (fun z => G (cotangentChartInv y.val.1 z)) Set.univ (cotangentChart y.val.1 y.val)
  exact hAt.contDiffWithinAt

theorem cotangentHolomorphicOn_ambient_contDiffOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    {f : E → CotangentPoint M} (hf : CotangentHolomorphicOn f S)
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G) :
    ContDiffOn ℂ ∞ (fun z => G (f z)) S :=
  ((nativeCotangentMap_contMDiff hG).comp_contMDiffOn
    (cotangentHolomorphicOn_native_contMDiffOn hf)).contDiffOn

theorem cotangentDisc_ambient_contDiffOn {f : ℂ → CotangentPoint M}
    (hf : CotangentDisc f) {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) :
    ContDiffOn ℂ ∞ (fun z => G (f z)) (Metric.closedBall 0 1) :=
  cotangentHolomorphicOn_ambient_contDiffOn (cotangentDisc_holomorphicOn hf) hG

end Yau.Blueprint.V03Proof
