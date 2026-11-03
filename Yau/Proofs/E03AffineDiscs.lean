import Yau.Proofs.E03JointSmooth
import Yau.Proofs.V03CotangentSmooth

/-! Actual holomorphic cotangent discs induced by affine joint coordinates. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem affine_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p v : E) : ContDiff ℂ ∞ (fun ζ : ℂ => p + ζ • v) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

theorem chart_affine_isCotangentDisc (c : M.Carrier)
    (z η a u : ComplexVector n)
    (hdisc : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, z + ζ • a ∈ chartTarget c) :
    IsCotangentDisc (fun ζ => chartInv c (z + ζ • a))
      (fun ζ => covectorOfCoords c (chartInv c (z + ζ • a)) (η + ζ • u)) := by
  let q : ℂ → CotangentCoord n := fun ζ => (z + ζ • a, η + ζ • u)
  have hq : ContDiff ℂ ∞ q := (affine_contDiff z a).prodMk (affine_contDiff η u)
  refine ⟨?_, ?_⟩
  · intro ζ hζ
    have hi : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞
        (chartInv c) (z + ζ • a) :=
      (contMDiffOn_extChartAt_symm (I := ComplexModel n) c).contMDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds (hdisc ζ hζ))
    exact (hi.comp ζ (affine_contDiff z a).contMDiff.contMDiffAt).contMDiffWithinAt
  · intro ζ hζ
    have htrans := cotangentChartTransition_contDiffAt c (chartInv c (z + ζ • a))
      (z := q ζ) ⟨hdisc ζ hζ, Set.mem_univ _⟩ (mem_extChartAt_source _)
    have hc := ContDiffAt.comp
      (g := fun p : CotangentCoord n => cotangentChart (chartInv c (z + ζ • a)) (cotangentChartInv c p))
      (f := q) ζ htrans hq.contDiffAt
    exact hc.snd.contDiffWithinAt

end Yau.NodeProofs.E03Aux
