import Yau.Proofs.V03SymbolTraceBound

/-! Continuity of the original boundary quadratic test follows from the
actual ambient tensor and the supplied smooth frame and column. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem boundary_quadratic_continuous {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 4 ≤ a) (F : VariationDisc X)
    (hF : AdmissibleVariationDisc d j F) (E : ℂ → CotangentMatrix n)
    (hE : NormalizedDiscFrame d.G F.f E) (l : ℂ → CotangentIndex n → ℂ)
    (hl : HolomorphicColumn l) :
    Continuous (fun θ => quadValue (boundarySymbol d j a F E (circlePoint θ))
      (l (circlePoint θ))) := by
  have hU : Continuous (fun θ => ambientFrame d.G F.f E (circlePoint θ)) :=
    continuous_pi (fun i => continuous_pi (fun k =>
      (ambientFrame_entry_contDiffOn hE.1 hd.2.2.2.2.1.1 i k).continuousOn.comp_continuous
        circlePoint_contDiff.continuous circlePoint_mem_closedBall))
  have hT := boundaryAmbientTensor_continuous hd j a ha hF
  have heq : (fun θ => boundarySymbol d j a F E (circlePoint θ)) =
      fun θ => (ambientFrame d.G F.f E (circlePoint θ))ᴴ *
        boundaryAmbientTensor d j a F θ * ambientFrame d.G F.f E (circlePoint θ) := by
    funext θ
    exact boundarySymbol_eq_boundaryAmbientTensor hd j a ha F hF E θ
  have hB : Continuous (fun θ => boundarySymbol d j a F E (circlePoint θ)) := by
    rw [heq]
    exact (hU.matrix_conjTranspose.matrix_mul hT).matrix_mul hU
  have hcol : Continuous (fun θ => l (circlePoint θ)) :=
    continuous_pi (fun i => (hl i).continuousOn.comp_continuous
      circlePoint_contDiff.continuous circlePoint_mem_closedBall)
  exact Complex.continuous_re.comp (hcol.star.dotProduct (hB.matrix_mulVec hcol))

end Yau.Blueprint.V02Proof
