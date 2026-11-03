import Yau.Proofs.V04MatrixGagliardo
import Yau.Proofs.V04BoundaryRegularity
import Yau.Proofs.V03CirclePeriod
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric

/-! The original symbol bounds pass to its actual negative part with the
same constant. Its Fourier seminorm is the original component-summed
seminorm, including infinite endpoints and zero matrix rank. -/

open scoped Matrix Topology ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

open scoped Matrix.Norms.L2Operator in
theorem rectOpNorm_negative_le (A : CotangentMatrix n) (hA : A.IsHermitian) :
    rectOpNorm (matrixNegative A) ≤ rectOpNorm A := by
  change ‖matrixNegative A‖ ≤ ‖A‖
  rw [matrixNegative_eq_negPart A hA]
  exact CStarAlgebra.norm_negPart_le A

theorem negative_symbol_bounds {d : VariationData X q} (hd : VariationSetup d)
    {a : ℕ} (ha : 4 ≤ a) (hsymbol : SymbolBounds d a) :
    ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
      (∀ θ, (matrixNegative (boundarySymbol d j a F E (circlePoint θ))).PosSemidef ∧
        rectOpNorm (matrixNegative (boundarySymbol d j a F E (circlePoint θ))) ≤ C) ∧
      matrixDSq (fun θ => matrixNegative (boundarySymbol d j a F E (circlePoint θ))) ≤
        ENNReal.ofReal C * (1 + variationEnergy d j F) := by
  intro j
  obtain ⟨C, hC, hbound⟩ := hsymbol j
  refine ⟨C, hC, fun F E hF hE => ?_⟩
  have hT := hbound F E hF hE
  refine ⟨fun θ => ⟨matrixNegative_posSemidef _,
    (rectOpNorm_negative_le _ (hT.1 θ).1).trans (hT.1 θ).2⟩, ?_⟩
  exact (matrixDSq_negative_le
    (fun i k => (boundarySymbol_trace_contDiff hd j a ha F hF E hE i k).continuous)
    (circleTrace_periodic (boundarySymbol d j a F E)) (fun θ => (hT.1 θ).1)).trans hT.2

end Yau.Blueprint.V04Proof
