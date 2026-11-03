import Yau.Proofs.V03RealizedCurrentAtom

/-! The actual signed current atoms are continuous angular traces, so
their original interval integrals commute with finite sums. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem realizedCurrentAtom_continuous {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ)
    {B : CotangentPoint X.manifold → Matrix (Fin q) (Fin q) ℂ}
    (hB : ∀ x b c, ContDiffOn ℝ ∞ (fun z => B (cotangentChartInv x z) b c) (cotangentTarget x))
    (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
    (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R)
    (i₁ i₂ : Option (Fin q)) (k : TensorFirstCoefficientIndex q) (s : Fin 4) (w : Fin q ⊕ Fin q) :
    Continuous (realizedCurrentAtom d B F E l h α i₁ i₂ k s w) := by
  let V := ambientVelocity d F E l h α
  have hV := realized_ambientVelocity_contDiffOn hd j a F E l h α fz R hR
  have hu := (currentVelocityFactor_contDiffOn hV i₁).continuousOn.comp_continuous
    circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hv := (currentVelocityFactor_contDiffOn hV i₂).continuousOn.comp_continuous
    circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hb := cotangentCoefficient_trace_continuous hd
    (b := fun y => tensorCurrentCoefficient d.G B k s y)
    (fun x => tensorCurrentCoefficient_chart_contDiffOn hd.2.2.2.2.1 hB k s x) hF
  have hf := currentDerivativeFunction_contDiffOn hd.2.2.2.2.1.1 hF.1 hV w
  exact Complex.reCLM.continuous.comp (((hu.star.mul hb).mul hv).mul
    (holomorphicAngularTrace_continuous hf))

end Yau.Blueprint.V03Proof
