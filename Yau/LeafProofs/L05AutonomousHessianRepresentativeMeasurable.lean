import Yau.Blueprint.ParabolicSpaces
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

noncomputable section
open Set MeasureTheory
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_hessian_piecewise_stronglyMeasurable {n : ℕ} {E : Type*}
    [instE : NormedAddCommGroup E] [instSecond : SecondCountableTopology E]
    {Q : Set (Point n)} [instDecidableQ : DecidablePred (fun p => p ∈ Q)]
    (hQ : MeasurableSet Q) {f : Point n → E}
    (hf : ContinuousOn f Q) : StronglyMeasurable (Q.piecewise f (fun _ => 0)) := by
  classical
  letI autoHessianRepTargetMeasurableSpace : MeasurableSpace E := borel E
  letI autoHessianRepTargetBorelSpace : BorelSpace E := ⟨rfl⟩
  exact (hf.measurable_piecewise continuousOn_const hQ).stronglyMeasurable

theorem auto_hessian_piecewise_continuousOn {n : ℕ} {E : Type*}
    [instE : NormedAddCommGroup E] {Q : Set (Point n)}
    [instDecidableQ : DecidablePred (fun p => p ∈ Q)] {f : Point n → E}
    (hf : ContinuousOn f Q) : ContinuousOn (Q.piecewise f (fun _ => 0)) Q := by
  classical
  apply hf.congr
  intro p hp
  simp only [Set.piecewise,if_pos hp]

end Yau.LeafProofs.L05AutonomousAux
