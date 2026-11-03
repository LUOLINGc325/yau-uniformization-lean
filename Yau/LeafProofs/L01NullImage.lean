import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal

namespace Yau.LeafProofs.L01Aux

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Lipschitz self-maps preserve outer-null Lebesgue sets. -/
theorem lipschitz_image_volume_zero {P : E → E} {K : ℝ≥0} (hP : LipschitzWith K P)
    {s : Set E} (hs : volume s = 0) : volume (P '' s) = 0 := by
  let ν : Measure E := hausdorffMeasure (Module.finrank ℝ E : ℝ)
  have hνv : ν ≪ (volume : Measure E) :=
    Measure.absolutelyContinuous_isAddHaarMeasure ν volume
  have hvν : (volume : Measure E) ≪ ν :=
    Measure.absolutelyContinuous_isAddHaarMeasure volume ν
  have hνs : ν s = 0 := hνv hs
  apply hvν
  have h := hP.hausdorffMeasure_image_le
    (show 0 ≤ (Module.finrank ℝ E : ℝ) by positivity) s
  change ν (P '' s) ≤ (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) * ν s at h
  simpa only [hνs, mul_zero, nonpos_iff_eq_zero] using h

/-- The image of the nondifferentiable and critical sets is outer-null. -/
theorem exists_null_bad_image {P : E → E} {K : ℝ≥0} (hP : LipschitzWith K P) :
    ∃ B : Set E, volume B = 0 ∧
      ∀ y, P y ∉ B → DifferentiableAt ℝ P y ∧ (fderiv ℝ P y).det ≠ 0 := by
  let N : Set E := {y | ¬ DifferentiableAt ℝ P y}
  let C : Set E := {y | DifferentiableAt ℝ P y ∧ (fderiv ℝ P y).det = 0}
  have hN : volume N = 0 := ae_iff.mp (hP.ae_differentiableAt (μ := volume))
  have hPN : volume (P '' N) = 0 := lipschitz_image_volume_zero hP hN
  have hPC : volume (P '' C) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun y => fderiv ℝ P y)
      (fun y hy => hy.1.hasFDerivAt.hasFDerivWithinAt)
      (fun y hy => hy.2)
  refine ⟨P '' N ∪ P '' C, measure_union_null hPN hPC, ?_⟩
  intro y hy
  have hdiff : DifferentiableAt ℝ P y := by
    by_contra hn
    exact hy (Or.inl ⟨y, hn, rfl⟩)
  refine ⟨hdiff, ?_⟩
  intro hdet
  exact hy (Or.inr ⟨y, ⟨hdiff, hdet⟩, rfl⟩)

end Yau.LeafProofs.L01Aux
