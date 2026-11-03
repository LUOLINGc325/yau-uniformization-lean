import Yau.Proofs.P06HodgeRegularityCoordinates
import Mathlib.MeasureTheory.Constructions.Pi

/-! Genuine real chart coordinates preserve the original Lebesgue measure.
The coordinate dimension is finite even when n=0. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

def hodgeRegularityRealEquiv (n : ℕ) : ComplexVector n ≃L[ℝ] (RIdx n → ℝ) :=
  (realModelBasis n).equivFun.toContinuousLinearEquiv

theorem hodgeRegularityRealEquiv_symm_apply (n : ℕ) (r : RIdx n → ℝ) :
    (hodgeRegularityRealEquiv n).symm r = ∑ i, r i • realVec i := by
  change (realModelBasis n).equivFun.symm r = _
  simp only [Basis.equivFun_symm_apply, realModelBasis_apply]

theorem hodgeRegularityRealEquiv_symm_measurePreserving (n : ℕ) :
    MeasurePreserving (hodgeRegularityRealEquiv n).symm volume (lebesgueC n) := by
  refine ⟨(hodgeRegularityRealEquiv n).symm.continuous.measurable, ?_⟩
  have heq : ((hodgeRegularityRealEquiv n).symm : (RIdx n → ℝ) → ComplexVector n) =
      fun r => ∑ i, r i • realVec i := funext (hodgeRegularityRealEquiv_symm_apply n)
  rw [heq]
  rfl

theorem hodgeRegularityRealEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (hodgeRegularityRealEquiv n) (lebesgueC n) volume := by
  let e := (hodgeRegularityRealEquiv n).toHomeomorph.toMeasurableEquiv
  exact MeasurePreserving.symm e.symm (hodgeRegularityRealEquiv_symm_measurePreserving n)

def hodgeRegularityFinReindex (n : ℕ) :
    (RIdx n → ℝ) ≃L[ℝ] (Fin (Fintype.card (RIdx n)) → ℝ) :=
  (LinearEquiv.piCongrLeft (R := ℝ) (φ := fun _ : Fin (Fintype.card (RIdx n)) => ℝ)
    (Fintype.equivFin (RIdx n))).toContinuousLinearEquiv

theorem hodgeRegularityFinReindex_measurePreserving (n : ℕ) :
    MeasurePreserving (hodgeRegularityFinReindex n) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card (RIdx n)) => ℝ)
    (Fintype.equivFin (RIdx n))

def hodgeRegularityFinEquiv (n : ℕ) :
    ComplexVector n ≃L[ℝ] (Fin (Fintype.card (RIdx n)) → ℝ) :=
  (hodgeRegularityRealEquiv n).trans (hodgeRegularityFinReindex n)

theorem hodgeRegularityFinEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (hodgeRegularityFinEquiv n) (lebesgueC n) volume :=
  (hodgeRegularityFinReindex_measurePreserving n).comp (hodgeRegularityRealEquiv_measurePreserving n)

theorem hodgeRegularityFinEquiv_symm_measurePreserving (n : ℕ) :
    MeasurePreserving (hodgeRegularityFinEquiv n).symm volume (lebesgueC n) := by
  let e := (hodgeRegularityFinEquiv n).toHomeomorph.toMeasurableEquiv
  exact MeasurePreserving.symm e (hodgeRegularityFinEquiv_measurePreserving n)

end Yau.NodeProofs.P06Aux
