import Yau.Proofs.F05JetNorms

/-! Actual Schauder functions are encoded by bounded continuous values,
gradients, and the literal two Holder graphs, with their inherited norm. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

def F05ActualJetComponent {n : ℕ} {α C : ℝ} {Q : Set (Point n)}
    {v : Point n → ℝ} (hα : 0 < α) (hv : SchauderBound α Q v C) : F05JetComponent α Q :=
  (boundedVectorContinuousOfBound (fun p : Q => v p.val) hv.1.1.domRestrict C
      (fun p => by simpa only [Real.norm_eq_abs] using (hv.2.2.1 p.val p.property).1),
    boundedVectorContinuousOfBound (fun p : Q => spatialD v p.val) hv.1.2.1.domRestrict C
      (fun p => (hv.2.2.1 p.val p.property).2),
    vectorHolderGraphOfBound hα hv.2.2.2.1,
    holderGraphOfBound hα hv.2.2.2.2)

theorem F05ActualJetComponent_norm_le {n : ℕ} {α C : ℝ} {Q : Set (Point n)}
    {v : Point n → ℝ} (hα : 0 < α) (hv : SchauderBound α Q v C) :
    ‖F05ActualJetComponent hα hv‖ ≤ C := by
  change max _ (max _ (max _ _)) ≤ C
  refine max_le ?_ (max_le ?_ (max_le
    (vectorHolderGraphOfBound_norm_le hα hv.2.2.2.1)
    (holderGraphOfBound_norm_le hα hv.2.2.2.2)))
  · apply (BoundedContinuousFunction.norm_le hv.2.1).mpr
    intro p
    change ‖v p.val‖ ≤ C
    exact (by simpa only [Real.norm_eq_abs] using (hv.2.2.1 p.val p.property).1)
  · apply (BoundedContinuousFunction.norm_le hv.2.1).mpr
    intro p
    change ‖spatialD v p.val‖ ≤ C
    exact (hv.2.2.1 p.val p.property).2

theorem F05ActualJetComponent_eval {n : ℕ} {α C : ℝ} {Q : Set (Point n)}
    {v : Point n → ℝ} (hα : 0 < α) (hv : SchauderBound α Q v C) :
    EqOn (F05BCFFun (F05ActualJetComponent hα hv).1) v Q ∧
    EqOn (F05BCFFun (F05ActualJetComponent hα hv).2.1) (spatialD v) Q ∧
    EqOn (F05BCFFun (F05ActualJetComponent hα hv).2.2.1.val.1) (spatialDD v) Q ∧
    EqOn (F05BCFFun (F05ActualJetComponent hα hv).2.2.2.val.1) (timeD Q v) Q := by
  refine ⟨?_,?_,?_,?_⟩
  · intro p hp
    rw [F05BCFFun_apply _ ⟨p,hp⟩]
    rfl
  · intro p hp
    rw [F05BCFFun_apply _ ⟨p,hp⟩]
    rfl
  · exact vectorHolderGraphOfBound_eqOn hα hv.2.2.2.1
  · exact holderGraphOfBound_eqOn hα hv.2.2.2.2

end Yau.Proofs.F05Aux
