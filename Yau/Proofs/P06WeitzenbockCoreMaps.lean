import Yau.Proofs.P06WeitzenbockProjectionEnergy
import Yau.Proofs.P06WeitzenbockTraceHodge

noncomputable section
open MeasureTheory
open scoped Manifold Topology ContDiff ComplexOrder
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem omegaForm_normSq (h : HermitianField M) (x : M.Carrier) :
    formNormSq h (omegaForm h) x = (n : ℝ) := by
  change formInner h (omegaForm h) (omegaForm h) x = _
  rw [← formTrace_eq_inner_omega h (omegaForm h) (omegaForm_oneOne h) x]
  unfold formTrace traceWith
  rw [formHermitianMatrix_of_representsIota (gMat h) (omegaForm h) (omegaForm_represents h)]
  have hu := (L12Aux.hMat_posDef h x (chartPt x x) (mem_extChartAt_target x)).isUnit.map
    Matrix.detMonoidHom
  change IsUnit (gMat h x).det at hu
  rw [Matrix.nonsing_inv_mul _ hu]
  simp

theorem scalarTrace_compact (h : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (hcA : CompactlySupportedRealForm A) :
    CompactlySupportedRealForm (scalarForm (formTrace h A)) := by
  apply hcA.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx hz
  apply hx
  apply ContinuousAlternatingMap.ext
  intro V
  change formTrace h A x = 0
  rw [formTrace_eq_inner_omega h A h11]
  exact L03.formInner_eq_zero_of_left_eq_zero h A (omegaForm h) x hz

/-- The type projection intertwines the original frozen compact smooth
Hodge core graph. -/
theorem hodgeCorePair_projection (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) {A W : RealForm M 2}
    (hAW : OperatorCandidates.HodgeCorePair g.form μ A W) :
    OperatorCandidates.HodgeCorePair g.form μ (oneOneProjection A) (oneOneProjection W) := by
  obtain ⟨hA, hcA, hW⟩ := (L03.hodgeCorePair_iff_computed g μ hμ A W).mp hAW
  apply (L03.hodgeCorePair_iff_computed g μ hμ _ _).mpr
  refine ⟨oneOneProjection_smooth A hA, oneOneProjection_compact A hcA, ?_⟩
  rw [hW, hodge_oneOneProjection g μ hμ hk A hA]

/-- Contraction with the Kähler metric intertwines the actual degree-two
and degree-zero core graphs. No closedness hypothesis occurs. -/
theorem hodgeCorePair_trace (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) {A W : RealForm M 2}
    (hAW : OperatorCandidates.HodgeCorePair g.form μ A W) (h11 : RealOneOne A) :
    OperatorCandidates.HodgeCorePair g.form μ
      (scalarForm (formTrace g.form A)) (scalarForm (formTrace g.form W)) := by
  obtain ⟨hA, hcA, hW⟩ := (L03.hodgeCorePair_iff_computed g μ hμ A W).mp hAW
  apply (L03.hodgeCorePair_iff_computed g μ hμ _ _).mpr
  refine ⟨scalarForm_smooth _ (trace_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g)
    A hA h11), scalarTrace_compact g.form A h11 hcA, ?_⟩
  rw [hW]
  exact trace_hodge g μ hμ hk A hA h11

end Yau.NodeProofs.P06Weitzenbock
