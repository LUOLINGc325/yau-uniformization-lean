import Yau.Proofs.P06ExteriorHeatResolvent

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.ExteriorHeat
open Yau Yau.LeafProofs.L03 Yau.LeafProofs.L19Aux
variable {n k : ℕ} {M : ComplexManifold n}

/-- The original heat at the unchanged t/2 Euler clock preserves the actual d graph. -/
theorem exteriorGraph_heat (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {f : L2FormHilbert g μ k}
    {df : L2FormHilbert g μ (k+1)} (hdf : (f,df) ∈ (closedExterior g μ hμ k).graph)
    (t : ℝ) (ht : 0 ≤ t) :
    (hodgeHeatHilbert g μ hμ k t f, hodgeHeatHilbert g μ hμ (k+1) t df) ∈
      (closedExterior g μ hμ k).graph := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [hodgeHeatHilbert_zero, one_apply_eq_self] using hdf
  apply (closedExterior_isClosed g μ hμ k).mem_of_tendsto
    ((hodgeHeatEuler_apply_tendsto g μ hμ k t ht f).prodMk_nhds
      (hodgeHeatEuler_apply_tendsto g μ hμ (k+1) t ht df))
  apply Eventually.of_forall
  intro j
  let s := (t/2) / scalarEulerCount j
  have hs : 0 < s := div_pos (half_pos ht) (scalarEulerCount_cast_pos j)
  have hp (m : ℕ) :
      ((hodgeImplicitResolvent g μ hμ k s hs ^ m) f,
        (hodgeImplicitResolvent g μ hμ (k+1) s hs ^ m) df) ∈
          (closedExterior g μ hμ k).graph := by
    induction m with
    | zero => simpa only [pow_zero, one_apply_eq_self] using hdf
    | succ m hm =>
      simpa only [pow_succ', mul_apply_eq_comp] using exteriorGraph_resolvent g μ hμ hm s hs
  exact hp (scalarEulerCount j)

theorem exteriorGraph_heat_core_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (B : RealForm M (k+1)) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (t : ℝ) (ht : 0 ≤ t) :
    inner ℝ (hodgeHeatHilbert g μ hμ k t
      (realizeActualForm g μ A (smooth_compactlySupported_l2RealForm g μ hμ A hA hcA)))
      (realizeActualForm g μ (codifferentialRealForm g.form B) (codifferentialRealForm_l2 g μ hμ B hB hcB)) =
    inner ℝ (hodgeHeatHilbert g μ hμ (k+1) t
      (realizeActualForm g μ (exteriorRealForm A) (exteriorRealForm_l2 g μ hμ A hA hcA)))
      (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)) :=
  (exteriorGraph_pairing g μ hμ
    (exteriorGraph_heat g μ hμ (exteriorGraph_core g μ hμ A hA hcA) t ht) B hB hcB).symm

end Yau.NodeProofs.P06Aux.ExteriorHeat
