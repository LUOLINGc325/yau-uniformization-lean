import Yau.Proofs.P06DDbarHeatResolvent

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.DDbarHeat
open Yau Yau.LeafProofs.L03 Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The original heat at the unchanged t/2 Euler clock preserves the actual dd graph. -/
theorem ddGraph_heat (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g) {f : L2FormHilbert g μ 0}
    {df : L2FormHilbert g μ 2} (hdf : (f,df) ∈ (closedDDbar g μ hμ).graph)
    (t : ℝ) (ht : 0 ≤ t) :
    (hodgeHeatHilbert g μ hμ 0 t f, hodgeHeatHilbert g μ hμ 2 t df) ∈
      (closedDDbar g μ hμ).graph := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [hodgeHeatHilbert_zero, one_apply_eq_self] using hdf
  apply (closedDDbar_isClosed g μ hμ).mem_of_tendsto
    ((hodgeHeatEuler_apply_tendsto g μ hμ 0 t ht f).prodMk_nhds
      (hodgeHeatEuler_apply_tendsto g μ hμ 2 t ht df))
  apply Eventually.of_forall
  intro j
  let s := (t/2) / scalarEulerCount j
  have hs : 0 < s := div_pos (half_pos ht) (scalarEulerCount_cast_pos j)
  have hp (m : ℕ) :
      ((hodgeImplicitResolvent g μ hμ 0 s hs ^ m) f,
        (hodgeImplicitResolvent g μ hμ 2 s hs ^ m) df) ∈
          (closedDDbar g μ hμ).graph := by
    induction m with
    | zero => simpa only [pow_zero, one_apply_eq_self] using hdf
    | succ m hm =>
      simpa only [pow_succ', mul_apply_eq_comp] using ddGraph_resolvent g μ hμ hk hm s hs
  exact hp (scalarEulerCount j)

theorem ddAdjointGraph_iff (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (b : L2FormHilbert g μ 2) (q : L2FormHilbert g μ 0) :
    (b,q) ∈ (closedDDbar g μ hμ).adjoint.graph ↔
      ∀ a da, (a,da) ∈ (closedDDbar g μ hμ).graph → inner ℝ da b = inner ℝ a q := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (closedDDbar_dense g μ hμ),
    Submodule.mem_adjoint_iff]
  simp only [sub_eq_zero]

theorem ddAdjointGraph_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (B : RealForm M 2)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB),
      realizeActualForm g μ (adjointForm g.form B) (adjointForm_l2 g μ hμ B hB hcB)) ∈
        (closedDDbar g μ hμ).adjoint.graph := by
  apply (ddAdjointGraph_iff g μ hμ _ _).mpr
  intro a da ha
  exact ddGraph_pairing g μ hμ ha B hB hcB

/-- Heat transport of the genuine Hilbert adjoint of the actual closed dd graph. -/
theorem ddAdjointGraph_heat (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    {b : L2FormHilbert g μ 2} {q : L2FormHilbert g μ 0}
    (hbq : (b,q) ∈ (closedDDbar g μ hμ).adjoint.graph) (t : ℝ) (ht : 0 ≤ t) :
    (hodgeHeatHilbert g μ hμ 2 t b, hodgeHeatHilbert g μ hμ 0 t q) ∈
      (closedDDbar g μ hμ).adjoint.graph := by
  apply (ddAdjointGraph_iff g μ hμ _ _).mpr
  intro a da ha
  calc
    inner ℝ da (hodgeHeatHilbert g μ hμ 2 t b) =
        inner ℝ (hodgeHeatHilbert g μ hμ 2 t da) b :=
      (hodgeHeatHilbert_symmetric g μ hμ 2 t da b).symm
    _ = inner ℝ (hodgeHeatHilbert g μ hμ 0 t a) q :=
      (ddAdjointGraph_iff g μ hμ b q).mp hbq _ _ (ddGraph_heat g μ hμ hk ha t ht)
    _ = inner ℝ a (hodgeHeatHilbert g μ hμ 0 t q) :=
      hodgeHeatHilbert_symmetric g μ hμ 0 t a q

end Yau.NodeProofs.P06Aux.DDbarHeat
