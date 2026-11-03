import Yau.Proofs.P06TraceHilbertCore
import Yau.Proofs.P06HodgeEuler

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.TraceHilbert
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem resolvent (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (s : ℝ) (hs : 0 < s) (f : L2FormHilbert g μ 2) :
    contraction g μ (hodgeImplicitResolvent g μ hμ 2 s hs f) =
      hodgeImplicitResolvent g μ hμ 0 s hs (contraction g μ f) := by
  have h2 := closed_graph g μ hμ hk (hodgeImplicitResolvent_graph g μ hμ 2 s hs f)
  have h0 := hodgeImplicitResolvent_graph g μ hμ 0 s hs (contraction g μ f)
  apply positiveShift_graph_injective (hodgeCompleteOperator g μ hμ 0)
    (hodgeCompleteOperator_nonnegative g μ hμ 0) (inv_pos.mpr hs) h2 h0
  simp only [map_smul, map_sub, smul_sub, sub_add_cancel]

theorem resolventOne (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (f : L2FormHilbert g μ 2) :
    contraction g μ (hodgeResolventOne g μ hμ 2 f) =
      hodgeResolventOne g μ hμ 0 (contraction g μ f) := by
  have h2 := closed_graph g μ hμ hk (hodgeResolventOne_graph g μ hμ 2 f)
  have h0 := hodgeResolventOne_graph g μ hμ 0 (contraction g μ f)
  apply positiveShift_graph_injective (hodgeCompleteOperator g μ hμ 0)
    (hodgeCompleteOperator_nonnegative g μ hμ 0) zero_lt_one h2 h0
  simp only [map_sub, one_smul, sub_add_cancel]

theorem resolvent_pow (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (s : ℝ) (hs : 0 < s) (f : L2FormHilbert g μ 2) (m : ℕ) :
    contraction g μ ((hodgeImplicitResolvent g μ hμ 2 s hs ^ m) f) =
      (hodgeImplicitResolvent g μ hμ 0 s hs ^ m) (contraction g μ f) := by
  induction m with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ m hm =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, resolvent g μ hμ hk, hm]

theorem heat (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (t : ℝ) (ht : 0 ≤ t) (f : L2FormHilbert g μ 2) :
    contraction g μ (hodgeHeatHilbert g μ hμ 2 t f) =
      hodgeHeatHilbert g μ hμ 0 t (contraction g μ f) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [hodgeHeatHilbert_zero, one_apply_eq_self]
  have h2 := (contraction g μ).continuous.continuousAt.tendsto.comp
    (hodgeHeatEuler_apply_tendsto g μ hμ 2 t ht f)
  have h0 := hodgeHeatEuler_apply_tendsto g μ hμ 0 t ht (contraction g μ f)
  have he (j : ℕ) : contraction g μ (hodgeHeatEuler g μ hμ 2 t ht j f) =
      hodgeHeatEuler g μ hμ 0 t ht j (contraction g μ f) :=
    resolvent_pow g μ hμ hk _ _ f _
  exact tendsto_nhds_unique (h2.congr he) h0

end Yau.NodeProofs.P06Aux.TraceHilbert
