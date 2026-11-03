import Yau.Proofs.P06SpectralEuler
import Yau.Proofs.P06HodgeSpectral

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03 Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

def hodgeImplicitResolvent (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (s : ℝ) (hs : 0 < s) :
    L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  normalizedResolvent (hodgeCompleteOperator g μ hμ k) (hodgeCompleteOperator_dense g μ hμ k)
    (hodgeCompleteOperator_selfAdjoint g μ hμ k) (hodgeCompleteOperator_nonnegative g μ hμ k) s hs

theorem hodgeImplicitResolvent_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (s : ℝ) (hs : 0 < s)
    (f : L2FormHilbert g μ k) :
    (hodgeImplicitResolvent g μ hμ k s hs f,
      s⁻¹ • (f - hodgeImplicitResolvent g μ hμ k s hs f)) ∈
        (hodgeCoreOperator g μ hμ k).closure.graph :=
  normalizedResolvent_graph _ _ _ _ s hs f

theorem hodgeImplicitResolvent_cfc (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (s : ℝ) (hs : 0 < s) :
    ComplexHilbert.complexify (hodgeImplicitResolvent g μ hμ k s hs) =
      cfc (scalarEulerMultiplier s) (ComplexHilbert.complexify (hodgeResolventOne g μ hμ k)) :=
  normalizedResolvent_complexify_eq_cfc _ _ _ _ _ (hodgeResolventOne_symmetric g μ hμ k)
    (hodgeResolventOne_positive g μ hμ k) (hodgeResolventOne_bound g μ hμ k)
    (hodgeResolventOne_injective g μ hμ k) rfl s hs

def hodgeHeatEuler (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (t : ℝ) (ht : 0 < t) (j : ℕ) :
    L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  normalizedResolventEuler (hodgeCompleteOperator g μ hμ k) (hodgeCompleteOperator_dense g μ hμ k)
    (hodgeCompleteOperator_selfAdjoint g μ hμ k) (hodgeCompleteOperator_nonnegative g μ hμ k)
    (t / 2) (half_pos ht) j

/-- Actual original resolvent Euler powers converge to the same paper-time
Hodge heat in operator norm, in every degree. -/
theorem hodgeHeatEuler_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (t : ℝ) (ht : 0 < t) :
    Tendsto (hodgeHeatEuler g μ hμ k t ht) atTop (𝓝 (hodgeHeatHilbert g μ hμ k t)) :=
  normalizedResolventEuler_tendsto _ _ _ _ _ (hodgeResolventOne_symmetric g μ hμ k)
    (hodgeResolventOne_positive g μ hμ k) (hodgeResolventOne_bound g μ hμ k)
    (hodgeResolventOne_injective g μ hμ k) rfl (t / 2) (half_pos ht)

theorem hodgeHeatEuler_apply_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (t : ℝ) (ht : 0 < t)
    (f : L2FormHilbert g μ k) :
    Tendsto (fun j => hodgeHeatEuler g μ hμ k t ht j f) atTop
      (𝓝 (hodgeHeatHilbert g μ hμ k t f)) :=
  (ContinuousLinearMap.apply ℝ (L2FormHilbert g μ k) f).continuous.continuousAt.tendsto.comp
    (hodgeHeatEuler_tendsto g μ hμ k t ht)

theorem hodgeHeat_mem_of_resolvent_invariant (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (K : Set (L2FormHilbert g μ k))
    (hclosed : IsClosed K)
    (hK : ∀ s (hs : 0 < s) f, f ∈ K → hodgeImplicitResolvent g μ hμ k s hs f ∈ K)
    (f : L2FormHilbert g μ k) (hf : f ∈ K) (t : ℝ) (ht : 0 ≤ t) :
    hodgeHeatHilbert g μ hμ k t f ∈ K := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [hodgeHeatHilbert_zero, one_apply_eq_self] using hf
  apply hclosed.mem_of_tendsto (hodgeHeatEuler_apply_tendsto g μ hμ k t ht f)
  apply Eventually.of_forall
  intro j
  let s := (t / 2) / scalarEulerCount j
  have hs : 0 < s := div_pos (half_pos ht) (scalarEulerCount_cast_pos j)
  have hpow (m : ℕ) : (hodgeImplicitResolvent g μ hμ k s hs ^ m) f ∈ K := by
    induction m with
    | zero => simpa only [pow_zero, one_apply_eq_self] using hf
    | succ m hm =>
        rw [pow_succ', mul_apply_eq_comp]
        exact hK s hs _ hm
  exact hpow (scalarEulerCount j)

end Yau.NodeProofs.P06Aux
