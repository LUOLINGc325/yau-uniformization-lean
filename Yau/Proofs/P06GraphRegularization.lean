import Yau.Proofs.P06HodgeSpectral
import Yau.Proofs.P06SpectralRegularization

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem graph_resolvent_preimage (T : H →ₗ.[ℝ] H)
    (hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : H) (T u)) (R : H →L[ℝ] H)
    (hR : ∀ f, (R f, f - R f) ∈ T.graph)
    {x y : H} (hxy : (x, y) ∈ T.graph) : R (x + y) = x := by
  apply positiveShift_graph_injective T hp zero_lt_one (hR (x + y)) hxy
  simp only [one_smul]
  abel

theorem graph_invariant_of_commute_resolvent (T : H →ₗ.[ℝ] H)
    (hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : H) (T u)) (R : H →L[ℝ] H)
    (hR : ∀ f, (R f, f - R f) ∈ T.graph) (S : H →L[ℝ] H) (hc : Commute S R)
    {x y : H} (hxy : (x, y) ∈ T.graph) : (S x, S y) ∈ T.graph := by
  have hpre := graph_resolvent_preimage T hp R hR hxy
  have hfirst := (congrArg (fun A : H →L[ℝ] H => A (x + y)) hc.eq).symm
  change R (S (x + y)) = S (R (x + y)) at hfirst
  rw [hpre] at hfirst
  have hg := hR (S (x + y))
  rw [hfirst, map_add, add_sub_cancel_left] at hg
  exact hg

/-- A finite chain is proved in the original partial operator graph.
No spectral domain or selected differential operator is assumed. -/
theorem resolventPower_graph_chain (T : H →ₗ.[ℝ] H) (R : H →L[ℝ] H)
    (hR : ∀ f, (R f, f - R f) ∈ T.graph) (m : ℕ) (f : H) :
    ∃ u : ℕ → H, u 0 = (R ^ m) f ∧
      ∀ j, j < m → (u j, u (j + 1)) ∈ T.graph := by
  induction m generalizing f with
  | zero =>
    refine ⟨fun _ => f, ?_, ?_⟩
    · simp
    · intro j hj
      omega
  | succ m ih =>
    obtain ⟨u, hu, hchain⟩ := ih (f - R f)
    let v : ℕ → H
      | 0 => (R ^ (m + 1)) f
      | j + 1 => u j
    refine ⟨v, rfl, ?_⟩
    intro j hj
    cases j with
    | zero =>
      change ((R ^ (m + 1)) f, u 0) ∈ T.graph
      rw [hu]
      have he : (R ^ m) (R f) = R ((R ^ m) f) := by
        exact congrArg (fun A : H →L[ℝ] H => A f) (Commute.pow_self R m).eq
      simpa only [pow_succ', mul_apply_eq_comp, map_sub, he] using hR ((R ^ m) f)
    | succ j =>
      exact hchain j (by omega)

end Hilbert

open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem hodgeHeatHilbert_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (t : ℝ)
    {x y : L2FormHilbert g μ k}
    (hxy : (x, y) ∈ (hodgeCoreOperator g μ hμ k).closure.graph) :
    (hodgeHeatHilbert g μ hμ k t x, hodgeHeatHilbert g μ hμ k t y) ∈
      (hodgeCoreOperator g μ hμ k).closure.graph :=
  graph_invariant_of_commute_resolvent (hodgeCompleteOperator g μ hμ k)
    (hodgeCompleteOperator_nonnegative g μ hμ k) (hodgeResolventOne g μ hμ k)
    (hodgeResolventOne_graph g μ hμ k) (hodgeHeatHilbert g μ hμ k t)
    (Spectral.realHeat_commute_resolvent _ _ _ _ _ (t / 2)) hxy

theorem hodgeHeatHilbert_graph_chain (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (f : L2FormHilbert g μ k)
    {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ∃ u : ℕ → L2FormHilbert g μ k, u 0 = hodgeHeatHilbert g μ hμ k t f ∧
      ∀ j, j < m → (u j, u (j + 1)) ∈ (hodgeCoreOperator g μ hμ k).closure.graph := by
  by_cases hm : 0 < m
  · let R := hodgeResolventOne g μ hμ k
    let B := Spectral.realHeatInverse R (hodgeResolventOne_symmetric g μ hμ k)
      (hodgeResolventOne_positive g μ hμ k) (hodgeResolventOne_bound g μ hμ k)
      (hodgeResolventOne_injective g μ hμ k) ((t / 2) / m)
    obtain ⟨u, hu, hchain⟩ := resolventPower_graph_chain (hodgeCompleteOperator g μ hμ k)
      R (hodgeResolventOne_graph g μ hμ k) m ((B ^ m) f)
    refine ⟨u, ?_, hchain⟩
    rw [hu]
    have hf := Spectral.realHeat_factor_power R (hodgeResolventOne_symmetric g μ hμ k)
      (hodgeResolventOne_positive g μ hμ k) (hodgeResolventOne_bound g μ hμ k)
      (hodgeResolventOne_injective g μ hμ k) (by positivity : 0 < t / 2) m hm
    exact (congrArg (fun A : L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k => A f) hf).symm
  · refine ⟨fun _ => hodgeHeatHilbert g μ hμ k t f, rfl, ?_⟩
    intro j hj
    omega

end Yau.NodeProofs.P06Aux
