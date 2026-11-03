import Yau.Proofs.P06BoundedGraphPowers

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- The bounded operator `□ exp(-t□/2)`, obtained from the same actual
resolvent factor as the heat family. -/
def hodgeHeatEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (t : ℝ) :
    L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  hodgeHeatHilbertInverse g μ hμ k t - hodgeHeatHilbert g μ hμ k t

theorem hodgeHeatEnergy_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (f : L2FormHilbert g μ k) :
    (hodgeHeatHilbert g μ hμ k t f, hodgeHeatEnergy g μ hμ k t f) ∈
      (hodgeCoreOperator g μ hμ k).closure.graph := by
  have hg := hodgeResolventOne_graph g μ hμ k (hodgeHeatHilbertInverse g μ hμ k t f)
  have he : hodgeResolventOne g μ hμ k (hodgeHeatHilbertInverse g μ hμ k t f) =
      hodgeHeatHilbert g μ hμ k t f := by
    rw [hodgeHeatHilbert_factor g μ hμ k ht]
    rfl
  rw [he] at hg
  exact hg

theorem hodgeHeatEnergy_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (f : L2FormHilbert g μ k) :
    ‖hodgeHeatEnergy g μ hμ k t f‖ ≤ (2 / t) * ‖f‖ := by
  have hb := Spectral.realHeatEnergy_norm_le (hodgeResolventOne g μ hμ k)
    (hodgeResolventOne_symmetric g μ hμ k) (hodgeResolventOne_positive g μ hμ k)
    (hodgeResolventOne_bound g μ hμ k) (hodgeResolventOne_injective g μ hμ k)
    (by positivity : 0 < t / 2) f
  have he : (t / 2)⁻¹ = 2 / t := by field_simp
  simpa only [hodgeHeatEnergy, sub_apply, hodgeHeatHilbertInverse, hodgeHeatHilbert, he] using hb

theorem hodgeHeatHilbert_commute_energy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Commute (hodgeHeatHilbert g μ hμ k t) (hodgeHeatEnergy g μ hμ k t) :=
  Spectral.realHeat_commute_energy _ _ _ _ _ (by positivity : 0 < t / 2)

/-- The canonical heat flow belongs to every finite original generator
domain, with an explicit norm bound for every member of its graph chain. -/
theorem hodgeHeatHilbert_bounded_graph_chain (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (f : L2FormHilbert g μ k)
    {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ∃ u : ℕ → L2FormHilbert g μ k, u 0 = hodgeHeatHilbert g μ hμ k t f ∧
      (∀ j, j < m → (u j, u (j + 1)) ∈ (hodgeCoreOperator g μ hμ k).closure.graph) ∧
      ∀ j, j ≤ m → ‖u j‖ ≤ (2 * (m : ℝ) / t) ^ j * ‖f‖ := by
  by_cases hm : 0 < m
  · let τ : ℝ := t / m
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hτ : 0 < τ := div_pos ht hmR
    obtain ⟨u, hu, hchain, hbound⟩ := boundedGraph_power_chain (hodgeCompleteOperator g μ hμ k)
      (hodgeHeatHilbert g μ hμ k τ) (hodgeHeatEnergy g μ hμ k τ)
      (hodgeHeatEnergy_graph g μ hμ k hτ) (hodgeHeatHilbert_commute_energy g μ hμ k hτ)
      (2 / τ) (by positivity) (hodgeHeatHilbert_bound g μ hμ k τ)
      (hodgeHeatEnergy_bound g μ hμ k hτ) m f
    refine ⟨u, ?_, hchain, ?_⟩
    · rw [hu]
      have htime : (m : ℝ) * (τ / 2) = t / 2 := by
        dsimp only [τ]
        field_simp
      have hp := Spectral.realHeat_nat_mul (hodgeResolventOne g μ hμ k)
        (hodgeResolventOne_symmetric g μ hμ k) (hodgeResolventOne_positive g μ hμ k)
        (hodgeResolventOne_bound g μ hμ k) (hodgeResolventOne_injective g μ hμ k)
        (by positivity : 0 ≤ τ / 2) m
      rw [htime] at hp
      exact congrArg (fun A : L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k => A f) hp.symm
    · have he : 2 / τ = 2 * (m : ℝ) / t := by
        dsimp only [τ]
        field_simp
      simpa only [he] using hbound
  · refine ⟨fun _ => hodgeHeatHilbert g μ hμ k t f, rfl, ?_, ?_⟩
    · intro j hj
      omega
    · intro j hj
      have hj0 : j = 0 := by omega
      simpa only [hj0, pow_zero, one_mul] using hodgeHeatHilbert_bound g μ hμ k t f

end Yau.NodeProofs.P06Aux
