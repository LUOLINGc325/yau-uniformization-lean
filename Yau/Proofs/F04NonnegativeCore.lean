import Yau.Proofs.F04SmoothCompositionContinuity
import Yau.Proofs.F04PositiveDifferential

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletPosPart_eq_self_of_nonneg (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (u : DirichletEnergy g μ hμ O)
    (hu : ∀ᵐ x ∂μ.restrict O, 0 ≤ dirichletL2 g μ hμ O u x) :
    dirichletPosPart g μ hμ O hO u = u := by
  apply dirichletL2_injective g hK μ hμ O hO
  rw [(dirichletPosPart_spec g μ hμ O hO u).1]
  apply Lp.ext
  filter_upwards [Lp.coeFn_posPart (dirichletL2 g μ hμ O u), hu] with x hx hp
  exact hx.trans (max_eq_left hp)

/-- Nonnegative elements have genuine nonnegative compact smooth approximants
in the original supported energy norm. -/
theorem exists_nonnegative_dirichletCore_tendsto
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (u : DirichletEnergy g μ hμ O)
    (hu : ∀ᵐ x ∂μ.restrict O, 0 ≤ dirichletL2 g μ hμ O u x) :
    ∃ f : ℕ → dirichletCore g μ hμ O,
      (∀ j x, 0 ≤ (f j).val x) ∧
      Tendsto (fun j => dirichletCoreToEnergy g μ hμ O (f j)) atTop (𝓝 u) := by
  obtain ⟨fs, hfs⟩ := exists_dirichletCore_tendsto g μ hμ O u
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp only [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let v : ℕ → DirichletEnergy g μ hμ O := fun j => dirichletPositiveSmoothing g μ hμ O (δ j) u
  have hv : Tendsto v atTop (𝓝 u) := by
    rw [← dirichletPosPart_eq_self_of_nonneg g hK μ hμ O hO u hu]
    exact dirichletPositiveSmoothing_tendsto g hK μ hμ O hO u δ hδ hδlim
  let q : ℕ → ℕ → dirichletCore g μ hμ O := fun j k =>
    smoothCompositionCore g μ hμ O (smoothPositive (δ j)) (smoothPositive_contDiff (δ j))
      (smoothPositive_zero (δ j)) (fs k)
  have hq (j : ℕ) : Tendsto (fun k => dirichletCoreToEnergy g μ hμ O (q j k)) atTop (𝓝 (v j)) := by
    have hc := (continuous_dirichletSmoothComp g μ hμ O (smoothPositive (δ j))
      (smoothPositive_contDiff (δ j)) (smoothPositive_zero (δ j))
      1 zero_le_one (smoothPositive_deriv_abs_le (δ j))).tendsto u |>.comp hfs
    simpa only [Function.comp_def, dirichletSmoothComp_core g hK μ hμ O hO, q, v,
      dirichletPositiveSmoothing] using hc
  have hm (j : ℕ) : ∃ k : ℕ,
      dist (dirichletCoreToEnergy g μ hμ O (q j k)) (v j) < δ j := by
    have he := (hq j).eventually (Metric.ball_mem_nhds (v j) (hδ j))
    obtain ⟨k, hk⟩ := he.exists
    exact ⟨k, hk⟩
  choose m hm using hm
  refine ⟨fun j => q j (m j), ?_, ?_⟩
  · intro j x
    exact (smoothPositive_bounds (hδ j) ((fs (m j)).val x)).1
  · apply tendsto_iff_dist_tendsto_zero.mpr
    have hvd := tendsto_iff_dist_tendsto_zero.mp hv
    apply squeeze_zero (fun _ => dist_nonneg) (fun j =>
      (dist_triangle _ (v j) u).trans (add_le_add (hm j).le le_rfl))
    simpa only [zero_add] using hδlim.add hvd

end Yau.F04Proof
