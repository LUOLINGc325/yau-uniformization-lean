import Yau.Proofs.F01PointwiseChartGlue

/-! Genuine all-order chart bounds construct a single global value
function and a single subsequence. Its actual chart derivatives are the
uniform limits, including any closed time faces in the chart domains. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace Yau.NodeProofs.F01Aux
variable {A E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem global_chart_smooth_limit
    (T : Set A) (S : ℕ → Set E) (e : ℕ → E → A)
    (hinto : ∀ j x, x ∈ S j → e j x ∈ T)
    (hcover : ∀ y ∈ T, ∃ j x, x ∈ S j ∧ e j x = y)
    (hS : ∀ j, Convex ℝ (S j)) (hcompact : ∀ j, IsCompact (S j))
    (hUnique : ∀ j, UniqueDiffOn ℝ (S j))
    (f : ℕ → A → F) (hf : ∀ m j, ContDiffOn ℝ ∞ (fun x => f m (e j x)) (S j))
    (C : ℕ → ℕ → ℝ≥0)
    (hbound : ∀ j k m x, x ∈ S j →
      ‖iteratedFDerivWithin ℝ k (fun y => f m (e j y)) (S j) x‖ ≤ C j k) :
    ∃ g : A → F, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ y ∈ T, Tendsto (fun m => f (σ m) y) atTop (𝓝 (g y))) ∧
      (∀ j, ContDiffOn ℝ ∞ (fun x => g (e j x)) (S j)) ∧
      ∀ j k : ℕ, TendstoUniformlyOn
        (fun m x => iteratedFDerivWithin ℝ k (fun y => f (σ m) (e j y)) (S j) x)
        (iteratedFDerivWithin ℝ k (fun y => g (e j y)) (S j)) atTop (S j) := by
  obtain ⟨v, σ, hσ, hv, hconv⟩ := countable_smooth_subsequence S hS hcompact hUnique
    (fun m j x => f m (e j x)) hf C hbound
  have hvalues (j : ℕ) : TendstoUniformlyOn (fun m x => f (σ m) (e j x)) (v j) atTop (S j) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hconv j 0)) ε hε] with m hm
    intro x hx
    simpa only [dist_iteratedFDerivWithin_zero] using hm x hx
  obtain ⟨g, hpoint, hglue⟩ := pointwise_chart_limit_glue T
    (fun j (x : S j) => e j x) (fun j x => hinto j x x.property)
    (fun y hy => by
      obtain ⟨j, x, hx, hxy⟩ := hcover y hy
      exact ⟨j, ⟨x, hx⟩, hxy⟩)
    (fun m y => f (σ m) y) (fun j (x : S j) => v j x)
    (fun j x => (hvalues j).tendsto_at x.property)
  have hEq (j : ℕ) : EqOn (fun x => g (e j x)) (v j) (S j) := by
    intro x hx
    exact hglue j ⟨x, hx⟩
  refine ⟨g, σ, hσ, hpoint, (fun j => (hv j).congr (hEq j)), ?_⟩
  intro j k
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hconv j k)) ε hε] with m hm
  intro x hx
  rw [iteratedFDerivWithin_congr (hEq j) hx k]
  exact hm x hx

end Yau.NodeProofs.F01Aux
