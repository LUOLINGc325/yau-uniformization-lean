import Yau.Proofs.F03DirichletRieszField
import Yau.Proofs.F03DirichletClassicalSemigroup

/-! Compact source bounds at every later time, chosen before all sources. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletClassicalHeat_compact_fixed_time_bound (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (K : Set M.Carrier) (hKc : IsCompact K) (hKΩ : K ⊆ Ω)
    {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Lp ℝ 2 (μ.restrict Ω), ∀ x ∈ K,
      |dirichletClassicalHeat g hK μ hμ Ω hΩ f x t| ≤ C*‖f‖ := by
  obtain ⟨C,hC⟩ := hKc.bddAbove_image
    (((dirichletRieszVectorAt_continuousOn g hK μ hμ Ω hΩ t ht).norm).mono hKΩ)
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro f x hx
  rw [← dirichletRieszVectorAt_inner g hK μ hμ Ω hΩ t ht x (hKΩ hx) f]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right ((hC ⟨x,hx,rfl⟩).trans (le_max_right _ _)) (norm_nonneg f))

/-- The same compact constant works for every later time by the actual
semigroup identity and its proved L2 contraction. -/
theorem dirichletClassicalHeat_compact_later_bound (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (K : Set M.Carrier) (hKc : IsCompact K) (hKΩ : K ⊆ Ω)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Lp ℝ 2 (μ.restrict Ω), ∀ t : ℝ, τ ≤ t → ∀ x ∈ K,
      |dirichletClassicalHeat g hK μ hμ Ω hΩ f x t| ≤ C*‖f‖ := by
  obtain ⟨C,hC,hBound⟩ := dirichletClassicalHeat_compact_fixed_time_bound g hK μ hμ Ω hΩ K hKc hKΩ
    (half_pos hτ)
  refine ⟨C,hC,?_⟩
  intro f t ht x hx
  have hs : 0 ≤ t-τ/2 := by linarith only [hτ,ht]
  have hsem := dirichletClassicalHeat_semigroup g hK μ hμ Ω hΩ f (half_pos hτ) hs x (hKΩ hx)
  have htime : τ/2+(t-τ/2)=t := by ring
  have hsem' : dirichletClassicalHeat g hK μ hμ Ω hΩ f x t =
      dirichletClassicalHeat g hK μ hμ Ω hΩ (dirichletHeat g μ hμ Ω (t-τ/2) f) x (τ/2) := by
    simpa only [htime] using hsem
  rw [hsem']
  exact (hBound (dirichletHeat g μ hμ Ω (t-τ/2) f) x hx).trans
    (mul_le_mul_of_nonneg_left (dirichletHeat_norm_le g μ hμ Ω (t-τ/2) f) hC.le)

end Yau.Proofs.F03Aux
