import Yau.Proofs.F03BoundaryCompactBound
import Yau.Proofs.F03DirichletCoerciveSource

/-! The actual computed Laplacian and coercive source are bounded up to the boundary. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletClassicalHeat_compact_boundary_laplacian_bound (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (K : Set M.Carrier) (hKc : IsCompact K)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : Lp ℝ 2 (μ.restrict Ω), ∀ t : ℝ, τ ≤ t →
      ∀ x ∈ K, x ∈ Ω →
        |laplacian g.form (fun y => dirichletClassicalHeat g hK μ hμ Ω hΩ f y t) x| ≤ A*‖f‖ := by
  obtain ⟨C,hC,hBound⟩ := dirichletClassicalHeat_compact_boundary_bound g hK μ hμ Ω hΩ K hKc (half_pos hτ)
  obtain ⟨B,hB,hD⟩ := dirichletHeatDerivative_uniform_later_bound g μ hμ Ω (half_pos hτ)
  refine ⟨C*B,mul_pos hC hB,?_⟩
  intro f t ht x hxK hxΩ
  have hσt : τ/2 < t := (half_lt_self hτ).trans_le ht
  have hr : τ/2 ≤ t-τ/2 := by linarith only [ht]
  rw [dirichletClassicalHeat_laplacian_split g hK μ hμ Ω hΩ f x hxΩ (half_pos hτ) hσt]
  exact (hBound (dirichletHeatDerivativeOperator g μ hμ Ω (t-τ/2) f) (τ/2) le_rfl x hxK hxΩ).trans
    ((mul_le_mul_of_nonneg_left (hD (t-τ/2) hr f) hC.le).trans_eq (mul_assoc C B ‖f‖).symm)

theorem dirichletHeatInverse_boundary_abs_bound (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : SmoothPrecompactDomain Ω) {τ : ℝ} (hτ : 0 < τ) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : Lp ℝ 2 (μ.restrict Ω), ∀ t : ℝ, τ ≤ t →
      ∀ᵐ x ∂μ.restrict Ω, |dirichletHeatInverse g μ hμ Ω t f x| ≤ B*‖f‖ := by
  obtain ⟨C,hC,hU⟩ := dirichletClassicalHeat_compact_boundary_bound g hK μ hμ Ω hΩ.1
    (closure Ω) hΩ.2.2.2.1 hτ
  obtain ⟨A,hA,hL⟩ := dirichletClassicalHeat_compact_boundary_laplacian_bound g hK μ hμ Ω hΩ.1
    (closure Ω) hΩ.2.2.2.1 hτ
  refine ⟨C+A,add_pos hC hA,?_⟩
  intro f t ht
  filter_upwards [dirichletHeatInverse_ae_laplacian g hK μ hμ Ω hΩ.1 f (hτ.trans_le ht),
    ae_restrict_mem hΩ.1.measurableSet] with x hx hxΩ
  rw [hx]
  calc
    _ ≤ |dirichletClassicalHeat g hK μ hμ Ω hΩ.1 f x t|+
        |laplacian g.form (fun y => dirichletClassicalHeat g hK μ hμ Ω hΩ.1 f y t) x| := abs_sub _ _
    _ ≤ C*‖f‖+A*‖f‖ := add_le_add (hU f t ht x (subset_closure hxΩ) hxΩ)
      (hL f t ht x (subset_closure hxΩ) hxΩ)
    _ = _ := by ring

end Yau.Proofs.F03Aux
