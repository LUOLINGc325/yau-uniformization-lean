import Yau.Proofs.F03DirichletClassicalHeat

/-! Actual pointwise Markov bounds of the constructed classical heat. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletClassicalHeat_submarkov (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (K : ℝ) (hK0 : 0 ≤ K)
    (f : Lp ℝ 2 (μ.restrict Ω)) (hf : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x ∧ f x ≤ K)
    {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ Ω, 0 ≤ dirichletClassicalHeat g hK μ hμ Ω hΩ f x t ∧
      dirichletClassicalHeat g hK μ hμ Ω hΩ f x t ≤ K := by
  have hu : ∀ x ∈ Ω, dirichletClassicalHeat g hK μ hμ Ω hΩ f x t ≤ K := by
    apply leOn_open_of_riemannian_ae_le g μ hμ Ω hΩ _ (fun _ => K)
      (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ f ht) continuousOn_const
    filter_upwards [dirichletClassicalHeat_ae g hK μ hμ Ω hΩ f ht,
      dirichletHeat_submarkov g μ hμ Ω hΩ.measurableSet ht.le K hK0 f hf] with x hx hb
    simpa only [hx] using hb.2
  intro x hx
  exact ⟨dirichletClassicalHeat_nonneg g hK μ hμ Ω hΩ f (hf.mono (fun _ h => h.1)) ht x hx,hu x hx⟩

theorem dirichletClassicalHeat_abs_bound (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (K : ℝ) (hK0 : 0 < K)
    (f : Lp ℝ 2 (μ.restrict Ω)) (hf : ∀ᵐ x ∂μ.restrict Ω, |f x| ≤ K)
    {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ Ω, |dirichletClassicalHeat g hK μ hμ Ω hΩ f x t| ≤ K := by
  apply leOn_open_of_riemannian_ae_le g μ hμ Ω hΩ _ (fun _ => K)
    (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ f ht).abs continuousOn_const
  filter_upwards [dirichletClassicalHeat_ae g hK μ hμ Ω hΩ f ht,
    dirichletHeat_abs_markov g μ hμ Ω hΩ.measurableSet ht.le K hK0 f hf] with x hx hb
  simpa only [hx] using hb

end Yau.Proofs.F03Aux
