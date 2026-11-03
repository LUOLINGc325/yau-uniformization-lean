import Yau.Proofs.F03DirichletEnergy

/-! Genuine inclusion between the literal supported closed energy subspaces. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem dirichletEnergySubmodule_mono (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {Ω Γ : Set M.Carrier} (hΩΓ : Ω ⊆ Γ) :
    dirichletEnergySubmodule g μ hμ Ω ≤ dirichletEnergySubmodule g μ hμ Γ := by
  change closure ((dirichletCore g μ hμ Ω).map
    (UniformSpace.Completion.toComplL : ScalarEnergyDomain g μ hμ →L[ℝ]
      ScalarEnergySpace g μ hμ).toLinearMap : Set (ScalarEnergySpace g μ hμ)) ⊆
    closure ((dirichletCore g μ hμ Γ).map
      (UniformSpace.Completion.toComplL : ScalarEnergyDomain g μ hμ →L[ℝ]
        ScalarEnergySpace g μ hμ).toLinearMap : Set (ScalarEnergySpace g μ hμ))
  apply closure_mono
  rintro x ⟨f,hf,rfl⟩
  exact ⟨f,hf.trans hΩΓ,rfl⟩

def dirichletInclusion (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {Ω Γ : Set M.Carrier} (hΩΓ : Ω ⊆ Γ) :
    DirichletEnergy g μ hμ Ω →L[ℝ] DirichletEnergy g μ hμ Γ :=
  (Submodule.inclusion (dirichletEnergySubmodule_mono g μ hμ hΩΓ)).mkContinuous 1 (fun v => by
    change ‖v‖ ≤ 1*‖v‖
    rw [one_mul])

theorem dirichletInclusion_val (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {Ω Γ : Set M.Carrier} (hΩΓ : Ω ⊆ Γ) (u : DirichletEnergy g μ hμ Ω) :
    (dirichletInclusion g μ hμ hΩΓ u).val=u.val := rfl

theorem dirichletInclusion_norm (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {Ω Γ : Set M.Carrier} (hΩΓ : Ω ⊆ Γ) (u : DirichletEnergy g μ hμ Ω) :
    ‖dirichletInclusion g μ hμ hΩΓ u‖=‖u‖ := rfl

end Yau.Proofs.F03Aux
