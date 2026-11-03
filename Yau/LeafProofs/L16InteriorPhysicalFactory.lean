import Yau.LeafProofs.L16PhysicalPatchFactory
import Yau.LeafProofs.L16InteriorLinearFactory

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

local instance interiorPhysicalFactory_group {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedAddCommGroup (compatibleHolderGraph α O T) := inferInstance
local instance interiorPhysicalFactory_space {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedSpace ℝ (compatibleHolderGraph α O T) := inferInstance

/-- The actual interior source-linear solver and its actual cutoff error
realize the same physical factory property as the curved boundary patches. -/
theorem interior_physical_patch_factory {n : ℕ} {O : Set (Space n)}
    {α M lam upper P : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (z : Space n) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hInside : Metric.closedBall z (4*r) ⊆ O)
    (ψ : Space n → ℝ)
    (hψ : HolderBound α (cylinder univ 0 1) (fun p => ψ p.1) P)
    (hPlateau : ∀ x, outerPatchBump r hr z x*ψ x = ψ x) :
    ∃ δ C E : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < E ∧
      PhysicalDirichletPatchFactory O α lam upper M ψ δ C E := by
  obtain ⟨δ,C,hδ,hδ1,hC,hFactory⟩ := interiorDirichlet_linear_factory_uniform_short
    hα hα1 hM hP z hr hr1 hInside ψ hψ hPlateau
  obtain ⟨CG,hCG,hComm⟩ := outerPatchBump_commutator_holder_budget hα hα1 hr hr1 z
  let E : ℝ := 1+CG*M*C
  have hE : 0 < E := by dsimp only [E]; positivity
  refine ⟨δ,C,E,hδ,hδ1,hC,hE,?_⟩
  intro ρ T a b hρ hρ1 hT hTδ hTρ hEll ha hb
  obtain ⟨V,hVAdd,hVSmul,hV⟩ := hFactory ρ T a b hρ hρ1 hT hTδ hTρ hEll ha hb
  let W := fun f => interiorDirichletPatch z r hr (V f)
  let H := fun f => spatialCutoffCommutator a b (outerPatchBump r hr z) (V f)
  refine ⟨W,H,?_,?_,?_⟩
  · intro f g p hp
    change outerPatchBump r hr z p.1*V (f+g) p = _
    rw [hVAdd f g p hp]
    dsimp only [W,interiorDirichletPatch]
    ring
  · intro d f p hp
    change outerPatchBump r hr z p.1*V (d • f) p = _
    rw [hVSmul d f p hp]
    dsimp only [W,interiorDirichletPatch]
    ring
  · intro f
    obtain ⟨hv,hvLow,hv0,hw,hwLow,hw0,hwB,hwEq⟩ := hV f
    refine ⟨⟨hw,hwLow,hw0,hwB,hwEq⟩,?_,?_⟩
    · have h := hComm O T M (C*‖f‖*ρ^(1-α)) a b (V f) ha hb hvLow
      apply holderBound_mono_const h
      have hCost : CG*M*(C*‖f‖*ρ^(1-α)) = (CG*M*C)*(‖f‖*ρ^(1-α)) := by ring
      rw [hCost]
      change (CG*M*C)*(‖f‖*ρ^(1-α)) ≤ (1+CG*M*C)*‖f‖*ρ^(1-α)
      nlinarith only [mul_nonneg (norm_nonneg f) (Real.rpow_nonneg hρ.le (1-α))]
    · intro x hx
      exact spatialCutoffCommutator_initial_zero a b (outerPatchBump r hr z) hv0 x

end Yau.LeafProofs.L16Aux
