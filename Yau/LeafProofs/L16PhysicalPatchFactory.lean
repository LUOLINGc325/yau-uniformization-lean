import Yau.LeafProofs.L16CurvedBoundaryLinearFactory
import Yau.LeafProofs.L16CurvedPatchCommutator
import Yau.LeafProofs.L16CurvedPatchCover

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

local instance physicalPatchFactory_group {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedAddCommGroup (compatibleHolderGraph α O T) := inferInstance
local instance physicalPatchFactory_space {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedSpace ℝ (compatibleHolderGraph α O T) := inferInstance

/-- Concrete actual physical patch functions, with genuine source linearity,
zero data, the original closed-domain equation and its small cutoff error.
The interpolation scale and all PDE data are quantified after the constants. -/
def PhysicalDirichletPatchFactory {n : ℕ} (O : Set (Space n))
    (α lam upper M : ℝ) (ψ : Space n → ℝ) (δ C E : ℝ) : Prop :=
  ∀ (ρ T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
    0 < ρ → ρ ≤ 1 → 0 < T → T ≤ δ → T ≤ ρ^2 →
    Elliptic (cylinder (closure O) 0 T) a lam upper →
    HolderBound α (cylinder (closure O) 0 T) a M →
    (∀ i, HolderBound α (cylinder (closure O) 0 T) (fun p => b p i) M) →
    ∃ W H : compatibleHolderGraph α O T → Point n → ℝ,
      (∀ f g p, p ∈ cylinder univ 0 T → W (f+g) p = W f p+W g p) ∧
      (∀ (c : ℝ) f p, p ∈ cylinder univ 0 T → W (c • f) p = c*W f p) ∧
      ∀ f,
        (SchauderBound α (cylinder univ 0 T) (W f) (C*‖f‖) ∧
        HolderBound α (cylinder univ 0 T) (fun p => (W f p,spatialD (W f) p)) (C*‖f‖*ρ^(1-α)) ∧
        (∀ x, W f (x,0) = 0) ∧
        (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, W f (x,t) = 0) ∧
        ∀ p ∈ cylinder (closure O) 0 T,
          linearOp (cylinder (closure O) 0 T) a b (W f) p = ψ p.1*compatibleHolderFun f p-H f p) ∧
        (HolderBound α (cylinder (closure O) 0 T) (H f) (E*‖f‖*ρ^(1-α)) ∧
          ∀ x ∈ frontier O, H f (x,0) = 0)

/-- The actual boundary linear factory and the actual chart-commutator
estimate realize the physical patch property, with no operator hypotheses. -/
theorem boundary_physical_patch_factory {n : ℕ} {O : Set (Space n)}
    {α M lam upper P : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) (hP : 0 ≤ P)
    (z : Space n) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (e : Space n) (he : ‖e‖ = 1) (c : OpenPartialHomeomorph (Space n) (Space n))
    {q : ℝ} (hq : 0 < q) (hSource : Metric.closedBall z (4*r) ⊆ c.source)
    (hImage : MapsTo c (Metric.closedBall z (4*r)) (Metric.ball 0 (q/2)))
    (hTarget : Metric.closedBall (0 : Space n) (4*q) ⊆ c.target)
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    (hFaces : ∀ x ∈ c.source, (x ∈ closure O ↔ 0 ≤ inner ℝ e (c x)) ∧
      (x ∈ frontier O ↔ inner ℝ e (c x) = 0))
    (ψ : Space n → ℝ)
    (hψ : HolderBound α (cylinder univ 0 1) (fun p => ψ p.1) P)
    (hPlateau : ∀ x, outerPatchBump r hr z x*ψ x = ψ x) :
    ∃ δ C E : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < E ∧
      PhysicalDirichletPatchFactory O α lam upper M ψ δ C E := by
  obtain ⟨δ,C,hδ,hδ1,hC,hFactory⟩ := curvedBoundaryPatch_linear_factory_uniform_short
    hα hα1 hM hP z hr hr1 e he c hq hSource hImage hTarget hc hci hFaces ψ hψ hPlateau
  obtain ⟨CG,hCG,hComm⟩ := outerPatchBump_chart_commutator_holder_budget hα hα1 hr hr1
    z c.open_source hSource hc
  let E : ℝ := 1+CG*M*C
  have hE : 0 < E := by dsimp only [E]; positivity
  refine ⟨δ,C,E,hδ,hδ1,hC,hE,?_⟩
  intro ρ T a b hρ hρ1 hT hTδ hTρ hEll ha hb
  obtain ⟨V,hVAdd,hVSmul,hV⟩ := hFactory ρ T a b hρ hρ1 hT hTδ hTρ hEll ha hb
  let W := fun f => curvedBoundaryPatch c (outerPatchBump r hr z) (V f)
  let H := fun f => spatialCutoffCommutator a b (outerPatchBump r hr z) (chartSpaceTimePullback c (V f))
  refine ⟨W,H,?_,?_,?_⟩
  · intro f g p hp
    change outerPatchBump r hr z p.1*V (f+g) (c p.1,p.2) = _
    rw [hVAdd f g (c p.1,p.2) ⟨mem_univ _,hp.2⟩]
    dsimp only [W,curvedBoundaryPatch]
    ring
  · intro d f p hp
    change outerPatchBump r hr z p.1*V (d • f) (c p.1,p.2) = _
    rw [hVSmul d f (c p.1,p.2) ⟨mem_univ _,hp.2⟩]
    dsimp only [W,curvedBoundaryPatch]
    ring
  · intro f
    obtain ⟨hv,hvLow,hv0,hw,hwLow,hw0,hwB,hwEq⟩ := hV f
    refine ⟨⟨hw,hwLow,hw0,hwB,hwEq⟩,?_,?_⟩
    · have h := hComm O T M (C*‖f‖) (C*‖f‖*ρ^(1-α)) a b (V f) ha hb hv hvLow
      apply holderBound_mono_const h
      have hCost : CG*M*(C*‖f‖*ρ^(1-α)) = (CG*M*C)*(‖f‖*ρ^(1-α)) := by ring
      rw [hCost]
      change (CG*M*C)*(‖f‖*ρ^(1-α)) ≤ (1+CG*M*C)*‖f‖*ρ^(1-α)
      nlinarith only [mul_nonneg (norm_nonneg f) (Real.rpow_nonneg hρ.le (1-α))]
    · intro x hx
      exact chart_spatialCutoffCommutator_initial_zero a b (outerPatchBump r hr z) c hv0 x

theorem boundaryChartBuffer_physical_patch_factory {n : ℕ} {O : Set (Space n)}
    {α M lam upper P : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) (hP : 0 ≤ P)
    {z : Space n} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hBuffer : boundaryChartBuffer O z r)
    (ψ : Space n → ℝ)
    (hψ : HolderBound α (cylinder univ 0 1) (fun p => ψ p.1) P)
    (hPlateau : ∀ x, outerPatchBump r hr z x*ψ x = ψ x) :
    ∃ δ C E : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < E ∧
      PhysicalDirichletPatchFactory O α lam upper M ψ δ C E := by
  obtain ⟨e,c,q,he,hq,hSource,hImage,hTarget,hc,hci,hFaces⟩ := hBuffer
  exact boundary_physical_patch_factory hα hα1 hM hP z hr hr1 e he c hq hSource hImage
    hTarget hc hci (fun x hx => (hFaces x hx).2) ψ hψ hPlateau

end Yau.LeafProofs.L16Aux
