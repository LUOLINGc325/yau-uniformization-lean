import Yau.Proofs.F04FlowSourceLp
import Yau.Proofs.F05FlowScalarSmooth

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

/-- The actual fixed-initial-Ricci source is smooth on the original closed
 physical slab, using the certified scalar derivative and actual Laplacian. -/
theorem flow_source_smooth_closed
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T) :
    SmoothSpaceTime (source X h) (Icc 0 T) := by
  have hh : MetricFamilySmooth h (Icc 0 T) := fun c i j =>
    (hloc.1.2.1 c i j).mono (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hρ : SmoothSpaceTime ρ (Icc 0 T) := fun c => (hloc.2.2.2.1 c).mono
    (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hLap := metricFamily_laplacian_spaceTime_smooth h hT hh hρ
  have hR := Yau.Proofs.F05Aux.F05_flow_scalar_smooth o h U P ρ hloc hT
  intro c
  apply ((hR c).sub (hLap c)).congr
  intro p hp
  have he := rho_source_equation o h U P ρ hloc T hT (chartInv c p.1) p.2 hp.2
  unfold heatOp at he
  rw [rho_derivWithin_Icc o h U P ρ hloc T hT (chartInv c p.1) p.2 hp.2] at he
  exact he.symm

/-- Smooth spatial cutoffs give genuine smooth physical forcing profiles. -/
theorem flow_cutoff_source_smooth_closed
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (q : Pt X → ℝ) (hq : SmoothFn q) :
    SmoothSpaceTime (fun x t => q x * source X h x t) (Icc 0 T) := by
  have hF := flow_source_smooth_closed X o h U P ρ hloc hT
  intro c
  exact ((hq c).comp contDiffOn_fst (fun _ hp => hp.1)).mul (hF c)

end Yau.F04Proof
