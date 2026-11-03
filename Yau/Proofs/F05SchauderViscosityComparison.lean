import Yau.Proofs.F05FlowViscosityComparison
import Yau.Proofs.F05PositiveTimeBootstrap
import Yau.Proofs.F05SmoothNearTransport

/-! The supplied finite Schauder solution satisfies the original viscosity
comparison on the same localized flow. Positive-time SmoothNear is proved
from its original equation and smooth datum, rather than assumed. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_schauder_viscosity_comparison (hn : 0 < n)
    {O : Set (Pt X)} {A : AtlasData X.manifold} (hA : GenuineAtlas O A)
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T S β K : ℝ} (hS : 0 < S) (hST : S ≤ T) (hβ : 0 < β) (hβ1 : β < 1)
    (v u p : STF X)
    (hVusc : UpperSemicontinuousOn (fun z : Pt X × ℝ => v z.1 z.2) (univ ×ˢ Icc 0 T))
    (hVLocal : ∀ K : Set (Pt X), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ t ∈ Icc 0 T, |v x t| ≤ C)
    (hVRange : ∀ x t, t ∈ Icc 0 T → 0 ≤ v x t ∧ v x t ≤ ρ x t)
    (hVisc : NonlinearViscositySub h T v)
    (hp : SmoothSpaceTime p (Icc 0 S))
    (hUCont : ContinuousOn (fun z : Pt X × ℝ => u z.1 z.2) (closure O ×ˢ Icc 0 S))
    (hU : ∀ i, SchauderBound β (F05Q A i S) (pull A i u) K)
    (hU0 : ∀ x ∈ closure O, ∀ t ∈ Icc 0 S, 0 ≤ u x t)
    (hInitial : ∀ x ∈ closure O, u x 0 = p x 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 S, u x t = p x t)
    (hBoundaryMajorant : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 S, ρ x t ≤ u x t)
    (hEquation : ∀ x ∈ closure O, ∀ t ∈ Icc 0 S,
      derivWithin (u x) (Icc 0 S) t = Real.exp (-u x t)*laplacian (h t) (fun y => u y t) x+
        (1-Real.exp (-u x t))*scalarCurvature (h t) x) :
    ∀ x ∈ closure O, ∀ t ∈ Ico 0 S, v x t ≤ u x t := by
  have hh : MetricFamilySmooth h (Icc 0 S) := fun x j k =>
    (hloc.1.2.1 x j k).mono (fun z hz => ⟨hz.1,hz.2.1⟩)
  have hClosed := F05_positive_time_boundary_bootstrap hn hA h
    (fun x t => scalarCurvature (h t) x) p u hS hβ hβ1 hh
    (F05_flow_scalar_smooth o h U P ρ hloc hS) hp hUCont hU hInitial hBoundary hEquation
  have hOpen := F05_positive_closed_to_open_charts hA u hClosed
  apply F05_flow_viscosity_comparison hA o h U P ρ hloc hS hST v u hVusc hVLocal hVRange hVisc
    hUCont (fun i => (hU i).1) hU0 hBoundaryMajorant (F05_open_charts_smoothNear hA u hOpen)
  intro x hx t ht
  exact hEquation x (subset_closure hx) t ⟨ht.1.le,ht.2.le⟩

end Yau.Proofs.F05Aux
