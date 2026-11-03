import Yau.Proofs.F05ViscosityComparison
import Yau.Proofs.F05ReactionBound
import Yau.Proofs.F05FlowScalarSmooth

/-! The original F05 upper-semicontinuous, locally bounded viscosity
subsolution lies below any actual nonnegative smooth compact-domain solution
whose original boundary values dominate rho. -/

open Set
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_viscosity_comparison {O : Set (Pt X)} {A : AtlasData X.manifold}
    (hA : GenuineAtlas O A) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {T S : ℝ} (hS : 0 < S) (hST : S ≤ T)
    (v u : STF X)
    (hVusc : UpperSemicontinuousOn (fun q : Pt X × ℝ => v q.1 q.2) (univ ×ˢ Icc 0 T))
    (hVLocal : ∀ K : Set (Pt X), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ t ∈ Icc 0 T, |v x t| ≤ C)
    (hVRange : ∀ x t, t ∈ Icc 0 T → 0 ≤ v x t ∧ v x t ≤ ρ x t)
    (hVisc : NonlinearViscositySub h T v)
    (hUCont : ContinuousOn (fun q : Pt X × ℝ => u q.1 q.2) (closure O ×ˢ Icc 0 S))
    (hU : ∀ i, C2 (F05Q A i S) (pull A i u))
    (hU0 : ∀ x ∈ closure O, ∀ t ∈ Icc 0 S, 0 ≤ u x t)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 S, ρ x t ≤ u x t)
    (hSmooth : ∀ x ∈ O, ∀ t ∈ Ioo 0 S, SmoothNear u x t)
    (hEquation : ∀ x ∈ O, ∀ t ∈ Ioo 0 S, derivWithin (u x) (Icc 0 S) t =
      Real.exp (-u x t)*laplacian (h t) (fun y => u y t) x+
        (1-Real.exp (-u x t))*scalarCurvature (h t) x) :
    ∀ x ∈ closure O, ∀ t ∈ Ico 0 S, v x t ≤ u x t := by
  have hTime : Icc (0 : ℝ) S ⊆ Icc 0 T := fun t ht => ⟨ht.1,ht.2.trans hST⟩
  have hh : MetricFamilySmooth h (Icc 0 S) := fun x a b =>
    (hloc.1.2.1 x a b).mono (fun q hq => ⟨hq.1,hq.2.1⟩)
  obtain ⟨A₀,hA₀,hBound⟩ := F05_compact_reaction_bound hA h hh
    (F05_flow_scalar_smooth o h U P ρ hloc hS) u hU
  obtain ⟨B,hB⟩ := hVLocal (closure O) (F05_atlas_closure_compact hA)
  apply F05_viscosity_comparison_bounded hA h hS hST u v hVisc
    (hVusc.mono (fun q hq => ⟨mem_univ _,hTime hq.2⟩)) hUCont
    (fun x _ t ht => (hVRange x t (hTime ht)).1) hU0 B A₀
    (fun x hx t ht => (le_abs_self _).trans (hB x hx t (hTime ht)))
    (fun x hx t ht => hBound x (subset_closure hx) t ⟨ht.1.le,ht.2.le⟩)
  · intro x hx
    rw [bounded_subsolution_initial_zero o h U P ρ hloc T (hS.le.trans hST) v hVRange x]
    exact hU0 x hx 0 ⟨le_rfl,hS.le⟩
  · intro x hx t ht
    exact ((hVRange x t (hTime ht)).2).trans (hBoundary x hx t ht)
  · exact hSmooth
  · intro x hx t ht
    change deriv (u x) t = scalarNonlinearRHS _ _ _
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact hEquation x hx t ht

end Yau.Proofs.F05Aux
