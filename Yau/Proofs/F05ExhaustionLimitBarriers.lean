import Yau.Proofs.F05ExhaustionValueCompactness
import Yau.Proofs.F05FlowBarriers

/-! The actual approximants' inequalities pass to their genuine single
manifold limit. The corner error tends to zero; the given viscosity
subsolution remains dominated at every original positive-time point. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Blueprint Yau.HeatConcreteBindings
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_exhaustion_limit_barriers (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T : ℝ} (hT : 0 < T) (v : STF X)
    (hVRange : ∀ x t, t ∈ Icc 0 T → 0 ≤ v x t ∧ v x t ≤ ρ x t)
    (w : ℕ → STF X)
    (hBounds : ∀ j, ∀ x ∈ closure (O j), ∀ t ∈ Icc 0 T,
      0 ≤ w j x t ∧ w j x t ≤ ρ x t+2*F05ExhaustionError j)
    (hComparison : ∀ j, ∀ x ∈ closure (O j), ∀ t ∈ Ico 0 T, v x t ≤ w j x t)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (W : STF X) (hW0 : ∀ x, W x 0 = 0)
    (hPoint : ∀ x t, t ∈ Ioc 0 T → Tendsto (fun k => w (φ k) x t) atTop (𝓝 (W x t))) :
    ∀ x t, t ∈ Ico 0 T → 0 ≤ W x t ∧ v x t ≤ W x t ∧ W x t ≤ ρ x t := by
  intro x t ht
  by_cases ht0 : t = 0
  · rw [ht0,hW0 x,Yau.F04Proof.rho_initial o h U P ρ hloc x]
    have hV := (hVRange x 0 ⟨le_rfl,hT.le⟩).2
    rw [Yau.F04Proof.rho_initial o h U P ρ hloc x] at hV
    exact ⟨le_rfl,hV,le_rfl⟩
  have htPos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hxAll : x ∈ ⋃ j, O j := by rw [hO.2.2]; exact mem_univ x
  obtain ⟨j,hxj⟩ := mem_iUnion.mp hxAll
  have hDom : ∀ᶠ k in atTop, x ∈ closure (O (φ k)) :=
    (hφ.tendsto_atTop.eventually (eventually_ge_atTop j)).mono (fun k hk =>
      subset_closure (F05_smooth_exhaustion_monotone hO hk hxj))
  have hActual := hPoint x t ⟨htPos,ht.2.le⟩
  have hZero : 0 ≤ W x t := ge_of_tendsto hActual
    (hDom.mono (fun k hk => (hBounds (φ k) x hk t ⟨ht.1,ht.2.le⟩).1))
  have hV : v x t ≤ W x t := ge_of_tendsto hActual
    (hDom.mono (fun k hk => hComparison (φ k) x hk t ht))
  have hε := F05_exhaustion_error_tendsto.comp hφ.tendsto_atTop
  have hUpper : Tendsto (fun k => ρ x t+2*F05ExhaustionError (φ k)) atTop (𝓝 (ρ x t)) := by
    simpa only [mul_zero,add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hε) :
        Tendsto (fun k => ρ x t+2*F05ExhaustionError (φ k)) atTop (𝓝 (ρ x t+2*0)))
  exact ⟨hZero,hV,le_of_tendsto_of_tendsto hActual hUpper
    (hDom.mono (fun k hk => (hBounds (φ k) x hk t ⟨ht.1,ht.2.le⟩).2))⟩

end Yau.Proofs.F05Aux
